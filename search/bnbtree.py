"""Certifying branch-and-bound for V_n >= lam, production solver version 2 (drop-in for src/bnbcert.py).

Usage (same CLI and file queue as bnbcert.py):
  bnbcert2.py init CERTDIR n lam [--depth D] [--plain] [--opts JSON]   master DFS to depth D, delegate the rest as jobs
  bnbcert2.py work CERTDIR [--workers W] [--max-nodes N]                process queued jobs (file queue, preemption safe)
  bnbcert2.py status CERTDIR
  bnbcert2.py recover CERTDIR

Output format: CERT_FORMAT.md (format 2), checked by verify2.py.  With --plain (no square cuts, no compression)
the output is the old format and src/verify.py checks it unchanged.

Solver (all solver-side; the certificate semantics are those of the verifier):
  * lazy rows: window and McCormick rows enter the HiGHS LP only when violated (cutting-plane loop per node);
    rows without dual weight for max_age nodes are purged.  A leaf dual is zero on rows not in the LP, which is
    an admissible dual of the full LP;
  * parent-basis restore for the second child; HiGHS objective_bound = lam + 1e-6 (dual simplex stops early on
    leaves); Devex pricing;
  * branching: block with the largest sum of McCormick gaps, each pair's gap weighted by 1 + 20 * (its McCormick
    duals / max), split at the LP value clipped to the middle 50%, rounded to a multiple of 2^-30;
  * square cuts "m3": (v0 + v_D m_D + v_E m_E)^2 >= 0 from the most negative eigenvector of
    [1 m_D m_E; m_D Z_DD Z_DE; m_E Z_DE Z_EE], integer v (20 bits); defined per job by K records;
  * leaves are written as D records (compressed: integer duals on the non-P/G/ZA rows, the verifier completes the
    rest) or E records (explicit integer dual), each re-checked in floating point exactly as written (completion
    included) with margin 1e-8 before writing; optional exact self-check of a sample with verify2.py.
Robustness (as bnbcert.py): LP error -> cold retry -> midpoint split of the widest block; infeasible without a
usable ray -> midpoint split; all split points are multiples of 2^-30 so float propagation is exact.
"""
import sys, os, json, gzip, time, uuid, glob, signal, random
from fractions import Fraction as Fr
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import spsolve_triangular
import highspy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify import Spec, TMAX

SPLITBITS = 30
SCALE = float(2 ** SPLITBITS)
LB_MARGIN = 1e-9          # float pre-check margin for plain L records (as bnbcert.py)
REC_MARGIN = 1e-8         # float re-check margin for D / E records as written
INF = highspy.kHighsInf
_S = highspy.HighsBasisStatus
ENUM = [_S.kLower, _S.kBasic, _S.kUpper, _S.kZero, _S.kNonbasic]
BASIC = 1
MS = highspy.HighsModelStatus

DEFAULT_OPTS = dict(
    lazy_win=True, lazy_mc=True, restore=True, objbound=True,
    add_cap=400, max_rounds=30, viol_tol=1e-7, purge_every=20, max_age=40,
    hopts={"simplex_dual_edge_weight_strategy": 1},
    score_dual=20.0, split_clip=0.25,
    psd="m3", psd_rounds=1, psd_k=1, psd_tol=1e-6, psd_bits=20, cut_max_age=30, cutcap=200000,
    compress=True, D_F=[20, 24, 28, 32, 40, 48], E_F=[24, 32, 40, 48, 56, 64], selfcheck=0.0,
    tree_only=False, tree_margin=1e-7)
PLAIN_OPTS = dict(psd="", compress=False)


def frac_str(x):
    return str(Fr(x))


class Model:
    def __init__(self, n, lam, opts=None):
        self.opts = dict(DEFAULT_OPTS); self.opts.update(opts or {})
        o = self.opts
        self.n = n; self.lam = lam
        spec = self.spec = Spec(n)
        tree = spec.tree
        nB = spec.nB
        # ---- columns (identical to bnbcert.Model)
        colkeys = [("m", spec.leaf_of_bin[i]) for i in range(n)]
        colkeys += [("m", b) for b in range(nB) if not spec.leaf[b]]
        colkeys += [("Z", i, j) for i in range(n) for j in range(i, n)]
        nonroot = [b for b in range(nB) if b != 0]
        self.pairs = [(d, e) for k, d in enumerate(nonroot) for e in nonroot[k:]]
        colkeys += [("ZA", d, e) for (d, e) in self.pairs if not (spec.leaf[d] and spec.leaf[e])]
        colkeys += [("P", c) for c in range(2 * n - 1)]
        colkeys += [("G", c) for c in range(2 * n - 1)]
        colkeys += [("t",)]
        self.colkeys = colkeys
        self.cix = {k: i for i, k in enumerate(colkeys)}
        self.ncol = len(colkeys)
        # ---- rows: the canonical order (identical to bnbcert.Model)
        rowkeys = [("win", c1, c2) for c1 in range(2 * n - 1) for c2 in range(c1, 2 * n - 1)]
        self.nwin = len(rowkeys)
        rowkeys += [("P", c) for c in range(2 * n - 1)]
        rowkeys += [("G", c) for c in range(2 * n - 1)]
        rowkeys += [("tree", b) for b in range(nB) if not spec.leaf[b]]
        for (d, e) in self.pairs:
            if spec.leaf[d] and spec.leaf[e]:
                continue
            if spec.leaf[d]:
                s = e
            elif spec.leaf[e]:
                s = d
            else:
                s = d if (tree[d][1] - tree[d][0]) >= (tree[e][1] - tree[e][0]) else e
            rowkeys.append(("ZA", d, e, s))
        rowkeys += [("rlt", i) for i in range(n)]
        rowkeys += [("sym",)]
        self.nfixed = len(rowkeys)
        rowkeys += [("mc", d, e, q) for (d, e) in self.pairs for q in range(4)]
        self.rowkeys = rowkeys
        self.nrow = len(rowkeys)
        L0, U0 = spec.root_region()
        rows_lo = np.empty(self.nrow); rows_up = np.empty(self.nrow)
        I, J, V = [], [], []
        for r, key in enumerate(rowkeys):
            lo, up, ent = spec.row(key, L0, U0)
            rows_lo[r] = -INF if lo is None else float(lo)
            rows_up[r] = INF if up is None else float(up)
            for ck, a in ent.items():
                I.append(r); J.append(self.cix[ck]); V.append(float(a))
        A = sp.csr_matrix((V, (I, J)), shape=(self.nrow, self.ncol))
        A.sort_indices()
        self.A = A
        self.AfixT = A[: self.nfixed].T.tocsr()
        # ---- McCormick structure
        self.npairs = len(self.pairs)
        self.mc_z = np.array([self.cix[spec.canon_pair(d, e)] for (d, e) in self.pairs])
        self.mc_md = np.array([self.cix[("m", d)] for (d, e) in self.pairs])
        self.mc_me = np.array([self.cix[("m", e)] for (d, e) in self.pairs])
        self.mc_d = np.array([d for (d, e) in self.pairs]); self.mc_e = np.array([e for (d, e) in self.pairs])
        self.mc_diag = self.mc_d == self.mc_e
        self.blockcol = np.array([self.cix[("m", b)] for b in range(nB)])
        self.diagcol = np.array([self.cix[spec.canon_pair(b, b)] for b in range(1, nB)])
        self.cost = np.zeros(self.ncol); self.cost[self.cix[("t",)]] = 1.0
        self.tcol = self.cix[("t",)]
        lb = np.zeros(self.ncol); ub = np.ones(self.ncol); ub[self.tcol] = float(TMAX)
        lb[self.blockcol] = [float(x) for x in L0]; ub[self.blockcol] = [float(x) for x in U0]
        self.col_lb, self.col_ub = lb, ub
        self.L = np.array([float(x) for x in L0]); self.U = np.array([float(x) for x in U0])
        self.root_region_float = (self.L.copy(), self.U.copy())
        self.pair_ids_of_block = [[] for _ in range(nB)]
        for k, (d, e) in enumerate(self.pairs):
            self.pair_ids_of_block[d].append(k)
            if e != d:
                self.pair_ids_of_block[e].append(k)
        wk = rowkeys[: self.nwin]
        self.w_c1 = np.array([k[1] for k in wk]); self.w_c2 = np.array([k[2] for k in wk])
        self.w_w = np.array([2.0 * n / (k[2] - k[1] + 2) for k in wk])
        self.gcol = np.array([self.cix[("G", c)] for c in range(2 * n - 1)])
        # ---- row universe: canonical rows, then dynamic cut rows (ids >= nrow)
        self.cap = cap = self.nrow + int(o["cutcap"])
        self.row_lo = np.concatenate([rows_lo, np.zeros(cap - self.nrow)])
        self.row_up = np.concatenate([rows_up, np.full(cap - self.nrow, INF)])
        kind = np.zeros(cap, dtype=np.int8)       # 0 always in the LP, 1 window, 2 mc, 3 cut
        kind[: self.nwin] = 1; kind[self.nfixed:self.nrow] = 2; kind[self.nrow:] = 3
        self.kind = kind
        lazy = np.zeros(cap, bool); lazy[self.nrow:] = True
        if o["lazy_win"]:
            lazy[kind == 1] = True
        if o["lazy_mc"]:
            lazy[kind == 2] = True
        self.lazy = lazy
        never = np.zeros(cap, bool)               # duplicate diagonal McCormick rows (q=3 equals q=2 when d == e)
        for k in np.nonzero(self.mc_diag)[0]:
            never[self.nfixed + 4 * k + 3] = True
        self.never = never
        self.ncut = 0; self.cut_cols = {}; self.cut_vals = {}; self.cut_key = {}; self.cut_seen = {}; self.cut_nnz = 0
        # ---- auxiliary rows (P, G, ZA) and the float completion for D records (mirror of verify2.Completion)
        self._build_completion()
        # ---- HiGHS
        h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("threads", 1)
        h.setOptionValue("simplex_iteration_limit", 30000)   # as src/bnbopt.py: a stalled solve returns instead of running forever
        h.setOptionValue("presolve", "off")
        h.setOptionValue("solver", "simplex")
        h.setOptionValue("simplex_strategy", 1)
        for k, v in o["hopts"].items():
            h.setOptionValue(k, v)
        self.h = h
        lp = highspy.HighsLp()
        lp.num_col_ = self.ncol; lp.num_row_ = 0
        lp.col_cost_ = self.cost; lp.col_lower_ = lb.copy(); lp.col_upper_ = ub.copy()
        h.passModel(lp)
        self.pos = np.full(cap, -1, dtype=np.int64)
        self.lprows = np.zeros(0, dtype=np.int64)
        self.age = np.zeros(cap, dtype=np.int32)
        self.stats = {"lp": 0, "its": 0, "rounds": 0, "cuts": 0, "cut_resets": 0}
        self.add_rows(np.nonzero(~lazy & ~never)[0])
        self.objbound_on = False
        self.set_objbound(o["objbound"])
        self.last_rd = None

    # ---------------------------------------------------------------- completion structure
    def _build_completion(self):
        n, spec = self.n, self.spec
        rix = {k: i for i, k in enumerate(self.rowkeys)}
        self.grow = np.array([rix[("G", c)] for c in range(2 * n - 1)])
        self.prow = np.array([rix[("P", c)] for c in range(2 * n - 1)])
        za = [i for i, k in enumerate(self.rowkeys) if k[0] == "ZA"]
        self.za_rows = np.array(za)
        aux = np.zeros(self.nrow, bool); aux[self.grow] = True; aux[self.prow] = True; aux[za] = True
        self.aux = aux
        own = {r: self.cix[spec.canon_pair(self.rowkeys[r][1], self.rowkeys[r][2])] for r in za}
        owncol_row = {c: r for r, c in own.items()}
        tree = spec.tree

        def size(r):
            d, e = self.rowkeys[r][1], self.rowkeys[r][2]
            return (tree[d][1] - tree[d][0]) + (tree[e][1] - tree[e][0])
        order = sorted(za, key=lambda r: (-size(r), r))
        posr = {r: i for i, r in enumerate(order)}
        I, J, V = [], [], []
        A = self.A
        for r in za:
            a, b = A.indptr[r], A.indptr[r + 1]
            for c, v in zip(A.indices[a:b], A.data[a:b]):
                if c != own[r] and c in owncol_row:
                    child = owncol_row[c]
                    if posr[r] >= posr[child]:
                        raise RuntimeError("ZA completion order violated")
                    I.append(posr[child]); J.append(posr[r]); V.append(v)
        nza = len(order)
        self.comp_T = (sp.identity(nza, format="csr") + sp.csr_matrix((V, (I, J)), shape=(nza, nza))).tocsr()
        self.comp_order = np.array(order, dtype=np.int64)
        self.comp_own = np.array([own[r] for r in order], dtype=np.int64)
        wi, wj, wv = [], [], []
        for k in range(self.nwin):
            c1, c2, w = self.w_c1[k], self.w_c2[k], self.w_w[k]
            wi.append(k); wj.append(c2); wv.append(w)
            if c1 > 0:
                wi.append(k); wj.append(c1 - 1); wv.append(-w)
        self.comp_Wg = sp.csr_matrix((wv, (wi, wj)), shape=(self.nwin, 2 * n - 1)).T.tocsr()

    def complete(self, y, L, U):
        """Float mirror of verify2's completion: y (universe incl. cuts) with P/G/ZA entries overwritten so that
        the reduced costs of all G, P, ZA columns vanish.  Contributions come from all other rows with admissible
        sign (windows, mc, tree, rlt, sym, cuts)."""
        n = self.n
        y = y.copy()
        y[self.grow] = 0.0; y[self.prow] = 0.0; y[self.za_rows] = 0.0
        # drop inadmissible signs first (as the verifier does)
        nr = self.nrow + self.ncut
        lo = self.row_lo[:nr]; up = self.row_up[:nr]
        yy = y[:nr]
        yy[(yy > 0) & ~np.isfinite(lo)] = 0.0
        yy[(yy < 0) & ~np.isfinite(up)] = 0.0
        # G columns appear only in G rows and windows; P columns only in P and G rows
        wcontrib = self.comp_Wg @ yy[: self.nwin]
        yg = -np.cumsum(wcontrib[::-1])[::-1]
        y[self.grow] = yg
        y[self.prow] = yg
        # ZA columns: contributions of mc rows and cut rows (other row kinds do not contain ZA columns)
        contrib = np.zeros(self.ncol)
        cz, cmd, cme, rhs = self.mc_coeffs(np.asarray(L, float), np.asarray(U, float))
        ym = yy[self.nfixed:self.nrow].reshape(-1, 4).T
        np.add.at(contrib, self.mc_z, (cz * ym).sum(0))
        for cid in np.nonzero(yy[self.nrow:])[0] + self.nrow:
            np.add.at(contrib, self.cut_cols[cid], yy[cid] * self.cut_vals[cid])
        y[self.comp_order] = spsolve_triangular(self.comp_T, -contrib[self.comp_own], lower=True)
        return y

    # ---------------------------------------------------------------- LP management
    def set_objbound(self, on):
        if on != self.objbound_on:
            self.h.setOptionValue("objective_bound", float(self.lam) + 1e-6 if on else INF)
            self.objbound_on = on

    def mc_coeffs(self, L, U, ks=None):
        d, e = (self.mc_d, self.mc_e) if ks is None else (self.mc_d[ks], self.mc_e[ks])
        diag = self.mc_diag if ks is None else self.mc_diag[ks]
        Ld, Ud, Le, Ue = L[d], U[d], L[e], U[e]
        cz = np.array([-1.0, -1.0, 1.0, 1.0])[:, None] * np.ones(len(d))
        cmd = np.stack([Le, Ue, -Ue, -Le]); cme = np.stack([Ld, Ud, -Ld, -Ud])
        rhs = np.stack([Ld * Le, Ud * Ue, -Ld * Ue, -Ud * Le])
        cmd_d = np.stack([2 * Ld, 2 * Ud, -(Ld + Ud), -(Ld + Ud)])
        rhs_d = np.stack([Ld * Ld, Ud * Ud, -Ld * Ud, -Ld * Ud])
        cmd = np.where(diag[None, :], cmd_d, cmd)
        cme = np.where(diag[None, :], 0.0, cme)
        rhs = np.where(diag[None, :], rhs_d, rhs)
        return cz, cmd, cme, rhs

    def add_rows(self, rows):
        rows = np.asarray(rows, dtype=np.int64)
        rows = rows[self.pos[rows] < 0]
        if len(rows) == 0:
            return
        lo = np.empty(len(rows)); up = np.empty(len(rows)); starts = [0]; idx = []; val = []
        mcmask = self.kind[rows] == 2
        if mcmask.any():
            ks = (rows[mcmask] - self.nfixed) // 4; qs = (rows[mcmask] - self.nfixed) % 4
            cz, cmd, cme, rhs = self.mc_coeffs(self.L, self.U, ks)
            ar = np.arange(len(ks))
            mc_info = iter(zip(ks, cz[qs, ar], cmd[qs, ar], cme[qs, ar], rhs[qs, ar]))
        for t, r in enumerate(rows):
            if self.kind[r] == 3:
                idx += self.cut_cols[r].tolist(); val += self.cut_vals[r].tolist()
                lo[t] = self.row_lo[r]; up[t] = INF
            elif self.kind[r] == 2:
                k, a_z, a_d, a_e, rh = next(mc_info)
                if self.mc_diag[k]:
                    idx += [self.mc_z[k], self.mc_md[k]]; val += [a_z, a_d]
                else:
                    idx += [self.mc_z[k], self.mc_md[k], self.mc_me[k]]; val += [a_z, a_d, a_e]
                lo[t] = -INF; up[t] = rh
                self.row_up[r] = rh
            else:
                a, b = self.A.indptr[r], self.A.indptr[r + 1]
                idx += self.A.indices[a:b].tolist(); val += self.A.data[a:b].tolist()
                lo[t] = self.row_lo[r]; up[t] = self.row_up[r]
            starts.append(len(idx))
        nr0 = len(self.lprows)
        self.h.addRows(len(rows), lo, up, len(idx), np.array(starts[:-1], dtype=np.int32),
                       np.array(idx, dtype=np.int32), np.array(val, dtype=float))
        self.pos[rows] = nr0 + np.arange(len(rows))
        self.lprows = np.concatenate([self.lprows, rows])
        self.age[rows] = 0

    def delete_rows(self, rows):
        rows = np.asarray(rows, dtype=np.int64)
        rows = rows[self.pos[rows] >= 0]
        if len(rows) == 0:
            return
        hp = np.sort(self.pos[rows]).astype(np.int32)
        self.h.deleteRows(len(hp), hp)
        keep = np.ones(len(self.lprows), bool); keep[hp] = False
        self.pos[rows] = -1
        self.lprows = self.lprows[keep]
        self.pos[self.lprows] = np.arange(len(self.lprows))

    def set_region(self, L, U):
        L = np.asarray(L, float); U = np.asarray(U, float)
        changed = np.nonzero((L != self.L) | (U != self.U))[0]
        if len(changed) == 0:
            return
        self.L, self.U = L.copy(), U.copy()
        ks = np.array(sorted(set(k for b in changed for k in self.pair_ids_of_block[b])), dtype=np.int64)
        if len(ks):
            r0 = self.nfixed + 4 * ks
            present = (self.pos[r0[:, None] + np.arange(4)[None, :]] >= 0)
            sel = present.any(1)
            ks = ks[sel]; present = present[sel]
        if len(ks):
            cz, cmd, cme, rhs = self.mc_coeffs(L, U, ks)
            h = self.h
            ridx = []; rup = []
            for t, k in enumerate(ks):
                r0 = self.nfixed + 4 * int(k)
                md, me = int(self.mc_md[k]), int(self.mc_me[k])
                for q in range(4):
                    if not present[t, q]:
                        continue
                    hr = int(self.pos[r0 + q])
                    h.changeCoeff(hr, md, float(cmd[q, t]))
                    if not self.mc_diag[k]:
                        h.changeCoeff(hr, me, float(cme[q, t]))
                    ridx.append(hr); rup.append(float(rhs[q, t]))
                    self.row_up[r0 + q] = rhs[q, t]
            if ridx:
                ridx = np.array(ridx, dtype=np.int32); rup = np.array(rup)
                h.changeRowsBounds(len(ridx), ridx, np.full(len(ridx), -INF), rup)
        cols = self.blockcol[changed].astype(np.int32)
        self.col_lb[cols] = L[changed]; self.col_ub[cols] = U[changed]
        self.h.changeColsBounds(len(cols), cols, L[changed].copy(), U[changed].copy())

    def get_basis(self):
        b = self.h.getBasis()
        if not b.valid:
            return None
        return (self.lprows.copy(), np.array([int(s) for s in b.row_status], dtype=np.int8),
                np.array([int(s) for s in b.col_status], dtype=np.int8))

    def set_basis(self, stored):
        rows_s, rst, cst = stored
        absent = self.pos[rows_s] < 0
        readd = rows_s[absent & (rst != BASIC)]
        if len(readd):
            self.add_rows(readd)
        status = np.full(self.cap, BASIC, dtype=np.int8)
        status[rows_s] = rst
        nb = highspy.HighsBasis()
        nb.col_status = [ENUM[i] for i in cst]
        nb.row_status = [ENUM[i] for i in status[self.lprows]]
        nb.valid = True
        self.h.setBasis(nb)

    def run(self, cold_retry=True):
        h = self.h
        h.run()
        st = h.getModelStatus()
        self.stats["lp"] += 1; self.stats["its"] += h.getInfo().simplex_iteration_count
        if cold_retry and st not in (MS.kOptimal, MS.kInfeasible, MS.kObjectiveBound):
            # as src/bnbopt.py: cold retry with dual steepest-edge pricing (Devex can stall on degenerate LPs)
            h.clearSolver()
            h.setOptionValue("simplex_dual_edge_weight_strategy", 2)
            h.run()
            st = h.getModelStatus()
            h.setOptionValue("simplex_dual_edge_weight_strategy", int(self.opts["hopts"].get("simplex_dual_edge_weight_strategy", 1)))
            self.stats["lp"] += 1; self.stats["its"] += h.getInfo().simplex_iteration_count
        return st

    def full_dual(self, row_dual):
        y = np.zeros(self.cap)
        y[self.lprows] = row_dual
        return y

    def ns_bound(self, y, L, U, objective=True):
        """Float Neumaier-Shcherbina bound of y for region (L, U) (rows rebuilt from L, U), mirror of the verifier."""
        L = np.asarray(L, float); U = np.asarray(U, float)
        cz, cmd, cme, rhs = self.mc_coeffs(L, U)
        nr = self.nrow + self.ncut
        lo = self.row_lo[:nr].copy(); up = self.row_up[:nr].copy()
        up[self.nfixed:self.nrow] = rhs.T.reshape(-1)
        y = y[:nr].copy()
        y[(y > 0) & ~np.isfinite(lo)] = 0.0
        y[(y < 0) & ~np.isfinite(up)] = 0.0
        rowpart = float(np.sum(np.where(y > 0, y * np.where(np.isfinite(lo), lo, 0.0), y * np.where(np.isfinite(up), up, 0.0))))
        r = (self.cost if objective else np.zeros(self.ncol)) - self.AfixT @ y[: self.nfixed]
        ym = y[self.nfixed:self.nrow].reshape(-1, 4).T
        for cid in np.nonzero(y[self.nrow:])[0] + self.nrow:
            np.subtract.at(r, self.cut_cols[cid], y[cid] * self.cut_vals[cid])
        np.subtract.at(r, self.mc_z, (cz * ym).sum(0))
        np.subtract.at(r, self.mc_md, (cmd * ym).sum(0))
        np.subtract.at(r, self.mc_me, (cme * ym).sum(0))
        clb = self.col_lb.copy(); cub = self.col_ub.copy()
        clb[self.blockcol] = L; cub[self.blockcol] = U
        colpart = float(np.sum(np.minimum(r * clb, r * cub)))
        return rowpart + colpart

    def separate(self, x):
        tol = self.opts["viol_tol"]
        cand = []; viol = []
        if self.opts["lazy_win"]:
            Gm = np.concatenate([[0.0], x[self.gcol]])
            v = self.w_w * (Gm[self.w_c2 + 1] - Gm[self.w_c1]) - x[self.tcol]
            ids = np.nonzero(v > tol)[0]
            ids = ids[self.pos[ids] < 0]
            cand.append(ids); viol.append(v[ids])
        if self.opts["lazy_mc"]:
            cz, cmd, cme, rhs = self.mc_coeffs(self.L, self.U)
            act = cz * x[self.mc_z] + cmd * x[self.mc_md] + cme * x[self.mc_me] - rhs
            act[3, self.mc_diag] = -1.0
            q, k = np.nonzero(act > tol)
            ids = self.nfixed + 4 * k + q
            m = self.pos[ids] < 0
            cand.append(ids[m]); viol.append(act[q, k][m])
        if not cand:
            return np.zeros(0, dtype=np.int64)
        ids = np.concatenate(cand); v = np.concatenate(viol)
        if len(ids) > self.opts["add_cap"]:
            ids = ids[np.argsort(-v)[: self.opts["add_cap"]]]
        return ids

    # ---------------------------------------------------------------- square cuts (m3)
    def reset_cuts(self):
        lr = self.lprows
        cuts = lr[self.kind[lr] == 3]
        if len(cuts):
            self.delete_rows(cuts)
        self.pos[self.nrow:self.nrow + self.ncut] = -1
        self.age[self.nrow:self.nrow + self.ncut] = 0
        self.ncut = 0; self.cut_cols = {}; self.cut_vals = {}; self.cut_key = {}; self.cut_seen = {}; self.cut_nnz = 0
        self.stats["cut_resets"] += 1

    def new_cut(self, cols, vals, lo, key):
        sig = (tuple(cols), tuple(np.round(np.array(vals) * 2 ** 30).astype(np.int64).tolist()), lo)
        if sig in self.cut_seen:
            return self.cut_seen[sig]
        if self.ncut >= self.cap - self.nrow:
            return None
        cid = self.nrow + self.ncut; self.ncut += 1
        self.cut_cols[cid] = np.asarray(cols, dtype=np.int64); self.cut_vals[cid] = np.asarray(vals, dtype=float)
        self.cut_key[cid] = key
        self.cut_nnz += len(cols)
        self.row_lo[cid] = lo; self.row_up[cid] = INF
        self.cut_seen[sig] = cid
        return cid

    def separate_m3(self, x):
        o = self.opts; tol = o["psd_tol"]; sc = 2.0 ** o["psd_bits"]
        new = []
        off = ~self.mc_diag
        d = self.mc_d[off]; e = self.mc_e[off]
        md = x[self.blockcol[d]]; me = x[self.blockcol[e]]
        zde = x[self.mc_z[off]]
        zdd = x[self.diagcol[d - 1]]; zee = x[self.diagcol[e - 1]]
        M = np.zeros((len(d), 3, 3)); M[:, 0, 0] = 1
        M[:, 0, 1] = M[:, 1, 0] = md; M[:, 0, 2] = M[:, 2, 0] = me
        M[:, 1, 1] = zdd; M[:, 2, 2] = zee; M[:, 1, 2] = M[:, 2, 1] = zde
        w, V = np.linalg.eigh(M)
        order = np.argsort(w[:, 0])
        zoff = self.mc_z[off]
        for t in order[: o["psd_k"] * 10]:
            if w[t, 0] >= -tol:
                break
            v = V[t, :, 0] / np.abs(V[t, :, 0]).max(); v = np.round(v * sc) / sc
            cols = [int(self.blockcol[d[t]]), int(self.blockcol[e[t]]), int(self.diagcol[d[t] - 1]), int(zoff[t]), int(self.diagcol[e[t] - 1])]
            vals = [2 * v[0] * v[1], 2 * v[0] * v[2], v[1] ** 2, 2 * v[1] * v[2], v[2] ** 2]
            keep = [i for i in range(5) if vals[i] != 0]
            vi = np.round(v * sc).astype(np.int64)
            if vi[1] == 0 and vi[2] == 0:
                continue
            key = ["sq", int(vi[0]), [[int(d[t]), int(vi[1])], [int(e[t]), int(vi[2])]]]
            cid = self.new_cut([cols[i] for i in keep], [vals[i] for i in keep], -v[0] ** 2, key)
            if cid is not None:
                new.append(cid)
        return np.array(new, dtype=np.int64)

    def update_ages(self, row_dual):
        lr = self.lprows
        act = np.abs(row_dual) > 1e-12
        self.age[lr[act]] = 0
        self.age[lr[~act]] += 1

    def purge(self):
        lr = self.lprows
        lim = np.where(self.kind[lr] == 3, self.opts["cut_max_age"], self.opts["max_age"])
        dead = lr[self.lazy[lr] & (self.age[lr] > lim)]
        if len(dead):
            self.delete_rows(dead)

    def dual_ray(self):
        try:
            res = self.h.getDualRay()
        except Exception:
            return None
        if isinstance(res, tuple):
            ok, ray = res[0], res[1]
            if not ok:
                return None
            return np.array(ray)
        return None

    def solve_node(self):
        """Cutting-plane loop.  Returns (status, obj, x, y_full):
        'leaf' (y certifies: float NS bound >= lam + LB_MARGIN), 'farkas' (y = ray), 'branch', 'error'."""
        lam = self.lam
        psd_done = 0
        x = None; obj = None; rd = None
        for rnd in range(self.opts["max_rounds"]):
            st = self.run()
            self.stats["rounds"] += 1
            if st == MS.kInfeasible:
                ray = self.dual_ray()
                return ("farkas", None, None, self.full_dual(ray)) if ray is not None else ("error", None, None, None)
            if st == MS.kObjectiveBound:
                rd = np.array(self.h.getSolution().row_dual)
                y = np.where(np.abs(self.full_dual(rd)) > 1e-14, self.full_dual(rd), 0.0)
                lb = self.ns_bound(y, self.L, self.U)
                if lb >= lam + LB_MARGIN:
                    self.update_ages(rd)
                    return "leaf", lb, None, y
                self.set_objbound(False)
                st = self.run()
                self.set_objbound(self.opts["objbound"])
                if st == MS.kInfeasible:
                    ray = self.dual_ray()
                    return ("farkas", None, None, self.full_dual(ray)) if ray is not None else ("error", None, None, None)
            if st != MS.kOptimal:
                return "error", None, None, None
            obj = self.h.getInfo().objective_function_value
            sol = self.h.getSolution()
            rd = np.array(sol.row_dual)
            x = np.array(sol.col_value)
            if obj >= lam + 1e-7:
                y = np.where(np.abs(self.full_dual(rd)) > 1e-14, self.full_dual(rd), 0.0)
                lb = self.ns_bound(y, self.L, self.U)
                if lb >= lam + LB_MARGIN:
                    self.update_ages(rd)
                    return "leaf", lb, x, y
            new = self.separate(x)
            if len(new) == 0 and self.opts["psd"] == "m3" and psd_done < self.opts["psd_rounds"]:
                new = self.separate_m3(x); psd_done += 1
                new = new[self.pos[new] < 0] if len(new) else new
                self.stats["cuts"] += len(new)
            if len(new) == 0:
                break
            self.add_rows(new)
        self.update_ages(rd)
        self.last_rd = rd
        return "branch", obj, x, None

    # ---------------------------------------------------------------- leaf encoding (format 2)
    def encode_leaf(self, y, L, U):
        """Return (record, lb_float) for a D record, else an E record, re-checked in floats exactly as written;
        None if no encoding passes (the caller then branches instead)."""
        lam = self.lam
        b2 = 2 * self.opts["psd_bits"]                  # cut rows in the LP are the integer-key rows / 2^b2
        cuts = np.nonzero(y[self.nrow:self.nrow + self.ncut])[0] + self.nrow
        rows = np.nonzero(y[: self.nrow])[0]
        given = rows[~self.aux[rows]]
        if self.opts["compress"]:
            for F in self.opts["D_F"]:
                ints = np.round(y[given] * 2.0 ** F); m = ints != 0
                ic = np.round(y[cuts] * 2.0 ** F); mc = ic != 0
                yy = np.zeros(self.cap)
                yy[given[m]] = ints[m] / 2.0 ** F
                yy[cuts[mc]] = ic[mc] / 2.0 ** F
                yr = self.complete(yy, L, U)
                lb = self.ns_bound(yr, L, U)
                if lb >= lam + REC_MARGIN:
                    rec = ["D", lb, int(F), given[m].tolist(), [int(v) for v in ints[m]]]
                    if mc.any():
                        rec += [int(F + b2), [[int(c - self.nrow), int(v)] for c, v in zip(cuts[mc], ic[mc])]]
                    return rec, lb
        for F in self.opts["E_F"]:
            ints = np.round(y[rows] * 2.0 ** F); m = ints != 0
            ic = np.round(y[cuts] * 2.0 ** F); mc = ic != 0
            yy = np.zeros(self.cap)
            yy[rows[m]] = ints[m] / 2.0 ** F
            yy[cuts[mc]] = ic[mc] / 2.0 ** F
            lb = self.ns_bound(yy, L, U)
            if lb >= lam + REC_MARGIN:
                rec = ["E", lb, int(F), rows[m].tolist(), [int(v) for v in ints[m]]]
                if mc.any():
                    rec += [int(F + b2), [[int(c - self.nrow), int(v)] for c, v in zip(cuts[mc], ic[mc])]]
                return rec, lb
        return None

    def encode_farkas(self, ray, L, U):
        """Integer Farkas record ["F", idx, ints] re-checked in floats, or None (ray on cut rows or check fails)."""
        if ray is None or np.any(ray[self.nrow:] != 0):
            return None
        idx = np.nonzero(ray[: self.nrow])[0]
        if len(idx) == 0:
            return None
        sc = 2.0 ** 40 / np.abs(ray[idx]).max()
        ints = np.round(ray[idx] * sc); m = ints != 0
        yy = np.zeros(self.cap); yy[idx[m]] = ints[m]
        val = self.ns_bound(yy, L, U, objective=False)
        if not (val > 1e-6 * float(np.abs(ints).max())):
            return None
        return ["F", idx[m].tolist(), [int(v) for v in ints[m]]]


def propagate_float(spec, L, U):
    """Float mirror of Spec.propagate (exact for dyadic data)."""
    L = list(L); U = list(U); tree = spec.tree
    L[0] = max(L[0], 1.0); U[0] = min(U[0], 1.0)
    for _ in range(64):
        changed = False
        for b, (lo, hi, par, c1, c2) in enumerate(tree):
            if c1 < 0:
                continue
            nl = max(L[b], L[c1] + L[c2]); nu = min(U[b], U[c1] + U[c2])
            l1 = max(L[c1], L[b] - U[c2]); u1 = min(U[c1], U[b] - L[c2])
            l2 = max(L[c2], L[b] - U[c1]); u2 = min(U[c2], U[b] - L[c1])
            new = (nl, nu, l1, u1, l2, u2)
            if new != (L[b], U[b], L[c1], U[c1], L[c2], U[c2]):
                changed = True
                L[b], U[b], L[c1], U[c1], L[c2], U[c2] = new
        if not changed:
            break
    if any(L[b] > U[b] for b in range(spec.nB)):
        return None
    return L, U


def child_float(spec, region, b, s, side):
    L, U = list(region[0]), list(region[1])
    if side == 0:
        U[b] = s
    else:
        L[b] = s
    return propagate_float(spec, L, U)


def F_value(p):
    n = len(p)
    P = np.convolve(p, p)
    S_ = np.concatenate([[0.0], np.cumsum(P)])
    c1, c2 = np.triu_indices(2 * n - 1)
    return float((2.0 * n / (c2 - c1 + 2) * (S_[c2 + 1] - S_[c1])).max())


def choose_branch(model, x, L, U):
    spec = model.spec
    o = model.opts
    m = x[model.blockcol]
    z = x[model.mc_z]
    gap = np.abs(z - m[model.mc_d] * m[model.mc_e])
    if o["score_dual"] and model.last_rd is not None and len(model.last_rd) == len(model.lprows):
        ydual = np.zeros(model.npairs)
        lr = model.lprows; mcm = (lr >= model.nfixed) & (lr < model.nrow)
        np.add.at(ydual, (lr[mcm] - model.nfixed) // 4, np.abs(model.last_rd[mcm]))
        gap = gap * (1.0 + o["score_dual"] * ydual / max(1e-12, ydual.max()))
    score = np.zeros(spec.nB)
    np.add.at(score, model.mc_d, gap); np.add.at(score, model.mc_e, gap * (~model.mc_diag))
    width = np.asarray(U) - np.asarray(L)
    score[width < 8.0 / SCALE] = -1.0
    b = int(np.argmax(score))
    if score[b] <= 0:
        b = int(np.argmax(width))
    cl = o["split_clip"]
    lo, hi = L[b] + cl * width[b], U[b] - cl * width[b]
    s = min(max(m[b], lo), hi)
    s = round(s * SCALE) / SCALE
    if not (L[b] < s < U[b]):
        s = round(0.5 * (L[b] + U[b]) * SCALE) / SCALE
    if not (L[b] < s < U[b]):
        raise RuntimeError("cannot split")
    return b, s


def midpoint_split(reg):
    width = np.asarray(reg[1]) - np.asarray(reg[0])
    b = int(np.argmax(width))
    s = round(0.5 * (reg[0][b] + reg[1][b]) * SCALE) / SCALE
    if not (reg[0][b] < s < reg[1][b]):
        return None
    return b, s


class Interrupted(Exception):
    pass


_SELFCHECK = {}


def selfcheck_record(model, rec, reg, cut_defs):
    """Exact check of one D/E/F record with verify2.py's own code (if importable).  Returns True/False/None."""
    if "v2" not in _SELFCHECK:
        try:
            import verify2
            _SELFCHECK["v2"] = verify2
            _SELFCHECK["spec"] = verify2.Spec(model.n)
            _SELFCHECK["rk"] = [tuple(k) for k in model.rowkeys]
        except Exception:
            _SELFCHECK["v2"] = None
    v2 = _SELFCHECK["v2"]
    if v2 is None:
        return None
    spec = _SELFCHECK["spec"]; rk = _SELFCHECK["rk"]
    region = ([Fr(float(v)) for v in reg[0]], [Fr(float(v)) for v in reg[1]])
    lam = getattr(model, "lam_exact", None)
    if lam is None:
        lam = Fr(model.lam).limit_denominator(10 ** 9)
    if rec[0] == "F":
        return v2.farkas_ok(spec, region, rk, rec[1], rec[2])
    comp = None
    if rec[0] == "D":
        if model.n not in v2._COMP:
            v2._COMP[model.n] = v2.Completion(spec, rk)
        comp = v2._COMP[model.n]
    rows, cuts = v2._int_record(rec, rec[0], rk, cut_defs, comp, spec)
    if rec[0] == "D":
        rows = rows + comp.complete(spec, region, rk, rows, cuts)
    return v2.ns_bound(spec, region, rk, rows, cuts) >= lam


def process_subtree(model, region, path, out, lam, max_nodes, stop_flag=None, depth_limit=None):
    """DFS from region.  Appends records to out; returns (stats, delegated list of (path, region))."""
    spec = model.spec
    o = model.opts
    plain = not o["compress"] and o["psd"] != "m3"
    if model.ncut > (model.cap - model.nrow) // 2 or model.cut_nnz > 4_000_000:
        model.reset_cuts()
    stack = [(region, path, None)]
    stats = {"nodes": 0, "leaves": 0, "farkas": 0, "empty": 0, "minlb": float("inf"), "internal": 0,
             "D": 0, "E": 0, "L": 0, "K": 0, "encode_fail": 0, "selfcheck": 0, "selfcheck_fail": 0, "lperr": 0, "U": 0}
    delegated = []
    emitted = {}                        # cut id (row index - nrow) -> key, defined in this job

    def emit_split(reg, pth, b, s, pb=None):
        out.append(["I", b, frac_str(s)]); stats["internal"] += 1
        for side in (0, 1):
            c = child_float(spec, reg, b, s, side)
            if c is None:
                stats["empty"] += 1
            else:
                stack.append((c, pth + [(b, s, side)], pb if side == 0 else None))

    while stack:
        if stop_flag is not None and stop_flag():
            raise Interrupted()
        reg, pth, basis = stack.pop()
        if (max_nodes is not None and stats["nodes"] >= max_nodes) or (depth_limit is not None and len(pth) >= depth_limit):
            out.append(["S"]); delegated.append((pth, reg)); continue
        stats["nodes"] += 1
        if stats["nodes"] % o["purge_every"] == 0:
            model.purge()
        model.set_region(reg[0], reg[1])
        if basis is not None and o["restore"]:
            model.set_basis(basis)
        st, obj, x, y = model.solve_node()
        if st == "farkas":
            rec = model.encode_farkas(y, reg[0], reg[1]) if not plain else None
            if plain and y is not None and not np.any(y[model.nrow:] != 0):
                nz = np.nonzero(y[: model.nrow])[0]
                rec = ["F", nz.tolist(), [float(v) for v in y[nz]]]
            if rec is not None:
                out.append(rec); stats["farkas"] += 1
                continue
            st = "error"                 # no usable ray: midpoint split below
        if st == "error":
            stats["lperr"] += 1
            ms = midpoint_split(reg)
            if ms is None:
                raise RuntimeError("LP failure on a region too small to split at " + str(pth))
            emit_split(reg, pth, ms[0], ms[1])
            continue
        if st == "leaf" and o.get("tree_only"):
            # tree-only certificate (tree/verify_tree.py): no duals; the verifier re-solves the leaf LP and separates
            # its own square cuts.  Leaves with a thin float margin carry their duals as a verify_cmp L record.
            if obj >= lam + o.get("tree_margin", 1e-7):
                out.append(["U"])
            else:
                nz = np.nonzero(y[: model.nrow])[0]
                cz = np.nonzero(y[model.nrow:])[0] + model.nrow
                sc2 = 4.0 ** o["psd_bits"]
                rec = ["L", obj, nz.tolist(), [float(v) for v in y[nz]]]
                if len(cz):
                    rec.append([[model.cut_key[c], float(y[c]) / sc2] for c in cz])
                out.append(rec); stats["L"] += 1
            stats["leaves"] += 1; stats["U"] += 1; stats["minlb"] = min(stats["minlb"], obj)
            continue
        if st == "leaf":
            if plain:
                nz = np.nonzero(y[: model.nrow])[0]
                out.append(["L", obj, nz.tolist(), [float(v) for v in y[nz]]])
                stats["leaves"] += 1; stats["L"] += 1; stats["minlb"] = min(stats["minlb"], obj)
                continue
            enc = model.encode_leaf(y, reg[0], reg[1])
            if enc is not None and o["selfcheck"] > 0 and random.random() < o["selfcheck"]:
                rec0 = enc[0]
                need = [cid for cid, _ in rec0[6]] if len(rec0) == 7 else []
                table = dict(emitted); table.update({cid: model.cut_key[cid + model.nrow] for cid in need})
                ok = selfcheck_record(model, rec0, reg, table)
                if ok is not None:
                    stats["selfcheck"] += 1
                    if not ok:
                        stats["selfcheck_fail"] += 1
                        enc = None
            if enc is not None:
                rec, lbv = enc
                if len(rec) == 7:
                    for cid, _ in rec[6]:
                        if cid not in emitted:
                            key = model.cut_key[cid + model.nrow]
                            out.append(["K", cid, key]); emitted[cid] = key; stats["K"] += 1
                out.append(rec)
                stats["leaves"] += 1; stats[rec[0]] += 1; stats["minlb"] = min(stats["minlb"], lbv)
                continue
            stats["encode_fail"] += 1     # no encoding passed the re-check: branch instead (rare)
            ms = choose_branch(model, x, reg[0], reg[1]) if x is not None else midpoint_split(reg)
            if ms is None:
                raise RuntimeError("leaf encoding failed on a region too small to split at " + str(pth))
            emit_split(reg, pth, ms[0], ms[1])
            continue
        p = np.maximum(x[: model.n], 0)
        if p.sum() > 0 and F_value(p / p.sum()) < lam:
            raise RuntimeError(f"COUNTEREXAMPLE F={F_value(p/p.sum())} p={p.tolist()}")
        b, s = choose_branch(model, x, reg[0], reg[1])
        emit_split(reg, pth, b, s, model.get_basis() if o["restore"] else None)
    return stats, delegated


# ---------------------------------------------------------------- file queue (same semantics as bnbcert.py)
def write_job_log(path_file, header, records):
    tmp = path_file + ".tmp"
    with gzip.open(tmp, "wt", compresslevel=6) as fh:
        fh.write(json.dumps(header) + "\n")
        for r in records:
            fh.write(json.dumps(r) + "\n")
    os.replace(tmp, path_file)


def new_job(certdir, path):
    """Write the job spec outside todo/ first, then rename atomically into todo/ (no partial files in todo/)."""
    jid = uuid.uuid4().hex
    tmpdir = os.path.join(certdir, "tmpjobs")
    os.makedirs(tmpdir, exist_ok=True)
    tmp = os.path.join(tmpdir, jid + ".json")
    with open(tmp, "w") as fh:
        json.dump({"id": jid, "path": [[b, frac_str(s), side] for b, s, side in path]}, fh)
    os.replace(tmp, os.path.join(certdir, "todo", jid + ".json"))
    return jid


def load_opts(certdir):
    f = os.path.join(certdir, "opts.json")
    return json.load(open(f)) if os.path.exists(f) else {}


def make_model(n, lam, opts):
    m = Model(n, float(lam), opts)
    m.lam_exact = Fr(lam)
    return m


def cmd_init(certdir, n, lam_str, depth, opts):
    lam = Fr(lam_str)
    for d in ("jobs", "todo", "running", "done"):
        os.makedirs(os.path.join(certdir, d), exist_ok=True)
    with open(os.path.join(certdir, "opts.json"), "w") as fh:
        json.dump(opts, fh)
    model = make_model(n, lam, opts)
    meta = {"n": n, "lam": str(lam), "rowkeys": model.rowkeys, "colkeys": model.colkeys,
            "splitbits": SPLITBITS, "created": time.strftime("%Y-%m-%d %H:%M:%S"),
            "solver": "bnbtree" if model.opts.get("tree_only") else "bnbcert2", "format": 1 if (not model.opts["compress"] and model.opts["psd"] != "m3") else 2,
            "opts": model.opts}
    with open(os.path.join(certdir, "meta.json"), "w") as fh:
        json.dump(meta, fh)
    region = model.root_region_float
    out = []
    t0 = time.time()
    stats, delegated = process_subtree(model, (list(region[0]), list(region[1])), [], out, float(lam), None, depth_limit=depth)
    header = {"n": n, "lam": str(lam), "path": [], "id": "root", "stats": stats}
    for pth, reg in delegated:
        new_job(certdir, pth)
    write_job_log(os.path.join(certdir, "jobs", "root.jsonl.gz"), header, out)
    print(f"init: {stats} delegated={len(delegated)} time={time.time()-t0:.1f}s")


def worker_loop(certdir, max_nodes, wid):
    meta = json.load(open(os.path.join(certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    model = make_model(n, lam, load_opts(certdir))
    if [list(k) for k in model.rowkeys] != meta["rowkeys"]:
        raise RuntimeError("meta.json rowkeys differ from this solver's canonical rows")
    spec = model.spec
    random.seed(os.getpid())
    stop = {"flag": False}

    def handler(signum, frame):
        stop["flag"] = True
    signal.signal(signal.SIGTERM, handler)
    done_nodes = 0
    while not stop["flag"]:
        todo = sorted(glob.glob(os.path.join(certdir, "todo", "*.json")))
        if not todo:
            if glob.glob(os.path.join(certdir, "running", "*.json")):
                time.sleep(2.0)       # other workers may still delegate new jobs
                continue
            break
        claimed = None
        for f in todo[wid % max(1, len(todo)):] + todo[: wid % max(1, len(todo))]:
            dst = os.path.join(certdir, "running", os.path.basename(f))
            try:
                os.rename(f, dst)
                claimed = dst; break
            except FileNotFoundError:
                continue
        if claimed is None:
            continue
        job = json.load(open(claimed))
        path = [(int(b), float(Fr(s)), int(side)) for b, s, side in job["path"]]
        reg = (list(model.root_region_float[0]), list(model.root_region_float[1]))
        for (b, s, side) in path:
            reg = child_float(spec, reg, b, s, side)
        out = []
        try:
            stats, delegated = process_subtree(model, reg, path, out, float(lam), max_nodes, stop_flag=lambda: stop["flag"])
        except Interrupted:
            os.rename(claimed, os.path.join(certdir, "todo", os.path.basename(claimed)))
            break
        for pth, rg in delegated:
            new_job(certdir, pth)
        header = {"n": n, "lam": str(lam), "path": job["path"], "id": job["id"], "stats": stats}
        write_job_log(os.path.join(certdir, "jobs", job["id"] + ".jsonl.gz"), header, out)
        os.rename(claimed, os.path.join(certdir, "done", os.path.basename(claimed)))
        done_nodes += stats["nodes"]
    return done_nodes


def cmd_recover(certdir):
    """Move jobs left in running/ by an interrupted run back to todo/ (only when no worker is alive)."""
    for f in glob.glob(os.path.join(certdir, "running", "*.json")):
        jid = os.path.basename(f)[:-5]
        if not os.path.exists(os.path.join(certdir, "jobs", jid + ".jsonl.gz")):
            os.rename(f, os.path.join(certdir, "todo", os.path.basename(f)))
        else:
            os.rename(f, os.path.join(certdir, "done", os.path.basename(f)))


def cmd_work(certdir, workers, max_nodes):
    import multiprocessing as mp
    ctx = mp.get_context("fork")
    t0 = time.time()
    stopping = {"flag": False}
    while not stopping["flag"]:
        if not glob.glob(os.path.join(certdir, "todo", "*.json")):
            break
        procs = [ctx.Process(target=worker_loop, args=(certdir, max_nodes, w)) for w in range(workers)]
        for p in procs:
            p.start()

        def term(signum, frame):
            stopping["flag"] = True
            for p in procs:
                if p.is_alive():
                    os.kill(p.pid, signal.SIGTERM)
        signal.signal(signal.SIGTERM, term)
        for p in procs:
            p.join()
        if any(p.exitcode not in (0, None) for p in procs):
            print("worker failure", [p.exitcode for p in procs]); break
    print(f"work: done in {time.time()-t0:.1f}s")


def cmd_status(certdir):
    nt = len(glob.glob(os.path.join(certdir, "todo", "*.json")))
    nr = len(glob.glob(os.path.join(certdir, "running", "*.json")))
    nd = len(glob.glob(os.path.join(certdir, "done", "*.json")))
    tot = {"nodes": 0, "leaves": 0, "farkas": 0, "empty": 0}
    extra = {}
    minlb = float("inf")
    for f in glob.glob(os.path.join(certdir, "jobs", "*.jsonl.gz")):
        with gzip.open(f, "rt") as fh:
            h = json.loads(fh.readline())
        st = h.get("stats")
        if st:
            for k in tot:
                tot[k] += st[k]
            for k in ("D", "E", "L", "K", "encode_fail", "selfcheck", "selfcheck_fail", "lperr"):
                if k in st:
                    extra[k] = extra.get(k, 0) + st[k]
            minlb = min(minlb, st["minlb"])
    print(f"todo={nt} running={nr} done={nd} totals={tot} {extra} minlb={minlb}")


if __name__ == "__main__":
    import argparse
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "init":
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir"); ap.add_argument("n", type=int)
        ap.add_argument("lam"); ap.add_argument("--depth", type=int, default=10)
        ap.add_argument("--plain", action="store_true", help="old format (no square cuts, no compression): src/verify.py checks it")
        ap.add_argument("--opts", default="{}", help="JSON overrides of DEFAULT_OPTS")
        a = ap.parse_args()
        opts = dict(PLAIN_OPTS) if a.plain else {}
        opts.update(json.loads(a.opts))
        cmd_init(a.certdir, a.n, a.lam, a.depth, opts)
    elif cmd == "work":
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir")
        ap.add_argument("--workers", type=int, default=1); ap.add_argument("--max-nodes", type=int, default=20000)
        a = ap.parse_args(); cmd_work(a.certdir, a.workers, a.max_nodes)
    elif cmd == "recover":
        cmd_recover(sys.argv[2])
    elif cmd == "status":
        cmd_status(sys.argv[2])
    else:
        sys.exit(__doc__)
