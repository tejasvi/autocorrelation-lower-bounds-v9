"""Optimized certifying branch-and-bound for V_n >= lam.  Same certificate format as src/bnbcert.py
(same meta.json rowkeys/colkeys, same job-log records), so src/verify.py checks its output unchanged.

Differences to bnbcert (all are solver-side only; the certificate semantics are untouched):
  * lazy rows: window rows and McCormick rows enter the HiGHS LP only when violated at the LP point
    (cutting-plane loop per node), and leave it after `max_age` nodes without dual weight.  A leaf dual
    is padded with zeros for rows not in the LP; since the LP with a row subset is a relaxation of the
    full LP, the padded vector is an admissible dual of the full LP and the verifier's Neumaier-Shcherbina
    bound LB(y) is computed over the full row set exactly as before.
  * basis restore: the second child of a node is warm-started from the parent's optimal basis
    (stored with the parent's row set; rows deleted meanwhile are re-added if they were nonbasic).
  * HiGHS objective_bound = lam + 1e-6: the dual simplex stops as soon as its (dual feasible) objective
    exceeds lam; the duals at that point are certified with the same safe bound.
"""
import sys, os, json, gzip, time, uuid, glob, signal
from fractions import Fraction as Fr
import numpy as np
import scipy.sparse as sp
import highspy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify import Spec, TMAX

SPLITBITS = 30
SCALE = float(2 ** SPLITBITS)
LB_MARGIN = 1e-9
INF = highspy.kHighsInf
S = highspy.HighsBasisStatus
ENUM = [S.kLower, S.kBasic, S.kUpper, S.kZero, S.kNonbasic]
BASIC = 1
MS = highspy.HighsModelStatus

DEFAULT_OPTS = dict(lazy_win=True, lazy_mc=True, restore=True, objbound=True,
                    add_cap=400, max_rounds=30, viol_tol=1e-7, purge_every=20, max_age=40, init_full=False,
                    hopts={"simplex_dual_edge_weight_strategy": 1},
                    psd="", psd_rounds=3, psd_k=3, psd_tol=1e-6, psd_bits=20, cut_max_age=30, cutcap=200000,
                    rc=False, rc_frac=0.05, rc_max=8, rc_margin=1e-7, inherit=False, psd_levels=[2, 3, 4], lvl_k=1,
                    split_clip=0.25, score_alpha=0.0, score_dual=20.0,
                    compress=False, cut_table=False, compress_F=[20, 24, 28, 32, 40, 48], presep=False,
                    pc_gamma=0.0, pc_min=4, psd_gap=0.0)


def frac_str(x):
    return str(Fr(x))


class OptModel:
    def __init__(self, n, lam, opts=None):
        self.opts = dict(DEFAULT_OPTS); self.opts.update(opts or {})
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
        # ---- rows (identical order to bnbcert.Model)
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
        self.A = A                          # universe rows at the root region (mc part refreshed on the fly)
        self.row_lo, self.row_up = rows_lo, rows_up
        self.AfixT = A[: self.nfixed].T.tocsr()
        # McCormick structure
        self.npairs = len(self.pairs)
        self.mc_z = np.array([self.cix[spec.canon_pair(d, e)] for (d, e) in self.pairs])
        self.mc_md = np.array([self.cix[("m", d)] for (d, e) in self.pairs])
        self.mc_me = np.array([self.cix[("m", e)] for (d, e) in self.pairs])
        self.mc_d = np.array([d for (d, e) in self.pairs]); self.mc_e = np.array([e for (d, e) in self.pairs])
        self.mc_diag = self.mc_d == self.mc_e
        self.blockcol = np.array([self.cix[("m", b)] for b in range(nB)])
        self.block_size = np.array([t[1] - t[0] for t in tree], float)
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
        # window data for separation
        wk = rowkeys[: self.nwin]
        self.w_c1 = np.array([k[1] for k in wk]); self.w_c2 = np.array([k[2] for k in wk])
        self.w_w = np.array([2.0 * n / (k[2] - k[1] + 2) for k in wk])
        self.gcol = np.array([self.cix[("G", c)] for c in range(2 * n - 1)])
        # which rows are lazy
        self.cap = cap = self.nrow + int(self.opts["cutcap"])
        self.row_lo = np.concatenate([self.row_lo, np.full(cap - self.nrow, 0.0)])
        self.row_up = np.concatenate([self.row_up, np.full(cap - self.nrow, INF)])
        kind = np.zeros(cap, dtype=np.int8)       # 0 always, 1 window, 2 mc, 3 dynamic cut
        kind[: self.nwin] = 1
        kind[self.nfixed:self.nrow] = 2
        kind[self.nrow:] = 3
        self.kind = kind
        lazy = np.zeros(cap, bool)
        lazy[self.nrow:] = True
        if self.opts["lazy_win"]:
            lazy[kind == 1] = True
        if self.opts["lazy_mc"]:
            lazy[kind == 2] = True
        # duplicate diagonal mc rows (q=3 equals q=2 when d == e) are never used
        diag_dup = np.zeros(cap, bool)
        for k in np.nonzero(self.mc_diag)[0]:
            diag_dup[self.nfixed + 4 * k + 3] = True
        self.never = diag_dup
        self.lazy = lazy
        # ---- HiGHS model with the always-present rows
        h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("threads", 1)
        h.setOptionValue("presolve", "off")
        h.setOptionValue("solver", "simplex")
        h.setOptionValue("simplex_strategy", 1)
        h.setOptionValue("simplex_iteration_limit", 30000)   # a stalled solve returns instead of running forever
        for k, v in self.opts.get("hopts", {}).items():
            h.setOptionValue(k, v)
        self.h = h
        lp = highspy.HighsLp()
        lp.num_col_ = self.ncol; lp.num_row_ = 0
        lp.col_cost_ = self.cost; lp.col_lower_ = lb.copy(); lp.col_upper_ = ub.copy()
        h.passModel(lp)
        self.pos = np.full(cap, -1, dtype=np.int64)
        self.lprows = np.zeros(0, dtype=np.int64)
        self.age = np.zeros(cap, dtype=np.int32)
        self.ncut = 0; self.cut_cols = {}; self.cut_vals = {}; self.cut_key = {}; self.cut_seen = {}
        self.pcol = np.arange(n)                       # p_i columns
        zc = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for j in range(i, n):
                zc[i, j] = zc[j, i] = self.cix[("Z", i, j)]
        self.zcolmat = zc
        self.diagcol = np.array([self.cix[spec.canon_pair(b, b)] for b in range(1, nB)])
        self.diagblk = np.array([self.cix[("m", b)] for b in range(1, nB)])
        self.stats = {"lp": 0, "its": 0, "added": 0, "deleted": 0, "rounds": 0}
        init = np.nonzero(~lazy & ~self.never)[0]
        self.add_rows(init)
        self.objbound_on = False
        self.set_objbound(self.opts["objbound"])

    # ---- objective bound control
    def set_objbound(self, on):
        if on != self.objbound_on:
            self.h.setOptionValue("objective_bound", float(self.lam) + 1e-6 if on else INF)
            self.objbound_on = on

    # ---- McCormick coefficients (float mirror of Spec.row 'mc'), for a subset of pairs
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

    def row_entries(self, r):
        """(cols, vals, lo, up) of universe row r at the current region."""
        if self.kind[r] != 2:
            a, b = self.A.indptr[r], self.A.indptr[r + 1]
            return self.A.indices[a:b], self.A.data[a:b], self.row_lo[r], self.row_up[r]
        k, q = divmod(r - self.nfixed, 4)
        cz, cmd, cme, rhs = self.mc_coeffs(self.L, self.U, np.array([k]))
        if self.mc_diag[k]:
            cols = np.array([self.mc_z[k], self.mc_md[k]]); vals = np.array([cz[q, 0], cmd[q, 0]])
        else:
            cols = np.array([self.mc_z[k], self.mc_md[k], self.mc_me[k]]); vals = np.array([cz[q, 0], cmd[q, 0], cme[q, 0]])
        return cols, vals, -INF, float(rhs[q, 0])

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
        self.stats["added"] = self.stats.get("added", 0) + len(rows)

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
        self.stats["deleted"] += len(rows)

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
        # keep row_up of absent mc rows current lazily (only needed for rows in the LP and for float_bound)
        cols = self.blockcol[changed].astype(np.int32)
        self.col_lb[cols] = L[changed]; self.col_ub[cols] = U[changed]
        self.h.changeColsBounds(len(cols), cols, L[changed].copy(), U[changed].copy())

    # ---- basis store / restore
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
        rs = status[self.lprows]
        nb = highspy.HighsBasis()
        nb.col_status = [ENUM[i] for i in cst]
        nb.row_status = [ENUM[i] for i in rs]
        nb.valid = True
        self.h.setBasis(nb)

    # ---- LP solve with status handling
    def run(self):
        h = self.h
        h.run()
        st = h.getModelStatus()
        self.stats["lp"] += 1; self.stats["its"] += h.getInfo().simplex_iteration_count
        if st not in (MS.kOptimal, MS.kInfeasible, MS.kObjectiveBound):
            # cold retry with dual steepest-edge pricing (Devex can stall on degenerate LPs); restore afterwards
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

    def float_bound(self, y):
        """Neumaier-Shcherbina bound in floats over the full row set (absent rows have y = 0)."""
        nr = self.nrow + self.ncut
        yfull = y
        y = y[:nr].copy()
        lo, up = self.row_lo[:nr], self.row_up[:nr]
        # refresh rhs of mc rows with nonzero dual (rows in the LP are current already)
        y[(y > 0) & ~np.isfinite(lo)] = 0.0
        y[(y < 0) & ~np.isfinite(up)] = 0.0
        rowpart = float(np.sum(np.where(y > 0, y * np.where(np.isfinite(lo), lo, 0.0), y * np.where(np.isfinite(up), up, 0.0))))
        r = self.cost - self.AfixT @ y[: self.nfixed]
        cz, cmd, cme, rhs = self.mc_coeffs(self.L, self.U)
        ym = y[self.nfixed:self.nrow].reshape(-1, 4).T
        for cid in np.nonzero(y[self.nrow:])[0] + self.nrow:
            np.subtract.at(r, np.array(self.cut_cols[cid]), y[cid] * np.array(self.cut_vals[cid]))
        np.subtract.at(r, self.mc_z, (cz * ym).sum(0))
        np.subtract.at(r, self.mc_md, (cmd * ym).sum(0))
        np.subtract.at(r, self.mc_me, (cme * ym).sum(0))
        colpart = float(np.sum(np.minimum(r * self.col_lb, r * self.col_ub)))
        yfull = np.zeros(len(yfull)); yfull[:nr] = y
        return rowpart + colpart, yfull

    def ns_bound(self, y, L, U):
        """Float Neumaier-Shcherbina bound of dual y for an arbitrary region (L, U) (rows rebuilt from L, U),
        independent of the HiGHS state.  Returns (bound, reduced costs r)."""
        L = np.asarray(L, float); U = np.asarray(U, float)
        cz, cmd, cme, rhs = self.mc_coeffs(L, U)
        nr = self.nrow + self.ncut
        lo = self.row_lo[:nr].copy(); up = self.row_up[:nr].copy()
        up[self.nfixed:self.nrow] = rhs.T.reshape(-1)
        y = y[:nr].copy()
        y[(y > 0) & ~np.isfinite(lo)] = 0.0
        y[(y < 0) & ~np.isfinite(up)] = 0.0
        rowpart = float(np.sum(np.where(y > 0, y * np.where(np.isfinite(lo), lo, 0.0), y * np.where(np.isfinite(up), up, 0.0))))
        r = self.cost - self.AfixT @ y[: self.nfixed]
        ym = y[self.nfixed:self.nrow].reshape(-1, 4).T
        for cid in np.nonzero(y[self.nrow:])[0] + self.nrow:
            np.subtract.at(r, np.array(self.cut_cols[cid]), y[cid] * np.array(self.cut_vals[cid]))
        np.subtract.at(r, self.mc_z, (cz * ym).sum(0))
        np.subtract.at(r, self.mc_md, (cmd * ym).sum(0))
        np.subtract.at(r, self.mc_me, (cme * ym).sum(0))
        clb = self.col_lb.copy(); cub = self.col_ub.copy()
        clb[self.blockcol] = L; cub[self.blockcol] = U
        colpart = float(np.sum(np.minimum(r * clb, r * cub)))
        return rowpart + colpart, r

    def rc_candidates(self, y, L, U):
        """Reduced-cost tightenings certified by the dual y of region (L, U): list of (frac, b, s, leafside).
        Validity: for any sub-box R' of the region, LB_{R'}(y) >= min over R' of the region's Lagrangian
        (McCormick rows of a sub-box are pointwise tighter on the sub-box), and that minimum is
        >= LB(y) + r_b (s - L_b) on {m_b >= s} (r_b > 0), resp. >= LB(y) + |r_b| (U_b - s) on {m_b <= s} (r_b < 0)."""
        lb, r = self.ns_bound(y, L, U)
        gap = self.lam - lb + self.opts["rc_margin"]
        if gap <= 0:
            return lb, []
        out = []
        rb = r[self.blockcol]
        for b in range(1, self.spec.nB):
            w = U[b] - L[b]
            if w < 64.0 / SCALE:
                continue
            if rb[b] > 0:
                sv = np.ceil((L[b] + gap / rb[b]) * SCALE) / SCALE
                if L[b] < sv < U[b] and (U[b] - sv) >= self.opts["rc_frac"] * w:
                    out.append(((U[b] - sv) / w, b, float(sv), 1))
            elif rb[b] < 0:
                sv = np.floor((U[b] - gap / (-rb[b])) * SCALE) / SCALE
                if L[b] < sv < U[b] and (sv - L[b]) >= self.opts["rc_frac"] * w:
                    out.append(((sv - L[b]) / w, b, float(sv), 0))
        out.sort(reverse=True)
        return lb, out[: self.opts["rc_max"]]

    def separate(self, x):
        """Universe ids of violated lazy rows (most violated first, capped)."""
        tol = self.opts["viol_tol"]
        cand = []; viol = []
        if self.opts["lazy_win"]:
            G = x[self.gcol]
            Gm = np.concatenate([[0.0], G])
            v = self.w_w * (Gm[self.w_c2 + 1] - Gm[self.w_c1]) - x[self.tcol]
            ids = np.nonzero(v > tol)[0]
            ids = ids[self.pos[ids] < 0]
            cand.append(ids); viol.append(v[ids])
        if self.opts["lazy_mc"]:
            cz, cmd, cme, rhs = self.mc_coeffs(self.L, self.U)
            z = x[self.mc_z]; md = x[self.mc_md]; me = x[self.mc_me]
            act = cz * z + cmd * md + cme * me - rhs          # [4, npairs], row: act <= 0
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

    def reset_cuts(self):
        """Drop every dynamic cut (LP rows and storage); called between jobs when the cut store is half full."""
        lr = self.lprows
        cuts = lr[self.kind[lr] == 3]
        if len(cuts):
            self.delete_rows(cuts)
        self.pos[self.nrow:self.nrow + self.ncut] = -1
        self.age[self.nrow:self.nrow + self.ncut] = 0
        self.ncut = 0; self.cut_cols = {}; self.cut_vals = {}; self.cut_key = {}; self.cut_seen = {}
        self.cut_nnz = 0
        self.stats["cut_resets"] = self.stats.get("cut_resets", 0) + 1

    def new_cut(self, cols, vals, lo, key):
        sig = (tuple(cols), tuple(np.round(np.array(vals) * 2 ** 30).astype(np.int64).tolist()), lo)
        if sig in self.cut_seen:
            return self.cut_seen[sig]
        if self.ncut >= self.cap - self.nrow:
            return None
        cid = self.nrow + self.ncut; self.ncut += 1
        self.cut_cols[cid] = np.asarray(cols, dtype=np.int32); self.cut_vals[cid] = np.asarray(vals, dtype=float)
        self.cut_key[cid] = key
        self.cut_nnz = getattr(self, "cut_nnz", 0) + len(cols)
        self.row_lo[cid] = lo; self.row_up[cid] = INF
        self.cut_seen[sig] = cid
        return cid

    def separate_psd(self, x):
        mode = self.opts["psd"]; tol = self.opts["psd_tol"]; sc = 2.0 ** self.opts["psd_bits"]
        new = []
        if "full" in mode:
            n = self.n
            M = np.empty((n + 1, n + 1)); M[0, 0] = 1.0
            p = x[self.pcol]; M[0, 1:] = p; M[1:, 0] = p
            M[1:, 1:] = x[self.zcolmat]
            w, V = np.linalg.eigh(M)
            for j in range(min(self.opts["psd_k"], int((w < -tol).sum()))):
                v = V[:, j] / np.abs(V[:, j]).max()
                v = np.round(v * sc) / sc
                cols = []; vals = []
                for i in range(n):
                    if v[0] * v[i + 1] != 0:
                        cols.append(int(self.pcol[i])); vals.append(2 * v[0] * v[i + 1])
                for i in range(n):
                    for k in range(i, n):
                        a = v[i + 1] * v[k + 1] * (1 if i == k else 2)
                        if a != 0:
                            cols.append(int(self.zcolmat[i, k])); vals.append(a)
                vi = np.round(v * sc).astype(np.int64)
                key = ["sq", int(vi[0]), [[int(self.spec.leaf_of_bin[i]), int(vi[i + 1])] for i in range(n) if vi[i + 1] != 0]]
                cid = self.new_cut(cols, vals, -v[0] ** 2, key)
                if cid is not None:
                    new.append(cid)
        if "tan" in mode:
            m = x[self.diagblk]; zd = x[self.diagcol]
            viol = m * m - zd
            for t in np.nonzero(viol > tol)[0]:
                a = round(m[t] * sc) / sc
                key = ["sq", -int(round(a * sc)), [[int(t) + 1, int(sc)]]]
                cid = self.new_cut([int(self.diagcol[t]), int(self.diagblk[t])], [1.0, -2 * a], -a * a, key)
                if cid is not None:
                    new.append(cid)
        if "lvl" in mode:
            for lev in self.opts["psd_levels"]:
                blocks = self.level_blocks(lev)
                k = len(blocks)
                if k < 2:
                    continue
                M = np.empty((k + 1, k + 1)); M[0, 0] = 1.0
                mb = x[self.blockcol[blocks]]
                M[0, 1:] = mb; M[1:, 0] = mb
                cm = self.pcolmat(blocks)
                M[1:, 1:] = x[cm]
                w, V = np.linalg.eigh(M)
                for j in range(min(self.opts["lvl_k"], int((w < -tol).sum()))):
                    v = V[:, j] / np.abs(V[:, j]).max(); v = np.round(v * sc) / sc
                    cols = []; vals = []
                    for a in range(k):
                        if v[0] * v[a + 1] != 0:
                            cols.append(int(self.blockcol[blocks[a]])); vals.append(2 * v[0] * v[a + 1])
                        for c in range(a, k):
                            cf = v[a + 1] * v[c + 1] * (1 if a == c else 2)
                            if cf != 0:
                                cols.append(int(cm[a, c])); vals.append(cf)
                    vi = np.round(v * sc).astype(np.int64)
                    key = ["sq", int(vi[0]), [[int(blocks[a]), int(vi[a + 1])] for a in range(k) if vi[a + 1] != 0]]
                    cid = self.new_cut(cols, vals, -v[0] ** 2, key)
                    if cid is not None:
                        new.append(cid)
        if "m3" in mode:
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
            for t in order[: self.opts["psd_k"] * 10]:
                if w[t, 0] >= -tol:
                    break
                v = V[t, :, 0] / np.abs(V[t, :, 0]).max(); v = np.round(v * sc) / sc
                cols = [int(self.blockcol[d[t]]), int(self.blockcol[e[t]]), int(self.diagcol[d[t] - 1]), int(self.mc_z[off][t]), int(self.diagcol[e[t] - 1])]
                vals = [2 * v[0] * v[1], 2 * v[0] * v[2], v[1] ** 2, 2 * v[1] * v[2], v[2] ** 2]
                vi = np.round(v * sc).astype(np.int64)
                key = ["sq", int(vi[0]), [[int(d[t]), int(vi[1])], [int(e[t]), int(vi[2])]]]
                cid = self.new_cut(cols, vals, -v[0] ** 2, key)
                if cid is not None:
                    new.append(cid)
        return np.array(new, dtype=np.int64)

    def compress_leaf(self, y, L, U):
        """Compressed leaf (verify_cmp.py 'D' record) or None: non-P/G/ZA duals rounded to int/2^F for the smallest F
        in compress_F whose float-screened bound, after completing the P/G/ZA duals, is >= lam + LB_MARGIN."""
        if not hasattr(self, "_imp"):
            from implied import Implied
            self._imp = Implied(self)
            aux = np.zeros(self.nrow, bool)
            aux[self._imp.grow] = True; aux[self._imp.prow] = True; aux[self._imp.za_rows] = True
            self._aux = aux
        idx = np.nonzero(y[: self.nrow])[0]
        idx = idx[~self._aux[idx]]
        cuts = np.nonzero(y[self.nrow:])[0] + self.nrow
        extra = [(np.array(self.cut_cols[c]), np.array(self.cut_vals[c]), y[c]) for c in cuts]
        for F in self.opts["compress_F"]:
            ints = np.round(y[idx] * 2.0 ** F)
            m = ints != 0
            yy = np.zeros(self.cap); yy[idx[m]] = ints[m] / 2.0 ** F; yy[cuts] = y[cuts]
            yr = self._imp.reconstruct(yy, L, U, extra)
            yr[cuts] = y[cuts]
            lb, _ = self.ns_bound(yr, L, U)
            if lb >= self.lam + LB_MARGIN:
                return F, lb, idx[m], ints[m]
        return None

    def level_blocks(self, lev):
        """Partition of the bins into tree blocks at depth lev (leaves above that depth are kept)."""
        if not hasattr(self, "_lvl"):
            self._lvl = {}
        if lev not in self._lvl:
            tree = self.spec.tree; out = []
            def rec(b, d):
                if d == lev or tree[b][3] < 0:
                    out.append(b)
                else:
                    rec(tree[b][3], d + 1); rec(tree[b][4], d + 1)
            rec(0, 0)
            self._lvl[lev] = np.array(out)
        return self._lvl[lev]

    def pcolmat(self, blocks):
        k = len(blocks); cm = np.zeros((k, k), dtype=np.int64)
        for a in range(k):
            for c in range(a, k):
                cm[a, c] = cm[c, a] = self.cix[self.spec.canon_pair(int(blocks[a]), int(blocks[c]))]
        return cm

    def update_ages(self, row_dual):
        """Age lazy rows without dual weight; returns nothing."""
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

    def solve_node(self):
        """Cutting-plane loop.  Returns (status, obj, x, y_full) with status in
        'leaf' (y_full certifies), 'farkas' (y_full ray), 'branch' (x converged or rounds exhausted), 'error'."""
        lam = self.lam
        psd_done = 0
        for rnd in range(self.opts["max_rounds"]):
            st = self.run()
            self.stats["rounds"] += 1
            if st == MS.kInfeasible:
                ray = self.dual_ray()
                if ray is None:
                    return "error", None, None, None
                return "farkas", None, None, self.full_dual(ray)
            if st == MS.kObjectiveBound:
                sol = self.h.getSolution()
                y = self.full_dual(np.array(sol.row_dual))
                yy = np.where(np.abs(y) > 1e-14, y, 0.0)
                lb, yy = self.float_bound(yy)
                if lb >= lam + LB_MARGIN:
                    self.update_ages(np.array(sol.row_dual))
                    return "leaf", lb, None, yy
                self.set_objbound(False)
                st = self.run()
                self.set_objbound(self.opts["objbound"])
                if st == MS.kInfeasible:
                    ray = self.dual_ray()
                    if ray is None:
                        return "error", None, None, None
                    return "farkas", None, None, self.full_dual(ray)
            if st != MS.kOptimal:
                return "error", None, None, None
            obj = self.h.getInfo().objective_function_value
            sol = self.h.getSolution()
            rd = np.array(sol.row_dual)
            x = np.array(sol.col_value)
            if obj >= lam + 1e-7:
                y = self.full_dual(rd)
                yy = np.where(np.abs(y) > 1e-14, y, 0.0)
                lb, yy = self.float_bound(yy)
                if lb >= lam + LB_MARGIN:
                    self.update_ages(rd)
                    return "leaf", lb, x, yy
            new = self.separate(x)
            if len(new) == 0 and self.opts["psd"] and psd_done < self.opts["psd_rounds"] and \
                    (self.opts["psd_gap"] <= 0 or lam - obj < self.opts["psd_gap"]):
                new = self.separate_psd(x); psd_done += 1
                new = new[self.pos[new] < 0] if len(new) else new
                self.stats["cuts"] = self.stats.get("cuts", 0) + len(new)
            if len(new) == 0:
                self.update_ages(rd)
                self.last_rd = rd
                return "branch", obj, x, (self.full_dual(rd) if (self.opts["rc"] or self.opts["inherit"]) else None)
            self.add_rows(new)
        self.update_ages(rd)
        return "branch", obj, x, (self.full_dual(rd) if (self.opts["rc"] or self.opts["inherit"]) else None)

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
    if o.get("score_dual", 0.0) and getattr(model, "last_rd", None) is not None:
        # weight each pair's gap by 1 + w * (dual weight of its McCormick rows in the LP)
        ydual = np.zeros(model.npairs)
        lr = model.lprows; mcm = (lr >= model.nfixed) & (lr < model.nrow)
        np.add.at(ydual, (lr[mcm] - model.nfixed) // 4, np.abs(model.last_rd[mcm]))
        if o["score_dual"] < 0:          # pure dual-weighted gap
            gap = gap * ydual
        else:
            gap = gap * (1.0 + o["score_dual"] * ydual / max(1e-12, ydual.max()))
    score = np.zeros(spec.nB)
    np.add.at(score, model.mc_d, gap); np.add.at(score, model.mc_e, gap * (~model.mc_diag))
    if o.get("score_alpha", 0.0):
        score = score * model.block_size ** o["score_alpha"]
    if o.get("pc_gamma", 0.0) and hasattr(model, "pc_sum"):
        cnt = model.pc_cnt; ok = (cnt[:, 0] >= o["pc_min"]) & (cnt[:, 1] >= o["pc_min"])
        if ok.sum() >= 2:
            pc = np.sqrt(np.maximum(model.pc_sum[:, 0] / np.maximum(cnt[:, 0], 1), 1e-9) *
                         np.maximum(model.pc_sum[:, 1] / np.maximum(cnt[:, 1], 1), 1e-9))
            ref = np.exp(np.mean(np.log(pc[ok])))
            f = np.where(ok, pc / ref, 1.0)
            score = score * f ** o["pc_gamma"]
    width = np.asarray(U) - np.asarray(L)
    score[width < 8.0 / SCALE] = -1.0
    b = int(np.argmax(score))
    if score[b] <= 0:
        b = int(np.argmax(width))
    cl = o.get("split_clip", 0.25)
    lo, hi = L[b] + cl * width[b], U[b] - cl * width[b]
    s = min(max(m[b], lo), hi)
    s = round(s * SCALE) / SCALE
    if not (L[b] < s < U[b]):
        s = round(0.5 * (L[b] + U[b]) * SCALE) / SCALE
    assert L[b] < s < U[b]
    return b, s


class Interrupted(Exception):
    pass


def process_subtree(model, region, path, out, lam, max_nodes, stop_flag=None, depth_limit=None):
    """DFS from region (same records and order as bnbcert.process_subtree)."""
    spec = model.spec
    restore = model.opts["restore"]
    stack = [(region, path, None, None, None)]
    stats = {"nodes": 0, "leaves": 0, "farkas": 0, "empty": 0, "minlb": float("inf"), "internal": 0, "rcleaves": 0}
    delegated = []

    emitted = set()
    o = model.opts
    if model.ncut > (model.cap - model.nrow) // 2 or getattr(model, "cut_nnz", 0) > 4_000_000:
        model.reset_cuts()
    if o["pc_gamma"] and not hasattr(model, "pc_sum"):
        model.pc_sum = np.zeros((spec.nB, 2)); model.pc_cnt = np.zeros((spec.nB, 2))

    def leaf_record(lb, y, reg):
        """Append the leaf's records (cut definitions first when cut_table is on)."""
        nz = np.nonzero(y[: model.nrow])[0]
        cz_ = np.nonzero(y[model.nrow:])[0] + model.nrow
        extra = []
        if len(cz_):
            sc2 = 4.0 ** o["psd_bits"]
            for c in cz_:
                if o["cut_table"]:
                    if c not in emitted:
                        out.append(["K", int(c - model.nrow), model.cut_key[c]]); emitted.add(c)
                    extra.append([int(c - model.nrow), float(y[c]) / sc2])
                else:
                    extra.append([model.cut_key[c], float(y[c]) / sc2])
        cmp_ = model.compress_leaf(y, reg[0], reg[1]) if o["compress"] else None
        if cmp_ is not None:
            F, lbc, ii, ints = cmp_
            rec = ["D", lbc, int(F), ii.tolist(), [int(v) for v in ints]]
        else:
            rec = ["L", lb, nz.tolist(), [float(v) for v in y[nz]]]
        if extra:
            rec.append(extra)
        out.append(rec)

    while stack:
        if stop_flag is not None and stop_flag():
            raise Interrupted()
        reg, pth, basis, pend, xpar = stack.pop()
        if pend is not None:              # leaf piece cut off by a reduced-cost tightening: certified by a stored dual
            leaf_record(pend[0], pend[1], reg)
            stats["leaves"] += 1; stats["rcleaves"] += 1; stats["minlb"] = min(stats["minlb"], pend[0])
            continue
        if (max_nodes is not None and stats["nodes"] >= max_nodes) or (depth_limit is not None and len(pth) >= depth_limit):
            out.append(["S"]); delegated.append((pth, reg)); continue
        stats["nodes"] += 1
        if stats["nodes"] % model.opts["purge_every"] == 0:
            model.purge()
        model.set_region(reg[0], reg[1])
        if basis is not None:
            model.set_basis(basis)
        if o["presep"] and xpar is not None:
            pre = model.separate(xpar[0] if isinstance(xpar, tuple) else xpar)
            if len(pre):
                model.add_rows(pre)
                stats["presep"] = stats.get("presep", 0) + len(pre)
        st, obj, x, y = model.solve_node()
        if o["pc_gamma"] and xpar is not None and isinstance(xpar, tuple) and obj is not None:
            zpar, bb, side_, frac = xpar[1], xpar[2], xpar[3], xpar[4]
            if frac > 0:
                gain = max(0.0, min(obj, lam + 0.05) - zpar) / frac
                model.pc_sum[bb, side_] += gain; model.pc_cnt[bb, side_] += 1
        if st == "farkas":
            nz = np.nonzero(np.abs(y) > 0)[0]
            out.append(["F", nz.tolist(), [float(v) for v in y[nz]]])
            stats["farkas"] += 1
            continue
        if st == "leaf":
            leaf_record(obj, y, reg)
            stats["leaves"] += 1; stats["minlb"] = min(stats["minlb"], obj)
            continue
        if st == "error":
            stats["lperr"] = stats.get("lperr", 0) + 1
            width = np.asarray(reg[1]) - np.asarray(reg[0])
            b = int(np.argmax(width))
            s = round(0.5 * (reg[0][b] + reg[1][b]) * SCALE) / SCALE
            if not (reg[0][b] < s < reg[1][b]):
                raise RuntimeError("LP failure on a region too small to split at " + str(pth))
            out.append(["I", b, frac_str(s)]); stats["internal"] += 1
            for side in (0, 1):
                c = child_float(spec, reg, b, s, side)
                if c is None:
                    stats["empty"] += 1
                else:
                    stack.append((c, pth + [(b, s, side)], None, None, None))
            continue
        p = np.maximum(x[: model.n], 0)
        if p.sum() > 0 and F_value(p / p.sum()) < lam:
            raise RuntimeError(f"COUNTEREXAMPLE F={F_value(p/p.sum())} p={p.tolist()}")
        pb = model.get_basis() if restore else None
        if model.opts["rc"] and y is not None:
            lb0, cands = model.rc_candidates(y, reg[0], reg[1])
            cur, cpth = reg, pth
            did = 0
            for frac, b, sv, ls in cands:
                if not (cur[0][b] < sv < cur[1][b]):
                    continue
                piece = child_float(spec, cur, b, sv, ls)
                rest = child_float(spec, cur, b, sv, 1 - ls)
                if rest is None:
                    continue
                if piece is not None:
                    lbp, _ = model.ns_bound(y, piece[0], piece[1])
                    if lbp < lam + LB_MARGIN:
                        continue
                out.append(["I", b, frac_str(sv)]); stats["internal"] += 1; did += 1
                if piece is None:
                    stats["empty"] += 1
                elif ls == 1:            # leaf piece is processed first in DFS preorder: emit now
                    leaf_record(lbp, y, piece)
                    stats["leaves"] += 1; stats["rcleaves"] += 1; stats["minlb"] = min(stats["minlb"], lbp)
                else:                    # leaf piece comes after the subtree of the other side
                    stack.append((piece, cpth + [(b, sv, 0)], None, (lbp, y), None))
                cur, cpth = rest, cpth + [(b, sv, 1 - ls)]
            if did:
                stats["rc"] = stats.get("rc", 0) + did
                stack.append((cur, cpth, pb, None, None))       # re-solve the tightened region
                continue
        b, s = choose_branch(model, x, reg[0], reg[1])
        out.append(["I", b, frac_str(s)]); stats["internal"] += 1
        for side in (0, 1):
            c = child_float(spec, reg, b, s, side)
            if c is None:
                stats["empty"] += 1
                continue
            pend = None
            if model.opts["inherit"] and y is not None:
                lbc, _ = model.ns_bound(y, c[0], c[1])
                if lbc >= lam + LB_MARGIN:
                    pend = (lbc, y); stats["inherited"] = stats.get("inherited", 0) + 1
            wpar = reg[1][b] - reg[0][b]
            frac = 1.0 - (c[1][b] - c[0][b]) / wpar if wpar > 0 else 0.0
            stack.append((c, pth + [(b, s, side)], pb if side == 0 else None, pend, (x, obj, b, side, frac)))
    return stats, delegated


def bench(n, lam, opts, max_nodes=None, outfile=None):
    model = OptModel(n, lam, opts)
    out = []
    t0 = time.time(); c0 = time.process_time()
    stats, delegated = process_subtree(model, (list(model.root_region_float[0]), list(model.root_region_float[1])), [], out, lam, max_nodes)
    wall = time.time() - t0; cpu = time.process_time() - c0
    nbytes = len(("\n".join(json.dumps(r) for r in out)).encode())
    res = dict(n=n, lam=lam, opts=opts, wall=wall, cpu=cpu, ms_node=1000 * cpu / max(1, stats["nodes"]),
               bytes_per_leaf=nbytes / max(1, stats["leaves"]), lprows=len(model.lprows), **stats, **model.stats)
    if outfile:
        write_job_log(outfile, {"n": n, "lam": str(Fr(lam).limit_denominator(10 ** 6)), "path": [], "id": "root"}, out)
    return res, out, model


# ---------------------------------------------------------------- production CLI (same as bnbcert)
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


def cmd_init(certdir, n, lam_str, depth, opts):
    lam = Fr(lam_str)
    for d in ("jobs", "todo", "running", "done"):
        os.makedirs(os.path.join(certdir, d), exist_ok=True)
    model = OptModel(n, float(lam), opts)
    meta = {"n": n, "lam": str(lam), "rowkeys": model.rowkeys, "colkeys": model.colkeys,
            "splitbits": SPLITBITS, "created": time.strftime("%Y-%m-%d %H:%M:%S")}
    with open(os.path.join(certdir, "meta.json"), "w") as fh:
        json.dump(meta, fh)
    with open(os.path.join(certdir, "opts.json"), "w") as fh:
        json.dump(opts, fh)
    region = model.root_region_float
    out = []
    t0 = time.time()
    stats, delegated = process_subtree(model, (list(region[0]), list(region[1])), [], out, float(lam), None, depth_limit=depth)
    header = {"n": n, "lam": str(lam), "path": [], "id": "root"}
    for pth, reg in delegated:
        new_job(certdir, pth)
    write_job_log(os.path.join(certdir, "jobs", "root.jsonl.gz"), header, out)
    print(f"init: {stats} delegated={len(delegated)} time={time.time()-t0:.1f}s")


def worker_loop(certdir, max_nodes, wid):
    meta = json.load(open(os.path.join(certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    model = OptModel(n, float(lam), load_opts(certdir))
    assert model.rowkeys == [tuple(k) for k in meta["rowkeys"]] or [list(k) for k in model.rowkeys] == meta["rowkeys"]
    spec = model.spec
    stop = {"flag": False}

    def handler(signum, frame):
        stop["flag"] = True
    signal.signal(signal.SIGTERM, handler)
    done_nodes = 0
    while not stop["flag"]:
        todo = sorted(glob.glob(os.path.join(certdir, "todo", "*.json")))
        if not todo:
            if glob.glob(os.path.join(certdir, "running", "*.json")):
                time.sleep(2.0)
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


if __name__ == "__main__":
    import argparse
    cmd = sys.argv[1]
    if cmd == "bench":
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("n", type=int); ap.add_argument("lam", type=float)
        ap.add_argument("--opts", default="{}"); ap.add_argument("--max-nodes", type=int, default=None); ap.add_argument("--out", default=None)
        a = ap.parse_args()
        res, out, model = bench(a.n, a.lam, json.loads(a.opts), a.max_nodes, a.out)
        print(json.dumps(res), flush=True)
    elif cmd == "init":
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir"); ap.add_argument("n", type=int)
        ap.add_argument("lam"); ap.add_argument("--depth", type=int, default=10); ap.add_argument("--opts", default="{}")
        a = ap.parse_args(); cmd_init(a.certdir, a.n, a.lam, a.depth, json.loads(a.opts))
    elif cmd == "work":
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir")
        ap.add_argument("--workers", type=int, default=1); ap.add_argument("--max-nodes", type=int, default=20000)
        a = ap.parse_args(); cmd_work(a.certdir, a.workers, a.max_nodes)
