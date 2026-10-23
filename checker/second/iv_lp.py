"""iv_lp: floating-point LP oracle and square-cut separation for the second verifier.

Nothing computed here is trusted: the oracle only proposes dual vectors and square-cut keys.  Acceptance of a leaf is
decided by iv_core.ns_bound in exact arithmetic.  Written from the mathematics of the leaf LP (CERT_FORMAT.md
section 4), without copying from the certificate writer or the first checker.
"""
import numpy as np
import highspy
from fractions import Fraction
import iv_core as C

INF = highspy.kHighsInf
ITLIM = 50000           # simplex iterations per solve before a cold retry (a stalled solve must not hang a worker)


def robust_run(h, ok, pricing):
    """run; if the status is neither in ok nor infeasible (iteration limit, numerical trouble), retry once from a cold
    start with the other dual pricing (Devex <-> steepest edge) and a larger iteration limit."""
    h.run()
    st = h.getModelStatus()
    if st in ok or st == highspy.HighsModelStatus.kInfeasible:
        return st
    h.clearSolver()
    h.setOptionValue('simplex_dual_edge_weight_strategy', 2 if pricing == 1 else 1)
    h.setOptionValue('simplex_iteration_limit', 4 * ITLIM)
    h.run()
    st = h.getModelStatus()
    h.setOptionValue('simplex_dual_edge_weight_strategy', pricing)
    h.setOptionValue('simplex_iteration_limit', ITLIM)
    return st


class Oracle:
    def __init__(self, T, rows):
        self.T, self.rows = T, rows
        L0, U0 = C.root_region(T)
        # column set: every column named by a row (static rows, McCormick rows for any region) plus m_B and t
        cols = set(('m', b) for b in range(T.nB))
        cols.add(('t',))
        for r, k in enumerate(rows.keys):
            if k[0] == 'mc':
                D, E = k[1], k[2]
                cols.update([T.pair(D, E), ('m', D), ('m', E)])
            else:
                cols.update(rows.static[r][2].keys())
        order = {'m': 0, 'Z': 1, 'ZA': 2, 'P': 3, 'G': 4, 't': 5}
        self.cols = sorted(cols, key=lambda c: (order[c[0]],) + tuple(c[1:]))
        self.cid = {c: j for j, c in enumerate(self.cols)}
        nc = len(self.cols)
        lb = np.zeros(nc); ub = np.ones(nc)
        for j, c in enumerate(self.cols):
            a, b = C.col_bounds(c, L0, U0)
            lb[j], ub[j] = float(a), float(b)
        cost = np.zeros(nc); cost[self.cid[('t',)]] = 1.0
        self.nrow = len(rows.keys)
        rl, ru, start, idx, val = [], [], [], [], []
        for r in range(self.nrow):
            lo, up, ent = rows.row(r, L0, U0)
            rl.append(-INF if lo is None else float(lo)); ru.append(INF if up is None else float(up))
            start.append(len(idx))
            for c, a in ent.items():
                idx.append(self.cid[c]); val.append(float(a))
        h = highspy.Highs()
        h.setOptionValue('output_flag', False); h.setOptionValue('threads', 1); h.setOptionValue('presolve', 'off')
        h.setOptionValue('simplex_iteration_limit', ITLIM)
        lp = highspy.HighsLp()
        lp.num_col_ = nc; lp.num_row_ = self.nrow
        lp.col_cost_ = cost; lp.col_lower_ = lb; lp.col_upper_ = ub
        lp.row_lower_ = np.array(rl); lp.row_upper_ = np.array(ru)
        lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
        lp.a_matrix_.start_ = np.array(start + [len(idx)], dtype=np.int32)
        lp.a_matrix_.index_ = np.array(idx, dtype=np.int32)
        lp.a_matrix_.value_ = np.array(val)
        h.passModel(lp)
        self.h = h
        # McCormick bookkeeping: rows touching each block
        self.mc_of_block = [[] for _ in range(T.nB)]
        for r, k in enumerate(rows.keys):
            if k[0] == 'mc':
                self.mc_of_block[k[1]].append(r)
                if k[2] != k[1]:
                    self.mc_of_block[k[2]].append(r)
        self.region = (list(L0), list(U0))
        self.cuts = []          # list of (key, scale) in LP order after the base rows
        self.cut_ix = {}        # json-ish key string -> position
        self.mcol = np.array([self.cid[('m', b)] for b in range(T.nB)], dtype=np.int32)
        # separation index arrays (pairs of non-root blocks)
        pr = [(d, e) for d in range(1, T.nB) for e in range(d + 1, T.nB)]
        self.sep_d = np.array([d for d, e in pr]); self.sep_e = np.array([e for d, e in pr])
        self.sep_md = np.array([self.cid[('m', d)] for d, e in pr]); self.sep_me = np.array([self.cid[('m', e)] for d, e in pr])
        self.sep_dd = np.array([self.cid[T.pair(d, d)] for d, e in pr]); self.sep_ee = np.array([self.cid[T.pair(e, e)] for d, e in pr])
        self.sep_de = np.array([self.cid[T.pair(d, e)] for d, e in pr])

    def set_region(self, region):
        L, U = region
        oL, oU = self.region
        changed = [b for b in range(self.T.nB) if L[b] != oL[b] or U[b] != oU[b]]
        if not changed:
            return
        h = self.h
        touched = sorted(set(r for b in changed for r in self.mc_of_block[b]))
        for r in touched:
            lo, up, ent = self.rows.mc_row(self.rows.keys[r], L, U)
            for c, a in ent.items():
                h.changeCoeff(r, self.cid[c], float(a))
            h.changeRowBounds(r, -INF, float(up))
        cc = np.array([self.mcol[b] for b in changed], dtype=np.int32)
        h.changeColsBounds(len(cc), cc, np.array([float(L[b]) for b in changed]), np.array([float(U[b]) for b in changed]))
        self.region = (list(L), list(U))

    def add_cuts(self, keys):
        rl, start, idx, val = [], [], [], []
        new = []
        for key in keys:
            sk = repr(key)
            if sk in self.cut_ix:
                continue
            lo, up, ent = C.square_cut(self.T, key)
            s = max(abs(a) for a in ent.values())          # an integer >= 1 (integer coefficients)
            rl.append(float(lo / s)); start.append(len(idx))
            for c, a in ent.items():
                idx.append(self.cid[c]); val.append(float(a / s))
            new.append((key, s))
        if new:
            self.h.addRows(len(new), np.array(rl), np.full(len(new), INF), len(idx), np.array(start, dtype=np.int32),
                           np.array(idx, dtype=np.int32), np.array(val))
            for key, s in new:
                self.cut_ix[repr(key)] = len(self.cuts)
                self.cuts.append((key, s))
        return len(new)

    def drop_cuts(self, positions):
        if not positions:
            return
        pos = sorted(set(positions))
        self.h.deleteRows(len(pos), np.array([self.nrow + p for p in pos], dtype=np.int32))
        gone = set(pos)
        self.cuts = [c for i, c in enumerate(self.cuts) if i not in gone]
        self.cut_ix = {repr(k): i for i, (k, s) in enumerate(self.cuts)}

    def farkas(self):
        """dual ray of an infeasible LP (untrusted; checked exactly by the caller), or None."""
        h = self.h
        if h.getModelStatus() != highspy.HighsModelStatus.kInfeasible:
            return None
        out = h.getDualRay()                   # (HighsStatus, has_ray, ray)
        if not (isinstance(out, tuple) and len(out) == 3 and out[1]):
            return None
        return np.array(out[2], dtype=float)

    def solve(self):
        h = self.h
        st = robust_run(h, (highspy.HighsModelStatus.kOptimal,), -1)
        if st == highspy.HighsModelStatus.kInfeasible:
            return 'infeasible'
        if st != highspy.HighsModelStatus.kOptimal:
            return None
        sol = h.getSolution()
        y = np.array(sol.row_dual)
        x = np.array(sol.col_value)
        return h.getInfo().objective_function_value, x, y

    def separate(self, x, k=40, tol=1e-7, bits=20):
        """square cuts from the 3x3 moment matrices of block pairs: most negative eigenvalues first."""
        M = np.empty((len(self.sep_d), 3, 3))
        M[:, 0, 0] = 1.0
        M[:, 0, 1] = M[:, 1, 0] = x[self.sep_md]
        M[:, 0, 2] = M[:, 2, 0] = x[self.sep_me]
        M[:, 1, 1] = x[self.sep_dd]; M[:, 2, 2] = x[self.sep_ee]
        M[:, 1, 2] = M[:, 2, 1] = x[self.sep_de]
        w, V = np.linalg.eigh(M)
        order = np.argsort(w[:, 0])
        keys = []
        for t in order[:k]:
            if not (w[t, 0] < -tol):
                break
            v = V[t, :, 0]
            v = v / np.max(np.abs(v))
            iv = [int(round(float(c) * (1 << bits))) for c in v]
            if iv[1] == 0 and iv[2] == 0:
                continue
            keys.append(['sq', iv[0], [[int(self.sep_d[t]), iv[1]], [int(self.sep_e[t]), iv[2]]]])
        return keys


def to_dyadic(v, bits=50):
    """round a finite float to a multiple of 2^-bits (any dual is admissible, so rounding is sound)."""
    if not np.isfinite(v):
        return Fraction(0)
    return Fraction(int(round(v * (1 << bits))), 1 << bits)


def exact_farkas_value(orc, region, ray):
    """zero-objective NS value of a dual ray: > 0 proves the region's LP infeasible (section 6, F records).
    Both signs of the ray are tried (the oracle's sign convention for rays is not trusted)."""
    best = None
    for sg in (1.0, -1.0):
        row_duals = []
        for r in np.nonzero(ray[:orc.nrow])[0]:
            q = to_dyadic(sg * float(ray[r]))
            if q:
                row_duals.append((int(r), q))
        cut_duals = []
        for i, (key, s) in enumerate(orc.cuts):
            if orc.nrow + i < len(ray) and ray[orc.nrow + i] != 0.0:
                q = to_dyadic(sg * float(ray[orc.nrow + i])) / s
                if q:
                    cut_duals.append((C.square_cut(orc.T, key), q))
        v = C.ns_bound(orc.rows, region, row_duals, cut_duals, objective=False)
        best = v if best is None or v > best else best
    return best


def exact_leaf_bound(orc, region, y):
    """exact NS bound from the oracle dual y (base rows then cut rows, in LP order)."""
    nb = orc.nrow
    row_duals = []
    for r in np.nonzero(y[:nb])[0]:
        q = to_dyadic(float(y[r]))
        if q:
            row_duals.append((int(r), q))
    cut_duals = []
    for i, (key, s) in enumerate(orc.cuts):
        v = float(y[nb + i])
        if v != 0.0:
            q = to_dyadic(v) / s                    # dual of the unscaled cut row
            if q:
                cut_duals.append((C.square_cut(orc.T, key), q))
    return C.ns_bound(orc.rows, region, row_duals, cut_duals)


class LazyOracle:
    """Smaller HiGHS model for speed: the P, G, tree, ZA, rlt and sym rows are always present; window rows, McCormick
    rows and square cuts are present only while useful (added when violated at the LP point, removed after `maxage`
    leaves without dual weight).  Rows absent from the model have dual 0, which is admissible, so the duals of this
    relaxation are duals of the full row set.  Untrusted, like Oracle: it only proposes duals and cut keys."""

    def __init__(self, T, rows, lam, objbound=1e-6, devex=True, maxage=40, add_cap=400, tol=1e-9):
        self.T, self.rows = T, rows
        self.maxage, self.add_cap, self.tol = maxage, add_cap, tol
        L0, U0 = C.root_region(T)
        cols = set(('m', b) for b in range(T.nB)); cols.add(('t',))
        for r, k in enumerate(rows.keys):
            if k[0] == 'mc':
                cols.update([T.pair(k[1], k[2]), ('m', k[1]), ('m', k[2])])
            else:
                cols.update(rows.static[r][2].keys())
        order = {'m': 0, 'Z': 1, 'ZA': 2, 'P': 3, 'G': 4, 't': 5}
        self.cols = sorted(cols, key=lambda c: (order[c[0]],) + tuple(c[1:]))
        self.cid = {c: j for j, c in enumerate(self.cols)}
        nc = len(self.cols)
        lb = np.zeros(nc); ub = np.ones(nc)
        for j, c in enumerate(self.cols):
            a, b = C.col_bounds(c, L0, U0)
            lb[j], ub[j] = float(a), float(b)
        cost = np.zeros(nc); cost[self.cid[('t',)]] = 1.0
        h = highspy.Highs()
        h.setOptionValue('output_flag', False); h.setOptionValue('threads', 1); h.setOptionValue('presolve', 'off')
        h.setOptionValue('simplex_iteration_limit', ITLIM)
        self.pricing = 1 if devex else -1
        h.setOptionValue('simplex_dual_edge_weight_strategy', self.pricing)
        self.objbound = None if objbound is None else float(lam) + objbound
        if self.objbound is not None:
            h.setOptionValue('objective_bound', self.objbound)
        lp = highspy.HighsLp()
        lp.num_col_ = nc; lp.num_row_ = 0
        lp.col_cost_ = cost; lp.col_lower_ = lb; lp.col_upper_ = ub
        h.passModel(lp)
        self.h = h
        self.lp = []            # LP rows in order: int r (row of meta.rowkeys) or (key, scale) for a square cut
        self.age = []
        self.inlp = {}          # r -> True for base rows in the model; repr(key) -> True for cuts
        self.region = (list(L0), list(U0))
        self.Lf = np.array([float(v) for v in L0]); self.Uf = np.array([float(v) for v in U0])
        # vectorised lazy rows
        win = [r for r, k in enumerate(rows.keys) if k[0] == 'win']
        mc = [r for r, k in enumerate(rows.keys) if k[0] == 'mc']
        self.win_r = np.array(win, dtype=np.int64)
        self.win_w = np.array([2.0 * T.n / (rows.keys[r][2] - rows.keys[r][1] + 2) for r in win])
        self.win_g2 = np.array([self.cid[('G', rows.keys[r][2])] for r in win])
        self.win_g1 = np.array([self.cid[('G', rows.keys[r][1] - 1)] if rows.keys[r][1] > 0 else -1 for r in win])
        self.tcol = self.cid[('t',)]
        self.mc_r = np.array(mc, dtype=np.int64)
        self.mc_D = np.array([rows.keys[r][1] for r in mc], dtype=np.int64)
        self.mc_E = np.array([rows.keys[r][2] for r in mc], dtype=np.int64)
        self.mc_q = np.array([rows.keys[r][3] for r in mc], dtype=np.int64)
        self.mc_z = np.array([self.cid[T.pair(rows.keys[r][1], rows.keys[r][2])] for r in mc], dtype=np.int64)
        self.mc_mD = np.array([self.cid[('m', rows.keys[r][1])] for r in mc], dtype=np.int64)
        self.mc_mE = np.array([self.cid[('m', rows.keys[r][2])] for r in mc], dtype=np.int64)
        self.mcol = np.array([self.cid[('m', b)] for b in range(T.nB)], dtype=np.int32)
        pr = [(d, e) for d in range(1, T.nB) for e in range(d + 1, T.nB)]
        self.sep_d = np.array([d for d, e in pr]); self.sep_e = np.array([e for d, e in pr])
        self.sep_md = np.array([self.cid[('m', d)] for d, e in pr]); self.sep_me = np.array([self.cid[('m', e)] for d, e in pr])
        self.sep_dd = np.array([self.cid[T.pair(d, d)] for d, e in pr]); self.sep_ee = np.array([self.cid[T.pair(e, e)] for d, e in pr])
        self.sep_de = np.array([self.cid[T.pair(d, e)] for d, e in pr])
        self.add_rows([r for r, k in enumerate(rows.keys) if k[0] not in ('win', 'mc')])

    # model edits --------------------------------------------------------------------------------------------
    def _push(self, entries, rl, ru, ents):
        start, idx, val = [], [], []
        for ent in ents:
            start.append(len(idx))
            for c, a in ent.items():
                idx.append(self.cid[c]); val.append(float(a))
        self.h.addRows(len(ents), np.array(rl), np.array(ru), len(idx), np.array(start, dtype=np.int32),
                       np.array(idx, dtype=np.int32), np.array(val))
        self.lp.extend(entries); self.age.extend([0] * len(entries))

    def add_rows(self, rs):
        L, U = self.region
        rs = [r for r in rs if r not in self.inlp]
        if not rs:
            return 0
        rl, ru, ents = [], [], []
        for r in rs:
            lo, up, ent = self.rows.row(r, L, U)
            rl.append(-INF if lo is None else float(lo)); ru.append(INF if up is None else float(up)); ents.append(ent)
            self.inlp[r] = True
        self._push(rs, rl, ru, ents)
        return len(rs)

    def add_cuts(self, keys):
        new, rl, ru, ents = [], [], [], []
        for key in keys:
            sk = repr(key)
            if sk in self.inlp:
                continue
            lo, up, ent = C.square_cut(self.T, key)
            s = max(abs(a) for a in ent.values())
            ents.append({c: a / s for c, a in ent.items()}); rl.append(float(lo / s)); ru.append(INF)
            new.append((key, s)); self.inlp[sk] = True
        if new:
            self._push(new, rl, ru, ents)
        return len(new)

    def drop(self, positions):
        if not positions:
            return
        pos = sorted(set(positions))
        self.h.deleteRows(len(pos), np.array(pos, dtype=np.int32))
        gone = set(pos)
        for p in pos:
            e = self.lp[p]
            del self.inlp[e if isinstance(e, int) else repr(e[0])]
        self.lp = [e for i, e in enumerate(self.lp) if i not in gone]
        self.age = [a for i, a in enumerate(self.age) if i not in gone]

    def set_region(self, region):
        L, U = region
        oL, oU = self.region
        changed = [b for b in range(self.T.nB) if L[b] != oL[b] or U[b] != oU[b]]
        if not changed:
            return
        self.region = (list(L), list(U))
        self.Lf = np.array([float(v) for v in L]); self.Uf = np.array([float(v) for v in U])
        ch = set(changed)
        h = self.h
        for p, e in enumerate(self.lp):
            if isinstance(e, int) and self.rows.keys[e][0] == 'mc' and (self.rows.keys[e][1] in ch or self.rows.keys[e][2] in ch):
                lo, up, ent = self.rows.mc_row(self.rows.keys[e], L, U)
                for c, a in ent.items():
                    h.changeCoeff(p, self.cid[c], float(a))
                h.changeRowBounds(p, -INF, float(up))
        cc = np.array([self.mcol[b] for b in changed], dtype=np.int32)
        h.changeColsBounds(len(cc), cc, np.array([float(L[b]) for b in changed]), np.array([float(U[b]) for b in changed]))

    # solving ------------------------------------------------------------------------------------------------
    def early_stop(self, on):
        """switch the objective-bound early stop on or off (off: solve to optimality)."""
        if self.objbound is not None:
            self.h.setOptionValue('objective_bound', self.objbound if on else INF)

    def solve(self):
        h = self.h
        ok = (highspy.HighsModelStatus.kOptimal, highspy.HighsModelStatus.kObjectiveBound)
        st = robust_run(h, ok, self.pricing)
        if st == highspy.HighsModelStatus.kInfeasible:
            return 'infeasible'
        if st not in ok:
            return None
        sol = h.getSolution()
        return h.getInfo().objective_function_value, np.array(sol.col_value), np.array(sol.row_dual)

    def farkas(self):
        h = self.h
        if h.getModelStatus() != highspy.HighsModelStatus.kInfeasible:
            return None
        out = h.getDualRay()
        if not (isinstance(out, tuple) and len(out) == 3 and out[1]):
            return None
        return np.array(out[2], dtype=float)

    def violated(self, x):
        """lazy rows (window, McCormick) not in the model that x violates by more than tol, most violated first."""
        G = x
        g1 = np.where(self.win_g1 >= 0, G[np.maximum(self.win_g1, 0)], 0.0)
        vw = self.win_w * (G[self.win_g2] - g1) - x[self.tcol]
        LD, UD, LE, UE = self.Lf[self.mc_D], self.Uf[self.mc_D], self.Lf[self.mc_E], self.Uf[self.mc_E]
        z, mD, mE = x[self.mc_z], x[self.mc_mD], x[self.mc_mE]
        q = self.mc_q
        vm = np.where(q == 0, -z + LE * mD + LD * mE - LD * LE,
             np.where(q == 1, -z + UE * mD + UD * mE - UD * UE,
             np.where(q == 2, z - UE * mD - LD * mE + LD * UE, z - LE * mD - UD * mE + UD * LE)))
        cand_r = np.concatenate([self.win_r, self.mc_r]); cand_v = np.concatenate([vw, vm])
        sel = np.nonzero(cand_v > self.tol)[0]
        sel = sel[np.argsort(-cand_v[sel])]
        out = []
        for i in sel:
            r = int(cand_r[i])
            if r not in self.inlp:
                out.append(r)
                if len(out) >= self.add_cap:
                    break
        return out

    def separate(self, x, k=40, tol=1e-7, bits=20):
        M = np.empty((len(self.sep_d), 3, 3))
        M[:, 0, 0] = 1.0
        M[:, 0, 1] = M[:, 1, 0] = x[self.sep_md]
        M[:, 0, 2] = M[:, 2, 0] = x[self.sep_me]
        M[:, 1, 1] = x[self.sep_dd]; M[:, 2, 2] = x[self.sep_ee]
        M[:, 1, 2] = M[:, 2, 1] = x[self.sep_de]
        w, V = np.linalg.eigh(M)
        order = np.argsort(w[:, 0])
        keys = []
        for t in order[:k]:
            if not (w[t, 0] < -tol):
                break
            v = V[t, :, 0]
            v = v / np.max(np.abs(v))
            iv = [int(round(float(c) * (1 << bits))) for c in v]
            if iv[1] == 0 and iv[2] == 0:
                continue
            keys.append(['sq', iv[0], [[int(self.sep_d[t]), iv[1]], [int(self.sep_e[t]), iv[2]]]])
        return keys

    def end_leaf(self, y):
        """age the lazy rows and cuts (reset where the final dual is nonzero) and drop the old ones."""
        drop = []
        for p, e in enumerate(self.lp):
            if isinstance(e, int) and self.rows.keys[e][0] not in ('win', 'mc'):
                continue
            if y is not None and p < len(y) and y[p] != 0.0:
                self.age[p] = 0
            else:
                self.age[p] += 1
                if self.age[p] > self.maxage:
                    drop.append(p)
        self.drop(drop)

    # exact evaluation ---------------------------------------------------------------------------------------
    def duals(self, y, sign=1.0):
        """exact admissible duals from an LP-ordered float vector: ([(row, q)], [((lo, up, ent), q)])."""
        row_duals, cut_duals = [], []
        for p in np.nonzero(y[:len(self.lp)])[0]:
            q = to_dyadic(sign * float(y[p]))
            if not q:
                continue
            e = self.lp[p]
            if isinstance(e, int):
                row_duals.append((e, q))
            else:
                key, s = e
                cut_duals.append((C.square_cut(self.T, key), q / s))
        return row_duals, cut_duals

    def exact_bound(self, region, y):
        rd, cd = self.duals(y)
        return C.ns_bound(self.rows, region, rd, cd)

    def exact_farkas(self, region, ray):
        best = None
        for sg in (1.0, -1.0):
            rd, cd = self.duals(ray, sg)
            v = C.ns_bound(self.rows, region, rd, cd, objective=False)
            best = v if best is None or v > best else best
        return best
