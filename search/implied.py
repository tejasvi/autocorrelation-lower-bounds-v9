"""Certificate compression analysis: implied duals for the auxiliary equality rows.

For each leaf of a certificate, drop the duals of the P, G and ZA rows and reconstruct them the way a
decompressing verifier would (making the reduced costs of the P, G and ZA columns zero, by triangular
back-substitution: G from c = 2n-2 down, P_c = G_c, ZA pairs in topological order parents-first).
Report how many leaves keep LB >= lam (float NS bound, screening) and the number of stored dual entries.
Usage: implied.py CERTDIR [--max-jobs K] [--fixed F]   (F: also round stored duals to multiples of 2^-F)
"""
import sys, os, json, gzip, glob
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bnbopt as B


def sq_float(model, key):
    v0 = key[1]; terms = [(b, v) for b, v in key[2] if v != 0]
    ent = {}
    for a in range(len(terms)):
        ba, va = terms[a]
        k = model.cix[model.spec.canon_pair(ba, ba)]; ent[k] = ent.get(k, 0.0) + float(va * va)
        if v0:
            k = model.cix[("m", ba)]; ent[k] = ent.get(k, 0.0) + float(2 * v0 * va)
        for c in range(a + 1, len(terms)):
            bc, vc = terms[c]
            k = model.cix[model.spec.canon_pair(ba, bc)]; ent[k] = ent.get(k, 0.0) + float(2 * va * vc)
    return np.array(list(ent.keys())), np.array(list(ent.values())), -float(v0 * v0)


class Implied:
    def __init__(self, model):
        self.m = m = model
        rk = m.rowkeys
        self.kind = np.array([k[0] for k in rk])
        self.rix = {k: i for i, k in enumerate(rk)}
        n = m.n
        self.grow = np.array([self.rix[("G", c)] for c in range(2 * n - 1)])
        self.prow = np.array([self.rix[("P", c)] for c in range(2 * n - 1)])
        self.gcol = np.array([m.cix[("G", c)] for c in range(2 * n - 1)])
        # ZA rows: own column and the ZA columns appearing in it (children terms)
        za_rows = [i for i, k in enumerate(rk) if k[0] == "ZA"]
        self.za_rows = za_rows
        self.za_own = {}
        parents_of = {}
        A = m.A
        for r in za_rows:
            d, e, s = rk[r][1], rk[r][2], rk[r][3]
            own = m.cix[m.spec.canon_pair(d, e)]
            self.za_own[r] = own
        own_to_row = {c: r for r, c in self.za_own.items()}
        self.own_to_row = own_to_row
        for r in za_rows:
            a, b = A.indptr[r], A.indptr[r + 1]
            for c, v in zip(A.indices[a:b], A.data[a:b]):
                if c != self.za_own[r] and c in own_to_row:
                    parents_of.setdefault(c, []).append((r, v))     # column c appears in parent row r with coef v
        self.parents_of = parents_of
        # topological order: a ZA row after all rows in which its own column appears
        order = []; seen = set()
        def visit(r):
            if r in seen:
                return
            seen.add(r)
            for (pr, v) in parents_of.get(self.za_own[r], []):
                visit(pr)
            order.append(r)
        for r in za_rows:
            visit(r)
        self.order = order
        # sparse triangular system (I + T) y_za = -contrib_own in topological order (T strictly lower)
        import scipy.sparse as sp
        pos = {r: i for i, r in enumerate(order)}
        I, J, V = [], [], []
        for r in order:
            for (pr, v) in parents_of.get(self.za_own[r], []):
                I.append(pos[r]); J.append(pos[pr]); V.append(v)
        nza = len(order)
        self.Tmat = (sp.identity(nza, format="csr") + sp.csr_matrix((V, (I, J)), shape=(nza, nza))).tocsr()
        self.order_arr = np.array(order, dtype=np.int64)
        self.own_arr = np.array([self.za_own[r] for r in order], dtype=np.int64)
        # window -> G column contributions as a sparse matrix (nwin x (2n-1))
        wi, wj, wv = [], [], []
        for k in range(m.nwin):
            c1, c2, w = m.w_c1[k], m.w_c2[k], m.w_w[k]
            wi.append(k); wj.append(c2); wv.append(w)
            if c1 > 0:
                wi.append(k); wj.append(c1 - 1); wv.append(-w)
        self.Wg = sp.csr_matrix((wv, (wi, wj)), shape=(m.nwin, 2 * n - 1)).T.tocsr()

    def reconstruct(self, y, L, U, extra_rows):
        """y: full dual (universe incl. mc rows), P/G/ZA entries are overwritten.  extra_rows: list of (cols, vals, dual)."""
        m = self.m; n = m.n
        y = y.copy()
        y[self.grow] = 0.0; y[self.prow] = 0.0; y[self.za_rows] = 0.0
        # contribution of window rows to G columns; yg[c] = -sum_{c' >= c} wcontrib[c']
        wcontrib = self.Wg @ y[: m.nwin]
        yg = -np.cumsum(wcontrib[::-1])[::-1]
        y[self.grow] = yg
        y[self.prow] = yg
        # mc + cut contributions to ZA columns
        cz, cmd, cme, rhs = m.mc_coeffs(np.asarray(L, float), np.asarray(U, float))
        contrib = np.zeros(m.ncol)
        ym = y[m.nfixed:m.nrow].reshape(-1, 4).T
        np.add.at(contrib, m.mc_z, (cz * ym).sum(0))
        for cols, vals, dv in extra_rows:
            np.add.at(contrib, cols, dv * vals)
        from scipy.sparse.linalg import spsolve_triangular
        y[self.order_arr] = spsolve_triangular(self.Tmat, -contrib[self.own_arr], lower=True)
        return y


def leaves(certdir, model, max_jobs=None):
    files = sorted(glob.glob(os.path.join(certdir, "jobs", "*.jsonl.gz")))
    if max_jobs:
        files = files[:max_jobs]
    for f in files:
        with gzip.open(f, "rt") as fh:
            h = json.loads(fh.readline())
            reg = (list(model.root_region_float[0]), list(model.root_region_float[1]))
            for b, s, side in h["path"]:
                reg = B.child_float(model.spec, reg, int(b), float(Fr(s)), int(side))
            stack = [reg]
            for line in fh:
                rec = json.loads(line)
                reg = stack.pop()
                if rec[0] == "I":
                    b, s = rec[1], float(Fr(rec[2]))
                    for side in (0, 1):
                        c = B.child_float(model.spec, reg, b, s, side)
                        if c is not None:
                            stack.append(c)
                elif rec[0] == "L":
                    yield reg, rec


def main():
    certdir = sys.argv[1]
    max_jobs = int(sys.argv[sys.argv.index("--max-jobs") + 1]) if "--max-jobs" in sys.argv else None
    meta = json.load(open(os.path.join(certdir, "meta.json")))
    n = meta["n"]; lam = float(Fr(meta["lam"]))
    model = B.OptModel(n, lam, {"lazy_win": False, "lazy_mc": False})
    imp = Implied(model)
    kinds = imp.kind
    N = 0; ok = 0; nnz_full = 0; nnz_cmp = 0; by = {}
    worst = 9.0
    for reg, rec in leaves(certdir, model, max_jobs):
        y = np.zeros(model.cap)
        idx = np.array(rec[2], dtype=np.int64); y[idx] = rec[3]
        extra = []
        if len(rec) == 5:
            for key, dv in rec[4]:
                cols, vals, lo = sq_float(model, key)
                extra.append((cols, vals, dv, lo))
        for k in set(kinds[idx]):
            by[k] = by.get(k, 0) + int((kinds[idx] == k).sum())
        yr = imp.reconstruct(y, reg[0], reg[1], [(c, v, d) for c, v, d, lo in extra])
        # float NS bound including the extra rows
        lb, r = model.ns_bound(yr, reg[0], reg[1])
        if extra:
            # ns_bound does not know these ad-hoc rows: add their contribution
            rr = r.copy(); rowp = 0.0
            for cols, vals, dv, lo in extra:
                np.subtract.at(rr, cols, dv * vals); rowp += dv * lo
            clb = model.col_lb.copy(); cub = model.col_ub.copy()
            clb[model.blockcol] = reg[0]; cub[model.blockcol] = reg[1]
            lb = lb - float(np.sum(np.minimum(r * clb, r * cub))) + float(np.sum(np.minimum(rr * clb, rr * cub))) + rowp
        N += 1; ok += lb >= lam; worst = min(worst, lb)
        keep = ~np.isin(kinds[idx], ["P", "G", "ZA"])
        nnz_full += len(idx); nnz_cmp += int(keep.sum())
    print(f"{certdir}: leaves {N}; implied-dual reconstruction keeps LB>=lam on {ok} ({100*ok/max(1,N):.2f}%); min LB {worst:.9f}")
    print(f"  stored dual entries per leaf: full {nnz_full/N:.1f} -> compressed {nnz_cmp/N:.1f}")
    print("  entries per leaf by row kind:", {k: round(v / N, 1) for k, v in sorted(by.items())})


if __name__ == "__main__":
    main()
