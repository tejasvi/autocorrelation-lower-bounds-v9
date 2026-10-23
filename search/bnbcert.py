"""Certifying branch-and-bound for V_n >= lam (see verify.py for the exact statement).

Usage:
  bnbcert.py init CERTDIR n lam [--depth D]      master phase: DFS to depth D, delegate the rest as jobs
  bnbcert.py work CERTDIR [--workers W] [--max-nodes N]   process queued jobs (file queue, preemption safe)
  bnbcert.py status CERTDIR

The LP rows are built from verify.Spec (one source of truth for the mathematics); the
verifier re-derives everything exactly and trusts nothing logged except as data.
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


def frac_str(x):
    return str(Fr(x))


class Model:
    def __init__(self, n, lam):
        self.n = n; self.lam = lam
        spec = self.spec = Spec(n)
        tree = spec.tree
        nB = spec.nB
        # ---- columns
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
        # ---- rows
        rowkeys = [("win", c1, c2) for c1 in range(2 * n - 1) for c2 in range(c1, 2 * n - 1)]
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
        # ---- root region and matrix
        L0, U0 = spec.root_region()
        rows_lo = np.empty(self.nrow); rows_up = np.empty(self.nrow)
        I, J, V = [], [], []
        for r, key in enumerate(rowkeys):
            lo, up, ent = spec.row(key, L0, U0)
            rows_lo[r] = -highspy.kHighsInf if lo is None else float(lo)
            rows_up[r] = highspy.kHighsInf if up is None else float(up)
            for ck, a in ent.items():
                I.append(r); J.append(self.cix[ck]); V.append(float(a))
        A = sp.csc_matrix((V, (I, J)), shape=(self.nrow, self.ncol))
        A.sort_indices()
        self.row_lo, self.row_up = rows_lo, rows_up
        # fixed part as CSR for float bound checks
        Afix = A[: self.nfixed].tocsr()
        self.AfixT = Afix.T.tocsr()
        # McCormick structure arrays
        self.mc_z = np.array([self.cix[spec.canon_pair(d, e)] for (d, e) in self.pairs])
        self.mc_md = np.array([self.cix[("m", d)] for (d, e) in self.pairs])
        self.mc_me = np.array([self.cix[("m", e)] for (d, e) in self.pairs])
        self.mc_d = np.array([d for (d, e) in self.pairs]); self.mc_e = np.array([e for (d, e) in self.pairs])
        self.mc_diag = self.mc_d == self.mc_e
        self.blockcol = np.array([self.cix[("m", b)] for b in range(nB)])
        self.cost = np.zeros(self.ncol); self.cost[self.cix[("t",)]] = 1.0
        self.tcol = self.cix[("t",)]
        lb = np.zeros(self.ncol); ub = np.ones(self.ncol); ub[self.tcol] = float(TMAX)
        lb[self.blockcol] = [float(x) for x in L0]; ub[self.blockcol] = [float(x) for x in U0]
        self.col_lb, self.col_ub = lb, ub
        h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("threads", 1)
        h.setOptionValue("presolve", "off")
        h.setOptionValue("solver", "simplex")
        h.setOptionValue("simplex_strategy", 1)
        lp = highspy.HighsLp()
        lp.num_col_ = self.ncol; lp.num_row_ = self.nrow
        lp.col_cost_ = self.cost; lp.col_lower_ = lb.copy(); lp.col_upper_ = ub.copy()
        lp.row_lower_ = rows_lo.copy(); lp.row_upper_ = rows_up.copy()
        lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
        lp.a_matrix_.start_ = A.indptr.astype(np.int32)
        lp.a_matrix_.index_ = A.indices.astype(np.int32)
        lp.a_matrix_.value_ = A.data.astype(float)
        h.passModel(lp)
        self.h = h
        self.L = np.array([float(x) for x in L0]); self.U = np.array([float(x) for x in U0])
        self.pair_ids_of_block = [[] for _ in range(nB)]
        for k, (d, e) in enumerate(self.pairs):
            self.pair_ids_of_block[d].append(k)
            if e != d:
                self.pair_ids_of_block[e].append(k)
        self.root_region_float = (self.L.copy(), self.U.copy())

    # ---- McCormick coefficients (float mirror of Spec.row 'mc')
    def mc_coeffs(self, L, U):
        d, e = self.mc_d, self.mc_e
        Ld, Ud, Le, Ue = L[d], U[d], L[e], U[e]
        diag = self.mc_diag
        # coefficient on z, on md, on me, rhs  for q = 0..3  (shape [4, npairs])
        cz = np.array([-1.0, -1.0, 1.0, 1.0])[:, None] * np.ones(len(d))
        cmd = np.stack([Le, Ue, -Ue, -Le]); cme = np.stack([Ld, Ud, -Ld, -Ud])
        rhs = np.stack([Ld * Le, Ud * Ue, -Ld * Ue, -Ud * Le])
        # diagonal pairs: single m column with combined coefficient
        cmd_d = np.stack([2 * Ld, 2 * Ud, -(Ld + Ud), -(Ld + Ud)])
        rhs_d = np.stack([Ld * Ld, Ud * Ud, -Ld * Ud, -Ld * Ud])
        cmd = np.where(diag[None, :], cmd_d, cmd)
        cme = np.where(diag[None, :], 0.0, cme)
        rhs = np.where(diag[None, :], rhs_d, rhs)
        return cz, cmd, cme, rhs

    def set_region(self, L, U):
        L = np.asarray(L, float); U = np.asarray(U, float)
        changed = np.nonzero((L != self.L) | (U != self.U))[0]
        if len(changed) == 0:
            return
        self.L, self.U = L.copy(), U.copy()
        ks = sorted(set(k for b in changed for k in self.pair_ids_of_block[b]))
        cz, cmd, cme, rhs = self.mc_coeffs(L, U)
        h = self.h
        ridx = []; rup = []
        for k in ks:
            r0 = self.nfixed + 4 * k
            md, me = int(self.mc_md[k]), int(self.mc_me[k])
            for q in range(4):
                h.changeCoeff(r0 + q, md, float(cmd[q, k]))
                if not self.mc_diag[k]:
                    h.changeCoeff(r0 + q, me, float(cme[q, k]))
                ridx.append(r0 + q); rup.append(float(rhs[q, k]))
        ridx = np.array(ridx, dtype=np.int32); rup = np.array(rup)
        self.row_up[ridx] = rup
        h.changeRowsBounds(len(ridx), ridx, np.full(len(ridx), -highspy.kHighsInf), rup)
        cols = self.blockcol[changed].astype(np.int32)
        self.col_lb[cols] = L[changed]; self.col_ub[cols] = U[changed]
        h.changeColsBounds(len(cols), cols, L[changed].copy(), U[changed].copy())

    def solve(self):
        h = self.h
        h.run()
        st = h.getModelStatus()
        if st not in (highspy.HighsModelStatus.kOptimal, highspy.HighsModelStatus.kInfeasible):
            h.clearSolver()          # numerical trouble: retry from scratch once
            h.run()
            st = h.getModelStatus()
        if st == highspy.HighsModelStatus.kInfeasible:
            return "infeasible", None, None, None
        if st != highspy.HighsModelStatus.kOptimal:
            return "error", None, None, None
        sol = h.getSolution()
        return "optimal", h.getInfo().objective_function_value, np.array(sol.col_value), np.array(sol.row_dual)

    def float_bound(self, y):
        """Neumaier-Shcherbina bound in floats with the current region (pre-check of the logged dual)."""
        y = y.copy()
        lo, up = self.row_lo, self.row_up
        y[(y > 0) & ~np.isfinite(lo)] = 0.0
        y[(y < 0) & ~np.isfinite(up)] = 0.0
        rowpart = float(np.sum(np.where(y > 0, y * np.where(np.isfinite(lo), lo, 0.0), y * np.where(np.isfinite(up), up, 0.0))))
        r = self.cost - self.AfixT @ y[: self.nfixed]
        cz, cmd, cme, rhs = self.mc_coeffs(self.L, self.U)
        ym = y[self.nfixed:].reshape(-1, 4).T      # [4, npairs]
        np.subtract.at(r, self.mc_z, (cz * ym).sum(0))
        np.subtract.at(r, self.mc_md, (cmd * ym).sum(0))
        np.subtract.at(r, self.mc_me, (cme * ym).sum(0))
        colpart = float(np.sum(np.minimum(r * self.col_lb, r * self.col_ub)))
        return rowpart + colpart, y

    def dual_ray(self):
        h = self.h
        try:
            res = h.getDualRay()
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
    S = np.concatenate([[0.0], np.cumsum(P)])
    c1, c2 = np.triu_indices(2 * n - 1)
    return float((2.0 * n / (c2 - c1 + 2) * (S[c2 + 1] - S[c1])).max())


def choose_branch(model, x, L, U):
    spec = model.spec
    m = x[model.blockcol]
    z = x[model.mc_z]
    gap = np.abs(z - m[model.mc_d] * m[model.mc_e])
    score = np.zeros(spec.nB)
    np.add.at(score, model.mc_d, gap); np.add.at(score, model.mc_e, gap * (~model.mc_diag))
    width = np.asarray(U) - np.asarray(L)
    score[width < 8.0 / SCALE] = -1.0
    b = int(np.argmax(score))
    if score[b] <= 0:
        b = int(np.argmax(width))
    lo, hi = L[b] + 0.25 * width[b], U[b] - 0.25 * width[b]
    s = min(max(m[b], lo), hi)
    s = round(s * SCALE) / SCALE
    if not (L[b] < s < U[b]):
        s = round(0.5 * (L[b] + U[b]) * SCALE) / SCALE
    assert L[b] < s < U[b]
    return b, s


class Interrupted(Exception):
    pass


def process_subtree(model, region, path, out, lam, max_nodes, stop_flag=None, depth_limit=None):
    """DFS from region. Writes records to out (list of json-able). Returns (stats, delegated list of (path, region))."""
    spec = model.spec
    stack = [(region, path)]
    stats = {"nodes": 0, "leaves": 0, "farkas": 0, "empty": 0, "minlb": float("inf")}
    delegated = []
    while stack:
        if stop_flag is not None and stop_flag():
            raise Interrupted()
        reg, pth = stack.pop()
        if (max_nodes is not None and stats["nodes"] >= max_nodes) or (depth_limit is not None and len(pth) >= depth_limit):
            out.append(["S"]); delegated.append((pth, reg)); continue
        stats["nodes"] += 1
        model.set_region(reg[0], reg[1])
        st, obj, x, y = model.solve()
        if st == "infeasible":
            ray = model.dual_ray()
            if ray is not None:
                nz = np.nonzero(np.abs(ray) > 0)[0]
                out.append(["F", nz.tolist(), [float(v) for v in ray[nz]]])
                stats["farkas"] += 1
                continue
            st = "error"             # no ray available: fall through to the midpoint split below
        if st != "optimal":
            # LP failed even after a cold retry: split the widest block at its midpoint (no certificate needed)
            stats["lperr"] = stats.get("lperr", 0) + 1
            width = np.asarray(reg[1]) - np.asarray(reg[0])
            b = int(np.argmax(width))
            s = round(0.5 * (reg[0][b] + reg[1][b]) * SCALE) / SCALE
            if not (reg[0][b] < s < reg[1][b]):
                raise RuntimeError("LP failure on a region too small to split at " + str(pth))
            out.append(["I", b, frac_str(s)])
            for side in (0, 1):
                c = child_float(spec, reg, b, s, side)
                if c is None:
                    stats["empty"] += 1
                else:
                    stack.append((c, pth + [(b, s, side)]))
            continue
        if obj >= lam + 1e-7:
            yy = np.where(np.abs(y) > 1e-14, y, 0.0)
            lb, yy = model.float_bound(yy)
            if lb >= lam + LB_MARGIN:
                nz = np.nonzero(yy)[0]
                out.append(["L", lb, nz.tolist(), [float(v) for v in yy[nz]]])
                stats["leaves"] += 1; stats["minlb"] = min(stats["minlb"], lb)
                continue
        p = np.maximum(x[: model.n], 0)
        if p.sum() > 0 and F_value(p / p.sum()) < lam:
            raise RuntimeError(f"COUNTEREXAMPLE F={F_value(p/p.sum())} p={p.tolist()}")
        b, s = choose_branch(model, x, reg[0], reg[1])
        out.append(["I", b, frac_str(s)])
        for side in (0, 1):
            c = child_float(spec, reg, b, s, side)
            if c is None:
                stats["empty"] += 1
            else:
                stack.append((c, pth + [(b, s, side)]))
    return stats, delegated


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


def cmd_init(certdir, n, lam_str, depth):
    lam = Fr(lam_str)
    for d in ("jobs", "todo", "running", "done"):
        os.makedirs(os.path.join(certdir, d), exist_ok=True)
    model = Model(n, float(lam))
    meta = {"n": n, "lam": str(lam), "rowkeys": model.rowkeys, "colkeys": model.colkeys,
            "splitbits": SPLITBITS, "created": time.strftime("%Y-%m-%d %H:%M:%S")}
    with open(os.path.join(certdir, "meta.json"), "w") as fh:
        json.dump(meta, fh)
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
    model = Model(n, float(lam))
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
    minlb = float("inf")
    for f in glob.glob(os.path.join(certdir, "jobs", "*.jsonl.gz")):
        with gzip.open(f, "rt") as fh:
            h = json.loads(fh.readline())
        st = h.get("stats")
        if st:
            for k in tot:
                tot[k] += st[k]
            minlb = min(minlb, st["minlb"])
    print(f"todo={nt} running={nr} done={nd} totals={tot} minlb={minlb}")


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "init":
        import argparse
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir"); ap.add_argument("n", type=int)
        ap.add_argument("lam"); ap.add_argument("--depth", type=int, default=10)
        a = ap.parse_args(); cmd_init(a.certdir, a.n, a.lam, a.depth)
    elif cmd == "work":
        import argparse
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir")
        ap.add_argument("--workers", type=int, default=1); ap.add_argument("--max-nodes", type=int, default=20000)
        a = ap.parse_args(); cmd_work(a.certdir, a.workers, a.max_nodes)
    elif cmd == "recover":
        cmd_recover(sys.argv[2])
    elif cmd == "status":
        cmd_status(sys.argv[2])
