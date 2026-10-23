"""Independent exact verifier for the branch-and-bound certificate of V_n >= lam.

Mathematical claim verified:  for every p in Delta_n with sum_i (2i-(n-1)) p_i <= 0,
    F(p) = max_{0<=c1<=c2<=2n-2}  2n/(c2-c1+2) * sum_{c1<=i+j<=c2} p_i p_j   >=  lam.
(The reversal p_i -> p_{n-1-i} preserves F, so this covers all of Delta_n.)

Nothing from the solver is trusted except as data.  The verifier
  * builds the block tree, the column meaning and every LP row from semantic keys,
    with exact rational coefficients computed here;
  * recomputes every node region exactly (Fractions) from the logged split decisions,
    with its own interval propagation (sum rules on the tree, root mass = 1);
  * for each leaf, evaluates the Neumaier-Shcherbina bound
        LB(y) = sum_r (y_r>=0 ? y_r lo_r : y_r up_r) + sum_c min(r_c lb_c, r_c ub_c),  r = e_t - A^T y
    exactly, where y is the logged dual (any vector is admissible; wrong signs on
    one-sided rows are zeroed), and checks LB >= lam;
  * checks that empty children are empty (exact propagation) and that the job tree is
    a partition (every delegated subtree has exactly one job, no job is orphaned).

Validity of each row for the "true point" of any p in a region (with Z_ij = p_i p_j,
ZA_DE = m_D m_E, m_B = sum_{i in B} p_i, P_c = sum_{i+j=c} p_i p_j (ordered pairs),
G_c = P_0+...+P_c, t = F(p)):
  win:  w (G_c2 - G_{c1-1}) - t <= 0      since t is the max over windows
  P,G,tree,ZA rows: algebraic identities of the true point
  rlt:  sum_j Z_ij - p_i = 0             since sum_j p_j = 1
  sym:  sum (2i-(n-1)) p_i <= 0           half-space hypothesis
  mc:   McCormick inequalities, valid since L_D <= m_D <= U_D and L_E <= m_E <= U_E
Column bounds: m_B in [L_B,U_B]; Z, ZA, P, G in [0,1]; t in [0,3].  If F(p) < lam <= 3 the true
point is feasible with t = F(p), hence LB <= LP value <= F(p) < lam.  So LB >= lam excludes all p.
"""
import sys, os, json, gzip, glob, time
from fractions import Fraction as Fr

TMAX = Fr(3)


class Spec:
    def __init__(self, n):
        self.n = n
        tree = []

        def build(lo, hi, parent):
            idx = len(tree)
            tree.append([lo, hi, parent, -1, -1])
            if hi - lo > 1:
                mid = (lo + hi) // 2
                a = build(lo, mid, idx); b = build(mid, hi, idx)
                tree[idx][3], tree[idx][4] = a, b
            return idx
        build(0, n, -1)
        self.tree = tree
        self.nB = len(tree)
        self.leaf = [t[1] - t[0] == 1 for t in tree]
        self.bin_of_leaf = {b: tree[b][0] for b in range(self.nB) if self.leaf[b]}
        self.leaf_of_bin = {v: k for k, v in self.bin_of_leaf.items()}

    # ---- column semantics -------------------------------------------------
    def col_bounds(self, key, L, U):
        kind = key[0]
        if kind == "m":
            b = key[1]
            return L[b], U[b]
        if kind in ("Z", "ZA", "P", "G"):
            return Fr(0), Fr(1)
        if kind == "t":
            return Fr(0), TMAX
        raise ValueError(key)

    def canon_pair(self, d, e):
        """Column key of the product m_d m_e (leaf-leaf products are Z_ij)."""
        if d > e:
            d, e = e, d
        if self.leaf[d] and self.leaf[e]:
            i, j = sorted((self.bin_of_leaf[d], self.bin_of_leaf[e]))
            return ("Z", i, j)
        return ("ZA", d, e)

    def mcol(self, b):
        return ("m", b)

    # ---- strict validation of untrusted row keys (no reliance on assert)
    def validate_key(self, key):
        def isint(v):
            return type(v) is int
        n, nB, tree = self.n, self.nB, self.tree
        if not isinstance(key, tuple) or len(key) == 0 or not isinstance(key[0], str):
            raise ValueError(f"malformed row key {key!r}")
        kind, args = key[0], key[1:]
        if not all(isint(a) for a in args):
            raise ValueError(f"non-integer index in row key {key!r}")
        if kind == "win":
            if len(args) != 2 or not (0 <= args[0] <= args[1] <= 2 * n - 2):
                raise ValueError(f"bad window key {key!r}")
        elif kind in ("P", "G"):
            if len(args) != 1 or not (0 <= args[0] <= 2 * n - 2):
                raise ValueError(f"bad band key {key!r}")
        elif kind == "tree":
            if len(args) != 1 or not (0 <= args[0] < nB) or self.leaf[args[0]]:
                raise ValueError(f"bad tree key {key!r}")
        elif kind == "ZA":
            if len(args) != 3:
                raise ValueError(f"bad ZA key {key!r}")
            d, e, s_ = args
            if not (0 <= d < nB and 0 <= e < nB and 0 <= s_ < nB) or s_ not in (d, e) or self.leaf[s_]:
                raise ValueError(f"bad ZA key {key!r}")
        elif kind == "rlt":
            if len(args) != 1 or not (0 <= args[0] < n):
                raise ValueError(f"bad rlt key {key!r}")
        elif kind == "sym":
            if len(args) != 0:
                raise ValueError(f"bad sym key {key!r}")
        elif kind == "mc":
            if len(args) != 3:
                raise ValueError(f"bad mc key {key!r}")
            d, e, q = args
            if not (0 <= d < nB and 0 <= e < nB and 0 <= q <= 3):
                raise ValueError(f"bad mc key {key!r}")
        else:
            raise ValueError(f"unknown row kind {key!r}")
        return key

    # ---- row semantics: returns (lo, up, {colkey: coef}) with exact Fractions; None = infinite
    def row(self, key, L, U):
        self.validate_key(key)
        n, tree = self.n, self.tree
        kind = key[0]
        if kind == "win":
            c1, c2 = key[1], key[2]
            w = Fr(2 * n, c2 - c1 + 2)
            ent = {("G", c2): w, ("t",): Fr(-1)}
            if c1 > 0:
                ent[("G", c1 - 1)] = ent.get(("G", c1 - 1), 0) - w
            return None, Fr(0), ent
        if kind == "P":
            c = key[1]
            ent = {("P", c): Fr(1)}
            for i in range(n):
                j = c - i
                if i <= j < n:
                    ent[("Z", i, j)] = Fr(-1 if i == j else -2)
            return Fr(0), Fr(0), ent
        if kind == "G":
            c = key[1]
            ent = {("G", c): Fr(1), ("P", c): Fr(-1)}
            if c > 0:
                ent[("G", c - 1)] = Fr(-1)
            return Fr(0), Fr(0), ent
        if kind == "tree":
            b = key[1]
            c1, c2 = tree[b][3], tree[b][4]
            if c1 < 0:
                raise ValueError(f"tree row on a leaf block {key!r}")
            return Fr(0), Fr(0), {self.mcol(b): Fr(1), self.mcol(c1): Fr(-1), self.mcol(c2): Fr(-1)}
        if kind == "ZA":
            # ZA_{de} = sum of the products obtained by splitting one non-leaf block s in {d,e} into children
            d, e, s = key[1], key[2], key[3]
            if s not in (d, e) or self.leaf[s]:
                raise ValueError(f"bad ZA split {key!r}")
            o = e if s == d else d
            s1, s2 = tree[s][3], tree[s][4]
            ent = {}
            target = self.canon_pair(d, e)
            ent[target] = Fr(1)
            if d == e:
                terms = [(s1, s1, 1), (s1, s2, 2), (s2, s2, 1)]
            else:
                terms = [(s1, o, 1), (s2, o, 1)]
            for (x, y, cf) in terms:
                k = self.canon_pair(x, y)
                ent[k] = ent.get(k, 0) - cf
            return Fr(0), Fr(0), ent
        if kind == "rlt":
            i = key[1]
            ent = {}
            for j in range(n):
                k = ("Z", min(i, j), max(i, j))
                ent[k] = ent.get(k, 0) + 1
            k = self.mcol(self.leaf_of_bin[i])
            ent[k] = ent.get(k, 0) - 1
            return Fr(0), Fr(0), ent
        if kind == "sym":
            ent = {self.mcol(self.leaf_of_bin[i]): Fr(2 * i - (n - 1)) for i in range(n) if 2 * i - (n - 1) != 0}
            return None, Fr(0), ent
        if kind == "mc":
            d, e, q = key[1], key[2], key[3]
            z = self.canon_pair(d, e); md = self.mcol(d); me = self.mcol(e)
            Ld, Ud, Le, Ue = L[d], U[d], L[e], U[e]
            if d == e:
                if q == 0:
                    return None, Ld * Ld, {z: Fr(-1), md: 2 * Ld}
                if q == 1:
                    return None, Ud * Ud, {z: Fr(-1), md: 2 * Ud}
                if q in (2, 3):
                    return None, -Ld * Ud, {z: Fr(1), md: -(Ld + Ud)}
            else:
                if q == 0:   # (m_d - L_d)(m_e - L_e) >= 0
                    return None, Ld * Le, {z: Fr(-1), md: Le, me: Ld}
                if q == 1:   # (U_d - m_d)(U_e - m_e) >= 0
                    return None, Ud * Ue, {z: Fr(-1), md: Ue, me: Ud}
                if q == 2:   # (m_d - L_d)(U_e - m_e) >= 0
                    return None, -Ld * Ue, {z: Fr(1), md: -Ue, me: -Ld}
                if q == 3:   # (U_d - m_d)(m_e - L_e) >= 0
                    return None, -Ud * Le, {z: Fr(1), md: -Le, me: -Ud}
        raise ValueError(key)

    # ---- exact propagation ------------------------------------------------
    def propagate(self, L, U):
        L = list(L); U = list(U); tree = self.tree
        L[0] = max(L[0], Fr(1)); U[0] = min(U[0], Fr(1))
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
        else:
            raise RuntimeError("propagation did not converge")
        if any(L[b] > U[b] for b in range(self.nB)):
            return None
        return L, U

    def root_region(self):
        r = self.propagate([Fr(0)] * self.nB, [Fr(1)] * self.nB)
        if r is None:
            raise RuntimeError("root region empty")
        return r

    def child(self, region, b, s, side):
        L, U = list(region[0]), list(region[1])
        if not (L[b] < s < U[b]):
            raise ValueError(f"split {s} not interior to [{L[b]}, {U[b]}] of block {b}")
        if side == 0:
            U[b] = s
        else:
            L[b] = s
        return self.propagate(L, U)


def leaf_bound(spec, region, rowkeys, colkeys, idx, vals):
    """Exact Neumaier-Shcherbina bound for dual y (sparse: rows idx with values vals)."""
    L, U = region
    r = {}            # reduced cost r = e_t - A^T y, only nonzero entries kept
    rowpart = Fr(0)
    for k, v in zip(idx, vals):
        y = Fr(v)
        if y == 0:
            continue
        lo, up, ent = spec.row(tuple(rowkeys[k]), L, U)
        if y > 0:
            if lo is None:
                continue          # inadmissible sign: drop (same as y_r = 0)
            rowpart += y * lo
        else:
            if up is None:
                continue
            rowpart += y * up
        for ck, a in ent.items():
            r[ck] = r.get(ck, 0) - a * y
    r[("t",)] = r.get(("t",), 0) + 1
    colpart = Fr(0)
    for ck, rc in r.items():
        if rc == 0:
            continue
        lb, ub = spec.col_bounds(ck, L, U)
        colpart += min(rc * lb, rc * ub)
    return rowpart + colpart


def farkas_ok(spec, region, rowkeys, idx, vals):
    """Infeasibility certificate: LB with zero objective > 0."""
    L, U = region
    r = {}; rowpart = Fr(0)
    for k, v in zip(idx, vals):
        y = Fr(v)
        if y == 0:
            continue
        lo, up, ent = spec.row(tuple(rowkeys[k]), L, U)
        if y > 0:
            if lo is None:
                continue
            rowpart += y * lo
        else:
            if up is None:
                continue
            rowpart += y * up
        for ck, a in ent.items():
            r[ck] = r.get(ck, 0) - a * y
    colpart = Fr(0)
    for ck, rc in r.items():
        if rc == 0:
            continue
        lb, ub = spec.col_bounds(ck, L, U)
        colpart += min(rc * lb, rc * ub)
    return rowpart + colpart > 0


def parse_frac(s):
    if isinstance(s, str) or type(s) in (int, float):
        return Fr(s)          # raises on nan/inf
    raise ValueError(f"bad number {s!r}")


def verify_job(path_file, spec, lam, rowkeys, colkeys, verbose=False):
    """Verify one job log. Returns (stats, delegated_paths, root_path)."""
    op = gzip.open if path_file.endswith(".gz") else open
    with op(path_file, "rt") as fh:
        header = json.loads(fh.readline())
        if header.get("n") != spec.n or Fr(header.get("lam")) != lam:
            raise ValueError(f"job header n/lam mismatch in {path_file}")
        root_path = []
        for b, s, side in header["path"]:
            if type(b) is not int or type(side) is not int or side not in (0, 1) or not (0 <= b < spec.nB):
                raise ValueError(f"bad path entry in {path_file}")
            root_path.append((b, parse_frac(s), side))
        region = spec.root_region()
        for (b, s, side) in root_path:
            region = spec.child(region, b, s, side)
            if region is None:
                raise AssertionError("job root region is empty")
        stack = [(region, root_path)]
        stats = {"leaves": 0, "internal": 0, "empty": 0, "farkas": 0, "delegated": 0, "minlb": None}
        delegated = []
        for line in fh:
            rec = json.loads(line)
            if not stack:
                raise AssertionError("more records than nodes")
            reg, path = stack.pop()
            kind = rec[0]
            if kind == "I":
                if len(rec) != 3 or type(rec[1]) is not int or not (0 <= rec[1] < spec.nB):
                    raise ValueError(f"bad I record {rec!r}")
                b, s = rec[1], parse_frac(rec[2])
                stats["internal"] += 1
                for side in (0, 1):     # push child0 then child1 (child1 processed first)
                    cr = spec.child(reg, b, s, side)
                    if cr is None:
                        stats["empty"] += 1
                    else:
                        stack.append((cr, path + [(b, s, side)]))
            elif kind == "L":
                if len(rec) != 4 or len(rec[2]) != len(rec[3]) or any(type(k) is not int or not (0 <= k < len(rowkeys)) for k in rec[2]):
                    raise ValueError("bad L record")
                lb = leaf_bound(spec, reg, rowkeys, colkeys, rec[2], rec[3])
                if lb < lam:
                    raise AssertionError(f"leaf bound {float(lb)} < lam at path {path}")
                stats["leaves"] += 1
                stats["minlb"] = lb if stats["minlb"] is None else min(stats["minlb"], lb)
            elif kind == "F":
                if len(rec) != 3 or len(rec[1]) != len(rec[2]) or any(type(k) is not int or not (0 <= k < len(rowkeys)) for k in rec[1]):
                    raise ValueError("bad F record")
                if not farkas_ok(spec, reg, rowkeys, rec[1], rec[2]):
                    raise AssertionError(f"Farkas certificate fails at path {path}")
                stats["farkas"] += 1
            elif kind == "S":
                stats["delegated"] += 1
                delegated.append(path)
            else:
                raise AssertionError(f"unknown record {kind}")
        if stack:
            raise AssertionError(f"{len(stack)} nodes left without records")
    return stats, delegated, root_path


def path_key(path):
    return tuple((b, str(s), side) for b, s, side in path)


def check_partition(job_records):
    """job_records: list of (name, root_key, delegated_keys). Global partition + reachability checks."""
    roots = {}
    delegated = []
    for name, rk, dl in job_records:
        if rk in roots:
            raise AssertionError(f"two jobs with the same root path: {roots[rk]} and {name}")
        roots[rk] = name
        delegated.extend(dl)
    expected = [()] + delegated
    if len(expected) != len(set(expected)):
        raise AssertionError("a subtree was delegated twice")
    if set(expected) != set(roots.keys()):
        missing = set(expected) - set(roots.keys()); extra = set(roots.keys()) - set(expected)
        raise AssertionError(f"job tree mismatch: missing {len(missing)}, orphan {len(extra)}")
    deleg_by_root = {rk: dl for name, rk, dl in job_records}
    seen = set(); todo = [()]
    while todo:
        k = todo.pop()
        if k in seen:
            raise AssertionError("cycle in job delegation graph")
        seen.add(k)
        todo.extend(deleg_by_root[k])
    if seen != set(roots.keys()):
        raise AssertionError(f"{len(set(roots.keys()) - seen)} jobs unreachable from the root")


def load_meta(certdir, args):
    meta = json.load(open(os.path.join(certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    if type(n) is not int or n < 2:
        sys.exit("bad n")
    if not (0 < lam <= TMAX):
        sys.exit("lam must satisfy 0 < lam <= 3 (column bound of t)")
    if args.expect_n is not None and args.expect_n != n:
        sys.exit(f"certificate is for n={n}, expected {args.expect_n}")
    if args.expect_lam is not None and Fr(args.expect_lam) != lam:
        sys.exit(f"certificate is for lam={lam}, expected {args.expect_lam}")
    spec = Spec(n)
    rowkeys = [spec.validate_key(tuple(k)) for k in meta["rowkeys"]]
    return meta, n, lam, spec, rowkeys


def key_to_json(k):
    return [[b, s, side] for (b, s, side) in k]


def key_from_json(j):
    return tuple((int(b), str(s), int(side)) for b, s, side in j)


def main():
    import argparse, hashlib
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir", nargs="?")
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--expect-n", type=int, default=None)
    ap.add_argument("--expect-lam", type=str, default=None)
    ap.add_argument("--summary", type=str, default=None, help="verify all job logs here; write per-job summaries (no global check)")
    ap.add_argument("--combine", nargs="*", default=None, help="summary files to combine for the global partition check")
    args = ap.parse_args()
    if not __debug__:
        sys.exit("refusing to run with assertions disabled (python -O / PYTHONOPTIMIZE)")
    if args.combine is not None:
        if args.certdir is None:
            sys.exit("give the certdir holding meta.json")
        meta, n, lam, spec, rowkeys = load_meta(args.certdir, args)
        mh = hashlib.sha256(open(os.path.join(args.certdir, "meta.json"), "rb").read()).hexdigest()
        recs = []; tot = {"leaves": 0, "internal": 0, "empty": 0, "farkas": 0, "delegated": 0}; minlb = None
        for sf in args.combine:
            with open(sf) as fh:
                head = json.loads(fh.readline())
                if head.get("meta_sha256") != mh or head.get("verifier_sha256") != hashlib.sha256(open(__file__, "rb").read()).hexdigest():
                    raise AssertionError(f"summary {sf} was made for a different meta.json or verifier")
                if head.get("n") != n or Fr(head.get("lam")) != lam:
                    raise AssertionError(f"summary {sf}: n/lam mismatch")
                for line in fh:
                    r = json.loads(line)
                    recs.append((r["file"], key_from_json(r["root"]), [key_from_json(d) for d in r["delegated"]]))
                    for key in tot:
                        tot[key] += r["stats"][key]
                    if r["stats"]["minlb"] is not None:
                        v = Fr(r["stats"]["minlb"])
                        minlb = v if minlb is None else min(minlb, v)
        check_partition(recs)
        print(f"VERIFIED: V_{n} >= {lam} = {float(lam)}; jobs={len(recs)}; {tot}; min leaf bound {float(minlb) if minlb is not None else None}")
        sys.exit(0)
    meta, n, lam, spec, rowkeys = load_meta(args.certdir, args)
    colkeys = None
    files = sorted(glob.glob(os.path.join(args.certdir, "jobs", "*.jsonl.gz")))
    print(f"n={n} lam={lam} ({float(lam)}) jobs={len(files)}", flush=True)
    t0 = time.time()
    if args.workers > 1:
        import multiprocessing as mp
        ctx = mp.get_context("fork")
        with ctx.Pool(args.workers) as pool:
            results = pool.starmap(verify_job, [(f, spec, lam, rowkeys, colkeys) for f in files], chunksize=8)
    else:
        results = [verify_job(f, spec, lam, rowkeys, colkeys) for f in files]
    if args.summary is not None:
        mh = hashlib.sha256(open(os.path.join(args.certdir, "meta.json"), "rb").read()).hexdigest()
        vh = hashlib.sha256(open(__file__, "rb").read()).hexdigest()
        tmp = args.summary + ".tmp"
        with open(tmp, "w") as out:
            out.write(json.dumps({"n": n, "lam": str(lam), "meta_sha256": mh, "verifier_sha256": vh, "jobs": len(files)}) + "\n")
            for f, (st, dl, rp) in zip(files, results):
                st2 = dict(st); st2["minlb"] = None if st["minlb"] is None else str(st["minlb"])
                out.write(json.dumps({"file": os.path.basename(f), "root": key_to_json(path_key(rp)),
                                      "delegated": [key_to_json(path_key(p)) for p in dl], "stats": st2}) + "\n")
        os.replace(tmp, args.summary)
        print(f"SUMMARY written: {len(files)} jobs verified locally in {time.time()-t0:.1f}s -> {args.summary}")
        sys.exit(0)
    recs = []; tot = {"leaves": 0, "internal": 0, "empty": 0, "farkas": 0, "delegated": 0}; minlb = None
    for f, (st, dl, rp) in zip(files, results):
        recs.append((f, path_key(rp), [path_key(p) for p in dl]))
        for key in tot:
            tot[key] += st[key]
        if st["minlb"] is not None:
            minlb = st["minlb"] if minlb is None else min(minlb, st["minlb"])
    check_partition(recs)
    print(f"VERIFIED: V_{n} >= {lam} = {float(lam)}; {tot}; min leaf bound {float(minlb) if minlb is not None else None}; {time.time()-t0:.1f}s")
    sys.exit(0)


if __name__ == "__main__":
    main()
