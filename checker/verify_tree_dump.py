"""Independent exact verifier for the branch-and-bound certificate of V_n >= lam.

[verify_tree_dump.py = verify_tree.py (frozen copy verify_tree_bae09172.py) + one extra OUTPUT, for the Lean check:
 with VT_DUMP_DIR set, every job is also written to VT_DUMP_DIR/<job file> with each accepted U or T leaf replaced by
 an explicit leaf ["L", lb, idx, vals, cutsA] that carries the dual the exact check accepted (row duals rounded to
 multiples of 2^-64 exactly as IntBound does, written as binary64, which they are exactly; cut duals floored to
 multiples of 2^-128 as IntBound does, written as exact fractions; leaves certified by the exact-path oracle (T leaves,
 hint retries) keep their binary64 row duals and get the same cut flooring, after which their bound is re-evaluated
 exactly and must still reach lam).  All other records are copied verbatim.  The accept/reject logic is unchanged: the
 dump only records what was accepted.  The filled certificate is a format-2 certificate (L records), checkable by
 verify_cmp.py and by the Lean exporter tools/export_jobsx.py.]

[verify_tree.py = verify_cmp.py + tree-only leaves (spec: TREE_FORMAT.md).  ["U"] and ["T"] / ["T", [cut ids]]
 carry NO duals; the verifier finds one itself and accepts the leaf only by the exact bound LB(y) >= lam:
  * U: an untrusted search (warm-started row-generation LP in DFS order, own square cuts by the m3 rule, up to 20
    separation rounds; first the previous leaf's certifying dual is tried on the new region) proposes y; its row duals
    are rounded to multiples of 2^-64 and its cut duals to multiples of 2^-128 (any y is admissible), and LB(y) is
    evaluated exactly in integer arithmetic (IntBound; Fractions via leaf_bound_exact if a region bound is not a
    multiple of 2^-30).
  * T: the LP over all rows plus the listed square cuts; the HiGHS duals of ALL rows are taken exactly (every finite
    float is a dyadic rational; no rounding, no completion) and LB(y) is evaluated with leaf_bound_exact.
 Non-finite oracle duals are replaced by 0 (still admissible) and counted.  Soundness is unchanged: LB(y) <= F(p) for
 every admissible y, however it was obtained; a poor oracle answer can only make verification fail.
 --combine trusts the per-job summary files (only meta.json and this file's sha256 are pinned): a combined VERIFIED
 is valid only for summaries produced by this verifier in the same controlled run (or re-verify jobs directly).]

[verify_cmp.py = verify_sq.py + compressed leaves.  A compressed leaf lists duals only for rows that are not
 P, G or ZA rows: ["C", lb, idx, vals(, extra)] (vals exact numbers) or ["D", lb, F, idx, ints(, extra)] (dual = int/2^F).
 Cut table: ["K", id, sqkey] records (not tree nodes) define per-job square cuts; leaf extras may then
 reference a cut by its integer id instead of repeating the key.
 The verifier completes y on the P, G and ZA rows (all equalities, so any sign is admissible) by the rule
 "reduced cost zero on every G, P and ZA column", solved exactly by back-substitution (G from c = 2n-2 down,
 P_c from G_c, ZA rows parents-first), and then evaluates the same exact bound LB(y).  Soundness is unchanged:
 LB(y) <= F(p) holds for every admissible y, however y was obtained.]
[verify_sq.py = verify.py + one extra row type: square cuts carried inline by leaf records.
 A leaf record may have a 5th field, a list of [key, y] with key = ["sq", v0, [[B1, v1], ..., [Bk, vk]]]
 (integers; B distinct non-root blocks).  Row: sum_{a,b} v_a v_b [m_Ba m_Bb] + 2 v0 sum_a v_a m_Ba >= -v0^2,
 where [m_D m_E] is the product column canon_pair(D, E).  Validity at the true point: LHS + v0^2 =
 (v0 + sum_a v_a m_Ba)^2 >= 0, because every product column equals m_D m_E there.  The row does not depend
 on the region, so it is valid in every region.]

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
import sys, os, json, gzip, glob, time, math
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

    # ---- square cuts (global rows carried by leaf records) -----------------
    def sq_row(self, key):
        """Validate an untrusted square-cut key and return (lo, up, ent) exactly."""
        if not (isinstance(key, list) and len(key) == 3 and key[0] == "sq" and type(key[1]) is int and isinstance(key[2], list)):
            raise ValueError(f"bad sq key {key!r}")
        v0 = key[1]
        terms = []
        seen = set()
        for t in key[2]:
            if not (isinstance(t, list) and len(t) == 2 and type(t[0]) is int and type(t[1]) is int):
                raise ValueError(f"bad sq term {t!r}")
            b, v = t
            if not (1 <= b < self.nB) or b in seen:
                raise ValueError(f"bad sq block {t!r}")
            seen.add(b)
            if v != 0:
                terms.append((b, v))
        if not terms:
            raise ValueError("empty sq key")
        ent = {}
        for a in range(len(terms)):
            ba, va = terms[a]
            k = self.canon_pair(ba, ba)
            ent[k] = ent.get(k, 0) + Fr(va * va)
            if v0 != 0:
                k = self.mcol(ba)
                ent[k] = ent.get(k, 0) + Fr(2 * v0 * va)
            for c in range(a + 1, len(terms)):
                bc, vc = terms[c]
                k = self.canon_pair(ba, bc)
                ent[k] = ent.get(k, 0) + Fr(2 * va * vc)
        return Fr(-v0 * v0), None, ent

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


def leaf_bound(spec, region, rowkeys, colkeys, idx, vals, extra=()):
    """Exact Neumaier-Shcherbina bound for dual y (sparse: rows idx with values vals; extra = [[sqkey, y], ...])."""
    L, U = region
    r = {}            # reduced cost r = e_t - A^T y, only nonzero entries kept
    rowpart = Fr(0)
    items = [(None, k, v) for k, v in zip(idx, vals)] + [(key, None, v) for key, v in extra]
    for key, k, v in items:
        y = parse_frac(v)
        if y == 0:
            continue
        if key is None:
            lo, up, ent = spec.row(tuple(rowkeys[k]), L, U)
        else:
            lo, up, ent = spec.sq_row(key)
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


class Implied:
    """Region-independent structure for completing duals on P, G, ZA rows."""
    def __init__(self, spec, rowkeys):
        n = spec.n
        self.n = n
        self.rix = {tuple(k): i for i, k in enumerate(rowkeys)}
        self.aux = set()
        self.grow = [self.rix[("G", c)] for c in range(2 * n - 1)]
        self.prow = [self.rix[("P", c)] for c in range(2 * n - 1)]
        self.aux.update(self.grow); self.aux.update(self.prow)
        L0, U0 = spec.root_region()
        za = [i for i, k in enumerate(rowkeys) if k[0] == "ZA"]
        self.aux.update(za)
        self.own = {}; parents = {}
        for r in za:
            key = tuple(rowkeys[r])
            own = spec.canon_pair(key[1], key[2])
            if own[0] != "ZA":
                raise ValueError("ZA row whose own column is not a ZA column")
            self.own[r] = own
        owncols = {c: r for r, c in self.own.items()}
        if len(owncols) != len(self.own):
            raise ValueError("two ZA rows define the same column")
        self.owncols = owncols
        for r in za:
            lo, up, ent = spec.row(tuple(rowkeys[r]), L0, U0)
            if lo != 0 or up != 0 or ent.get(self.own[r]) != 1:
                raise ValueError("unexpected ZA row form")
            for ck, a in ent.items():
                if ck != self.own[r] and ck in owncols:
                    parents.setdefault(ck, []).append((r, a))
        self.parents = parents
        order = []; state = {}
        for r0 in za:
            stack = [(r0, False)]
            while stack:
                r, done = stack.pop()
                if done:
                    state[r] = 2; order.append(r); continue
                if state.get(r) == 2:
                    continue
                if state.get(r) == 1:
                    raise ValueError("cycle in ZA definitions")
                state[r] = 1
                stack.append((r, True))
                for (pr, a) in parents.get(self.own[r], []):
                    if state.get(pr) != 2:
                        stack.append((pr, False))
        self.order = order


def complete_duals(spec, region, rowkeys, imp, given, extra):
    """given: list of (row index, Fraction) for non-auxiliary rows; extra: list of (sqkey, Fraction).
    Returns the list of (row index, Fraction) for the auxiliary rows (P, G, ZA)."""
    L, U = region
    n = spec.n
    contrib = {}
    def add(ent, y):
        for ck, a in ent.items():
            contrib[ck] = contrib.get(ck, 0) + a * y
    for k, y in given:
        if y == 0:
            continue
        lo, up, ent = spec.row(tuple(rowkeys[k]), L, U)
        if (y > 0 and lo is None) or (y < 0 and up is None):
            continue                      # inadmissible sign: dropped (as in leaf_bound)
        add(ent, y)
    for key, y in extra:
        if y == 0:
            continue
        lo, up, ent = spec.sq_row(key)
        if (y > 0 and lo is None) or (y < 0 and up is None):
            continue
        add(ent, y)
    out = []
    yg = [Fr(0)] * (2 * n)
    for c in range(2 * n - 2, -1, -1):
        # column G_c: +1 in row G_c, -1 in row G_{c+1}; reduced cost -(yg[c] - yg[c+1] + contrib) = 0
        yg[c] = yg[c + 1] - contrib.get(("G", c), 0)
    for c in range(2 * n - 1):
        out.append((imp.grow[c], yg[c]))
        # column P_c: +1 in row P_c, -1 in row G_c
        out.append((imp.prow[c], yg[c] - contrib.get(("P", c), 0)))
    yza = {}
    for r in imp.order:
        own = imp.own[r]
        v = -contrib.get(own, 0)
        for (pr, a) in imp.parents.get(own, []):
            v -= a * yza[pr]
        yza[r] = v
        out.append((r, v))
    return out


def leaf_bound_exact(spec, region, rowkeys, ylist, extra):
    """leaf_bound for exact (row, Fraction) lists."""
    L, U = region
    r = {}; rowpart = Fr(0)
    items = [(None, k, y) for k, y in ylist] + [(key, None, y) for key, y in extra]
    for key, k, y in items:
        if y == 0:
            continue
        if key is None:
            lo, up, ent = spec.row(tuple(rowkeys[k]), L, U)
        else:
            lo, up, ent = spec.sq_row(key)
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


_IMP = {}


class LeafLP:
    """Float LP of a leaf region (oracle for duals only).  One persistent HiGHS model per process: all rows of rowkeys
    (mc rows refreshed for the blocks whose bounds changed), plus the leaf's square cuts (replaced per leaf); the
    previous basis is kept (warm start in DFS order)."""
    def __init__(self, spec, rowkeys):
        import numpy as np, highspy
        self.np, self.highspy = np, highspy
        self.spec = spec; self.rowkeys = rowkeys
        L0, U0 = spec.root_region()
        cols = {}
        for b in range(spec.nB):
            cols.setdefault(spec.mcol(b), len(cols))
        rows = []
        for k, key in enumerate(rowkeys):
            lo, up, ent = spec.row(tuple(key), L0, U0)
            for ck in ent:
                cols.setdefault(ck, len(cols))
            rows.append((lo, up, ent))
        cols.setdefault(("t",), len(cols))
        self.cols = cols; self.ncol = len(cols)
        self.colkeys = [None] * self.ncol
        for ck, j in cols.items():
            self.colkeys[j] = ck
        inf = highspy.kHighsInf
        self.nb = len(rowkeys)
        lo_r = np.array([-inf if lo is None else float(lo) for lo, up, ent in rows])
        up_r = np.array([inf if up is None else float(up) for lo, up, ent in rows])
        starts, idx, val = [], [], []
        for lo, up, ent in rows:
            starts.append(len(idx))
            for ck, a in ent.items():
                idx.append(cols[ck]); val.append(float(a))
        # mc structure (block indices and columns)
        self.mc_rows = []; md = []; me = []; q_ = []; zc = []; mdc = []; mec = []
        for k, key in enumerate(rowkeys):
            if key[0] == "mc":
                d, e, q = key[1], key[2], key[3]
                self.mc_rows.append(k); md.append(d); me.append(e); q_.append(q)
                zc.append(cols[spec.canon_pair(d, e)]); mdc.append(cols[spec.mcol(d)]); mec.append(cols[spec.mcol(e)])
        self.mc_rows = np.array(self.mc_rows, dtype=np.int64); self.md = np.array(md); self.me = np.array(me)
        self.mq = np.array(q_); self.mdc = np.array(mdc, dtype=np.int32); self.mec = np.array(mec, dtype=np.int32)
        self.rows_of_block = [[] for _ in range(spec.nB)]
        for t in range(len(self.mc_rows)):
            self.rows_of_block[md[t]].append(t)
            if me[t] != md[t]:
                self.rows_of_block[me[t]].append(t)
        self.L = np.array([float(x) for x in L0]); self.U = np.array([float(x) for x in U0])
        clb = np.zeros(self.ncol); cub = np.ones(self.ncol)
        for j, ck in enumerate(self.colkeys):
            lb, ub = spec.col_bounds(ck, L0, U0)
            clb[j] = float(lb); cub[j] = float(ub)
        cost = np.zeros(self.ncol); cost[cols[("t",)]] = 1.0
        h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("threads", 1)
        h.setOptionValue("presolve", "off")
        lp = highspy.HighsLp(); lp.num_col_ = self.ncol; lp.num_row_ = self.nb
        lp.col_cost_ = cost; lp.col_lower_ = clb; lp.col_upper_ = cub
        lp.row_lower_ = lo_r; lp.row_upper_ = up_r
        lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
        lp.a_matrix_.start_ = np.array(starts + [len(idx)], dtype=np.int32)
        lp.a_matrix_.index_ = np.array(idx, dtype=np.int32); lp.a_matrix_.value_ = np.array(val)
        h.passModel(lp)
        self.h = h
        self.ncut = 0
        self.blockcol = np.array([cols[spec.mcol(b)] for b in range(spec.nB)], dtype=np.int32)

    def _mc(self, L, U, ts):
        np = self.np
        d, e, q = self.md[ts], self.me[ts], self.mq[ts]
        Ld, Ud, Le, Ue = L[d], U[d], L[e], U[e]
        diag = d == e
        a_d = np.select([q == 0, q == 1, q == 2], [Le, Ue, -Ue], -Le)
        a_e = np.select([q == 0, q == 1, q == 2], [Ld, Ud, -Ld], -Ud)
        rhs = np.select([q == 0, q == 1, q == 2], [Ld * Le, Ud * Ue, -Ld * Ue], -Ud * Le)
        a_dd = np.select([q == 0, q == 1], [2 * Ld, 2 * Ud], -(Ld + Ud))
        rhs_d = np.select([q == 0, q == 1], [Ld * Ld, Ud * Ud], -Ld * Ud)
        return np.where(diag, a_dd, a_d), np.where(diag, 0.0, a_e), np.where(diag, rhs_d, rhs), diag

    def solve(self, region, cutkeys):
        np, highspy = self.np, self.highspy
        spec = self.spec
        L = np.array([float(x) for x in region[0]]); U = np.array([float(x) for x in region[1]])
        h = self.h; inf = highspy.kHighsInf
        changed = np.nonzero((L != self.L) | (U != self.U))[0]
        if len(changed):
            ts = np.array(sorted(set(t for b in changed for t in self.rows_of_block[b])), dtype=np.int64)
            if len(ts):
                ad, ae, rhs, diag = self._mc(L, U, ts)
                rows = self.mc_rows[ts]
                for t in range(len(ts)):
                    r = int(rows[t])
                    h.changeCoeff(r, int(self.mdc[ts[t]]), float(ad[t]))
                    if not diag[t]:
                        h.changeCoeff(r, int(self.mec[ts[t]]), float(ae[t]))
                h.changeRowsBounds(len(rows), rows.astype(np.int32), np.full(len(rows), -inf), rhs.astype(float))
            cc = self.blockcol[changed]
            h.changeColsBounds(len(cc), cc, L[changed].copy(), U[changed].copy())
            self.L, self.U = L, U
        if self.ncut:
            h.deleteRows(self.ncut, np.arange(self.nb, self.nb + self.ncut, dtype=np.int32))
            self.ncut = 0
        if cutkeys:
            lo_r, starts, idx, val = [], [], [], []
            for key in cutkeys:
                lo, up, ent = spec.sq_row(key)
                sc = float(max(abs(float(a)) for a in ent.values()))
                div = int(sc) if sc >= 1 else 1
                starts.append(len(idx))
                for ck, a in ent.items():
                    idx.append(self.cols[ck]); val.append(float(a / div))
                lo_r.append(float(lo / div))
            h.addRows(len(cutkeys), np.array(lo_r), np.full(len(cutkeys), inf), len(idx), np.array(starts, dtype=np.int32),
                      np.array(idx, dtype=np.int32), np.array(val))
            self.ncut = len(cutkeys)
        h.run()
        if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
            h.clearSolver(); h.run()
            if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
                return None
        y = np.array(h.getSolution().row_dual)
        return h.getInfo().objective_function_value, y, self.nb + self.ncut


class IntBound:
    """Exact Neumaier-Shcherbina bound in integer arithmetic, for duals rounded to m / 2^G (any dual is admissible,
    so rounding the oracle duals is sound).  Every row coefficient and bound is a rational whose denominator divides
    DC = lcm(1..2n) * 2^60 (window weights 2n/(c2-c1+2); McCormick products of region bounds, which are multiples of
    2^-30; all other rows integral); column bounds are multiples of 2^-30.  The value equals leaf_bound_exact on the
    same rounded duals (cross-checked in testing)."""
    G = 128

    def __init__(self, spec, rowkeys):
        import math
        self.spec = spec; self.rowkeys = rowkeys
        n = spec.n
        l = 1
        for k in range(1, 2 * n + 1):
            l = l * k // math.gcd(l, k)
        self.DC = l * 2 ** 60
        L0, U0 = spec.root_region()
        self.static = {}
        self.colid = {}
        for k, key in enumerate(rowkeys):
            if key[0] == "mc":
                continue
            lo, up, ent = spec.row(tuple(key), L0, U0)
            self.static[k] = (self._scale(lo), self._scale(up), [(self._cid(ck), self._scale(a)) for ck, a in ent.items()])

    def _cid(self, ck):
        if ck not in self.colid:
            self.colid[ck] = len(self.colid)
        return self.colid[ck]

    def _scale(self, v):
        if v is None:
            return None
        q = v * self.DC
        if q.denominator != 1:
            raise ValueError("coefficient denominator does not divide DC")
        return q.numerator

    def _mc_int(self, key, li, ui):
        """McCormick row ('mc', d, e, q) scaled by DC, from integer region numerators li, ui (bounds * 2^30);
        mirrors Spec.row exactly (checked against it in testing)."""
        spec = self.spec
        d, e, q = key[1], key[2], key[3]
        K = self.DC >> 60; K30 = K << 30
        z = self._cid(spec.canon_pair(d, e)); md = self._cid(spec.mcol(d)); me = self._cid(spec.mcol(e))
        Ld, Ud, Le, Ue = li[d], ui[d], li[e], ui[e]
        if d == e:
            if q == 0:
                return None, Ld * Ld * K, [(z, -self.DC), (md, 2 * Ld * K30)]
            if q == 1:
                return None, Ud * Ud * K, [(z, -self.DC), (md, 2 * Ud * K30)]
            return None, -Ld * Ud * K, [(z, self.DC), (md, -(Ld + Ud) * K30)]
        if q == 0:
            return None, Ld * Le * K, [(z, -self.DC), (md, Le * K30), (me, Ld * K30)]
        if q == 1:
            return None, Ud * Ue * K, [(z, -self.DC), (md, Ue * K30), (me, Ud * K30)]
        if q == 2:
            return None, -Ld * Ue * K, [(z, self.DC), (md, -Ue * K30), (me, -Ld * K30)]
        return None, -Ud * Le * K, [(z, self.DC), (md, -Le * K30), (me, -Ud * K30)]

    def bound(self, reg, ylist, cuts):
        """ylist: [(row index, float dual)], cuts: [(sq key, Fraction dual of the sq_row as defined)].  Returns Fraction."""
        spec = self.spec; G = self.G
        L, U = reg
        li = []; ui = []
        for b in range(spec.nB):
            a = L[b] * 2 ** 30; c = U[b] * 2 ** 30
            if a.denominator != 1 or c.denominator != 1:
                raise NotDyadic("region bound is not a multiple of 2^-30")
            li.append(a.numerator); ui.append(c.numerator)
        R = {}                    # column id -> integer, = 2^G * DC * (reduced cost) without the objective
        rowpart = 0               # = 2^G * DC * rowpart
        for k, y in ylist:
            m = round(y * 2.0 ** 64) * 2 ** (G - 64)       # dual rounded to 2^-64, carried at 2^-G
            if m == 0:
                continue
            if k in self.static:
                lo, up, ent = self.static[k]
            else:
                key = self.rowkeys[k]
                if key[0] != "mc":
                    raise ValueError("unexpected region-dependent row")
                lo, up, ent = self._mc_int(key, li, ui)
            if m > 0:
                if lo is None:
                    continue
                rowpart += m * lo
            else:
                if up is None:
                    continue
                rowpart += m * up
            for c, a in ent:
                R[c] = R.get(c, 0) - m * a
        for key, yq in cuts:
            mq = yq * 2 ** G
            m = mq.numerator // mq.denominator            # floor: still a dyadic dual
            if m == 0:
                continue
            lo_f, up_f, ent_f = spec.sq_row(key)
            if m > 0:
                if lo_f is None:
                    continue
                rowpart += m * self._scale(lo_f)
            else:
                if up_f is None:
                    continue
                rowpart += m * self._scale(up_f)
            for ck, a in ent_f.items():
                if a.denominator != 1:
                    raise ValueError("non-integral square-cut coefficient")
                c = self._cid(ck)
                R[c] = R.get(c, 0) - m * a.numerator * self.DC
        tc = self._cid(("t",))
        R[tc] = R.get(tc, 0) + 2 ** G * self.DC
        if not hasattr(self, "_inv") or len(self._inv) != len(self.colid):
            self._inv = {c: ck for ck, c in self.colid.items()}
        inv = self._inv
        colpart = 0               # = 2^G * DC * 2^30 * colpart
        one30 = 2 ** 30
        for c, rc in R.items():
            if rc == 0:
                continue
            ck = inv[c]
            if ck[0] == "m":
                lbn, ubn = li[ck[1]], ui[ck[1]]
            elif ck[0] in ("Z", "ZA", "P", "G"):
                lbn, ubn = 0, one30
            elif ck[0] == "t":
                lbn, ubn = 0, int(TMAX * one30)
            else:
                lb, ub = spec.col_bounds(ck, L, U)
                lbn, ubn = int(lb * one30), int(ub * one30)
            colpart += min(rc * lbn, rc * ubn)
        return Fr(rowpart * 2 ** 30 + colpart, 2 ** G * self.DC * 2 ** 30)


_IB = {}
_NONFINITE = [0]


class NotDyadic(Exception):
    pass
_LP = {}
TREE_F = (20, 24, 28, 32, 40, 48, 56, 64)


def tree_leaf_bound(spec, reg, rowkeys, imp, cutkeys, lam):
    """Oracle dual for a tree-only leaf (all rows and the listed cuts), taken exactly (every float is a dyadic
    rational), then the exact Neumaier-Shcherbina bound."""
    if spec.n not in _LP:
        _LP[spec.n] = LeafLP(spec, rowkeys)
    res = _LP[spec.n].solve(reg, cutkeys)
    if res is None:
        return None
    obj, y, nrow = res
    nb = len(rowkeys)
    nonfinite = int(sum(1 for v in y if not math.isfinite(v)))
    if nonfinite:
        _NONFINITE[0] += nonfinite
        y = [v if math.isfinite(v) else 0.0 for v in y]
    ylist = [(k, Fr(float(y[k]))) for k in range(nb) if y[k] != 0.0]
    extra = []
    for t, key in enumerate(cutkeys):
        if y[nb + t] == 0.0:
            continue
        lo, up, ent = spec.sq_row(key)
        sc_c = float(max(abs(float(a)) for a in ent.values()))
        div = int(sc_c) if sc_c >= 1 else 1          # the oracle LP carried this cut row divided by div
        extra.append((key, Fr(float(y[nb + t])) / div))
    _CERT[0] = (ylist, extra)
    return leaf_bound_exact(spec, reg, rowkeys, ylist, extra)


class CutPool:
    """Square cuts found by the verifier's own separation (untrusted search; each cut row is valid by construction,
    since sq_row(key) is the expansion of a square).  Kept per job; the most recent `cap` cuts are used."""
    def __init__(self, spec, bits=20, tol=1e-6, k=20, rounds=20):
        import numpy as np
        self.np = np; self.spec = spec; self.bits = bits; self.tol = tol; self.k = k; self.rounds = rounds
        self.keys = []; self.seen = set()
        nB = spec.nB
        self.pairs = [(d, e) for d in range(1, nB) for e in range(d + 1, nB)]

    def separate(self, x, LP, return_keys=False):
        np = self.np; spec = self.spec; sc = 2.0 ** self.bits
        cols = LP.cols
        if not hasattr(self, "_idx"):
            d = np.array([p[0] for p in self.pairs]); e = np.array([p[1] for p in self.pairs])
            self._idx = (d, e, np.array([cols[spec.mcol(b)] for b in d]), np.array([cols[spec.mcol(b)] for b in e]),
                         np.array([cols[spec.canon_pair(b, b)] for b in d]), np.array([cols[spec.canon_pair(b, b)] for b in e]),
                         np.array([cols[spec.canon_pair(a, b)] for a, b in zip(d, e)]))
        d, e, cmd, cme, cdd, cee, cde = self._idx
        M = np.zeros((len(d), 3, 3)); M[:, 0, 0] = 1
        M[:, 0, 1] = M[:, 1, 0] = x[cmd]; M[:, 0, 2] = M[:, 2, 0] = x[cme]
        M[:, 1, 1] = x[cdd]; M[:, 2, 2] = x[cee]; M[:, 1, 2] = M[:, 2, 1] = x[cde]
        w, V = np.linalg.eigh(M)
        new = 0; found = []
        for t in np.argsort(w[:, 0])[: self.k]:
            if w[t, 0] >= -self.tol:
                break
            v = V[t, :, 0] / np.abs(V[t, :, 0]).max()
            vi = np.round(v * sc).astype(np.int64)
            if vi[1] == 0 and vi[2] == 0:
                continue
            key = ["sq", int(vi[0]), [[int(d[t]), int(vi[1])], [int(e[t]), int(vi[2])]]]
            found.append(key)
            sk = json.dumps(key)
            if sk in self.seen:
                continue
            self.seen.add(sk); self.keys.append(key); new += 1
        return found if return_keys else new



class LazyLP:
    """Oracle LP with row generation (untrusted; only proposes duals).  Universe = base rows [0, nb) plus square cuts
    appended as they are found.  Always in the LP: P, G, tree, ZA, rlt, sym rows; window, McCormick and cut rows enter
    when violated at the LP point and leave after `max_age` leaves without dual weight.  The returned dual is padded with
    zeros for rows not in the LP; at convergence (no violated row) it is optimal for the full LP."""
    def __init__(self, spec, rowkeys, max_age=40, add_cap=400, tol=1e-9):
        import numpy as np, highspy
        self.np, self.highspy = np, highspy
        self.spec = spec; self.rowkeys = rowkeys; self.max_age = max_age; self.add_cap = add_cap; self.tol = tol
        base = LeafLP(spec, rowkeys)          # reuse its column map and mc structure
        self.cols = base.cols; self.ncol = base.ncol; self.colkeys = base.colkeys
        self.md, self.me, self.mq, self.mdc, self.mec = base.md, base.me, base.mq, base.mdc, base.mec
        self.mc_rows = base.mc_rows; self.rows_of_block = base.rows_of_block; self.blockcol = base.blockcol
        self._mc = base._mc
        nb = self.nb = len(rowkeys)
        L0, U0 = spec.root_region()
        inf = highspy.kHighsInf
        lo = np.empty(nb); up = np.empty(nb); I, J, V = [], [], []
        for k, key in enumerate(rowkeys):
            l_, u_, ent = spec.row(tuple(key), L0, U0)
            lo[k] = -inf if l_ is None else float(l_); up[k] = inf if u_ is None else float(u_)
            for ck, a in ent.items():
                I.append(k); J.append(self.cols[ck]); V.append(float(a))
        import scipy.sparse as sp
        self.A = sp.csr_matrix((V, (I, J)), shape=(nb, self.ncol))
        self.lo = lo; self.up = up
        kinds = [key[0] for key in rowkeys]
        self.is_win = np.array([k == "win" for k in kinds]); self.is_mc = np.array([k == "mc" for k in kinds])
        self.lazy = self.is_win | self.is_mc
        self.mcpos = -np.ones(nb, dtype=np.int64); self.mcpos[self.mc_rows] = np.arange(len(self.mc_rows))
        self.win_idx = np.nonzero(self.is_win)[0]
        self.Awin = self.A[self.win_idx]
        # cut universe
        self.cut_rows = []            # (cols, vals, lo) scaled as in the LP
        self.cut_keys = []; self.cut_div = []; self.cut_index = {}
        # HiGHS model with the fixed rows
        h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("threads", 1)
        h.setOptionValue("presolve", "off"); h.setOptionValue("solver", "simplex"); h.setOptionValue("simplex_strategy", 1)
        h.setOptionValue("simplex_dual_edge_weight_strategy", 1)       # Devex
        for k_, v_ in json.loads(os.environ.get("VT_HIGHS_OPTS", "{}")).items():   # robustness tests only (oracle)
            h.setOptionValue(k_, v_)
        self.objbound = None
        lp = highspy.HighsLp(); lp.num_col_ = self.ncol; lp.num_row_ = 0
        clb = np.zeros(self.ncol); cub = np.ones(self.ncol)
        for j, ck in enumerate(self.colkeys):
            lb, ub = spec.col_bounds(ck, L0, U0)
            clb[j] = float(lb); cub[j] = float(ub)
        cost = np.zeros(self.ncol); cost[self.cols[("t",)]] = 1.0
        lp.col_cost_ = cost; lp.col_lower_ = clb; lp.col_upper_ = cub
        h.passModel(lp)
        self.h = h
        self.L = np.array([float(x) for x in L0]); self.U = np.array([float(x) for x in U0])
        self.lp_rows = []             # universe ids in HiGHS order (cuts: nb + c)
        self.pos = {}
        self.age = {}
        self._add(list(np.nonzero(~self.lazy)[0]))

    def _row_data(self, u):
        np = self.np
        if u >= self.nb:
            cols, vals, lo = self.cut_rows[u - self.nb]
            return cols, vals, lo, self.highspy.kHighsInf
        if self.is_mc[u]:
            t = self.mcpos[u]
            ad, ae, rhs, diag = self._mc(self.L, self.U, np.array([t]))
            md, me = int(self.mdc[t]), int(self.mec[t])
            k = self.rowkeys[u]
            z = self.cols[self.spec.canon_pair(k[1], k[2])]
            zc = -1.0 if k[3] in (0, 1) else 1.0
            if diag[0]:
                return [z, md], [zc, float(ad[0])], -self.highspy.kHighsInf, float(rhs[0])
            return [z, md, me], [zc, float(ad[0]), float(ae[0])], -self.highspy.kHighsInf, float(rhs[0])
        a, b = self.A.indptr[u], self.A.indptr[u + 1]
        return list(self.A.indices[a:b]), list(self.A.data[a:b]), self.lo[u], self.up[u]

    def _add(self, us):
        np = self.np
        us = [u for u in us if u not in self.pos]
        if not us:
            return
        lo, up, starts, idx, val = [], [], [], [], []
        for u in us:
            c, v, l_, u_ = self._row_data(u)
            starts.append(len(idx)); idx += list(c); val += list(v); lo.append(l_); up.append(u_)
        self.h.addRows(len(us), np.array(lo, dtype=float), np.array(up, dtype=float), len(idx), np.array(starts, dtype=np.int32),
                       np.array(idx, dtype=np.int32), np.array(val, dtype=float))
        for u in us:
            self.pos[u] = len(self.lp_rows); self.lp_rows.append(u); self.age[u] = 0

    def _delete(self, us):
        np = self.np
        us = [u for u in us if u in self.pos]
        if not us:
            return
        hp = sorted(self.pos[u] for u in us)
        self.h.deleteRows(len(hp), np.array(hp, dtype=np.int32))
        dead = set(us)
        self.lp_rows = [u for u in self.lp_rows if u not in dead]
        self.pos = {u: i for i, u in enumerate(self.lp_rows)}
        for u in us:
            self.age.pop(u, None)

    def ensure_cuts(self, keys):
        """put the given square cuts into the LP (new ones join the cut universe; aged-out ones are re-added).
        Returns the number of rows added."""
        want = []
        for key in keys:
            sk = json.dumps(key)
            if sk not in self.cut_index:
                lo, up, ent = self.spec.sq_row(key)
                sc = float(max(abs(float(a)) for a in ent.values()))
                div = int(sc) if sc >= 1 else 1
                self.cut_rows.append(([self.cols[ck] for ck in ent], [float(a / div) for a in ent.values()], float(lo / div)))
                self.cut_keys.append(key); self.cut_div.append(div)
                self.cut_index[sk] = len(self.cut_keys) - 1
            u = self.nb + self.cut_index[sk]
            if u not in self.pos:
                want.append(u)
        self._add(want)
        return len(want)

    def set_region(self, region):
        np, highspy = self.np, self.highspy
        L = np.array([float(x) for x in region[0]]); U = np.array([float(x) for x in region[1]])
        changed = np.nonzero((L != self.L) | (U != self.U))[0]
        if not len(changed):
            return
        self.L, self.U = L, U
        ts = sorted(set(t for b in changed for t in self.rows_of_block[b]))
        present = [t for t in ts if int(self.mc_rows[t]) in self.pos]
        if present:
            ts = np.array(present, dtype=np.int64)
            ad, ae, rhs, diag = self._mc(L, U, ts)
            hrows = []
            for i, t in enumerate(ts):
                r = self.pos[int(self.mc_rows[t])]
                self.h.changeCoeff(r, int(self.mdc[t]), float(ad[i]))
                if not diag[i]:
                    self.h.changeCoeff(r, int(self.mec[t]), float(ae[i]))
                hrows.append(r)
            self.h.changeRowsBounds(len(hrows), np.array(hrows, dtype=np.int32), np.full(len(hrows), -highspy.kHighsInf), rhs.astype(float))
        cc = self.blockcol[changed]
        self.h.changeColsBounds(len(cc), cc, L[changed].copy(), U[changed].copy())

    def violated(self, x):
        np = self.np
        out = []
        t = x[self.cols[("t",)]]
        act = self.Awin @ x
        v = act - self.up[self.win_idx]
        ids = self.win_idx[v > self.tol]
        out += [(float(vv), int(u)) for vv, u in zip(v[v > self.tol], ids) if int(u) not in self.pos]
        ts = np.arange(len(self.mc_rows))
        ad, ae, rhs, diag = self._mc(self.L, self.U, ts)
        z = np.array([x[self.cols[self.spec.canon_pair(int(self.md[i]), int(self.me[i]))]] for i in ts]) if not hasattr(self, "_zc") else x[self._zc]
        if not hasattr(self, "_zc"):
            self._zc = np.array([self.cols[self.spec.canon_pair(int(self.md[i]), int(self.me[i]))] for i in ts])
            self._zsign = np.where(self.mq <= 1, -1.0, 1.0)
        z = x[self._zc]
        a = self._zsign * z + ad * x[self.mdc] + np.where(diag, 0.0, ae * x[self.mec]) - rhs
        ids = np.nonzero(a > self.tol)[0]
        out += [(float(a[i]), int(self.mc_rows[i])) for i in ids if int(self.mc_rows[i]) not in self.pos]
        out.sort(reverse=True)
        return [u for _, u in out[: self.add_cap]]

    def set_objbound(self, v):
        if v != self.objbound:
            self.h.setOptionValue("objective_bound", self.highspy.kHighsInf if v is None else float(v))
            self.objbound = v

    def solve_converged(self, max_rounds=60):
        """Returns (obj, y, x, early): early = True if the dual simplex stopped at the objective bound (y is then a
        dual-feasible point of the current row set; the caller checks its exact bound)."""
        np, highspy = self.np, self.highspy
        h = self.h
        MS = highspy.HighsModelStatus
        for rnd in range(max_rounds):
            h.run()
            st = h.getModelStatus()
            if st == MS.kObjectiveBound:
                sol = h.getSolution()
                return h.getInfo().objective_function_value, np.array(sol.row_dual), np.array(sol.col_value), True
            if st != MS.kOptimal:
                h.clearSolver(); h.run()
                st = h.getModelStatus()
                if st == MS.kObjectiveBound:
                    sol = h.getSolution()
                    return h.getInfo().objective_function_value, np.array(sol.row_dual), np.array(sol.col_value), True
                if st != MS.kOptimal:
                    return None
            sol = h.getSolution()
            x = np.array(sol.col_value)
            new = self.violated(x)
            if not new:
                y = np.array(sol.row_dual)
                return h.getInfo().objective_function_value, y, x, False
            self._add(new)
        return None

    def end_leaf(self, y):
        """age rows by the dual of the last solve; drop lazy rows unused for max_age leaves."""
        dead = []
        for i, u in enumerate(self.lp_rows):
            if u < self.nb and not self.lazy[u]:
                continue
            if i < len(y) and y[i] != 0.0:
                self.age[u] = 0
            else:
                self.age[u] = self.age.get(u, 0) + 1
                if self.age[u] > self.max_age:
                    dead.append(u)
        self._delete(dead)


def exact_bound(spec, reg, rowkeys, ylist, cuts):
    """LB(y) exactly: IntBound (duals rounded to 2^-64 / 2^-128), or the same rounded duals in Fractions when a region
    bound is not a multiple of 2^-30."""
    try:
        return _IB[spec.n].bound(reg, ylist, cuts)
    except NotDyadic:
        G = IntBound.G
        yl = [(k, Fr(round(v * 2.0 ** 64) * 2 ** (G - 64), 2 ** G)) for k, v in ylist]
        cu = []
        for key, yq in cuts:
            mq = yq * 2 ** G
            cu.append((key, Fr(mq.numerator // mq.denominator, 2 ** G)))
        return leaf_bound_exact(spec, reg, rowkeys, [(k, v) for k, v in yl if v != 0], [(k, v) for k, v in cu if v != 0])


def tree_leaf_bound_lazy(spec, reg, rowkeys, cutpool, lam, state):
    """U leaf: (1) the previous leaf's certifying dual on this region; (2) the row-generation oracle with up to
    cutpool.rounds rounds of own square-cut separation.  Effort counters in state["eff"]."""
    if "LZ" not in state:
        state["LZ"] = LazyLP(spec, rowkeys)
        state["eff"] = {"reuse": 0, "solves": 0, "sep_hist": {}, "nonfinite": 0, "hints": []}
        state["leafno"] = 0
    LZ = state["LZ"]; eff = state["eff"]
    state["leafno"] += 1
    if spec.n not in _IB:
        _IB[spec.n] = IntBound(spec, rowkeys)
    last = state.get("last") if REUSE else None
    if last is not None:
        lb = exact_bound(spec, reg, rowkeys, last[0], last[1])
        if lb >= lam:
            eff["reuse"] += 1
            return lb
    LZ.set_region(reg)
    best = None
    LZ.set_objbound(float(lam) + 1e-6)
    rnd = 0
    while rnd <= cutpool.rounds:
        res = LZ.solve_converged()
        eff["solves"] += 1
        if res is None:
            return best
        obj, y, x, early = res
        if not all(math.isfinite(v) for v in y):
            eff["nonfinite"] += int(sum(1 for v in y if not math.isfinite(v)))
            y = LZ.np.where(LZ.np.isfinite(y), y, 0.0)
        if early or obj >= float(lam) - 1e-9:
            ylist = []; cuts = []
            for i, u in enumerate(LZ.lp_rows):
                if y[i] == 0.0:
                    continue
                if u < LZ.nb:
                    ylist.append((u, float(y[i])))
                else:
                    c = u - LZ.nb
                    cuts.append((LZ.cut_keys[c], Fr(float(y[i])) / LZ.cut_div[c]))
            lb = exact_bound(spec, reg, rowkeys, ylist, cuts)
            best = lb if best is None else max(best, lb)
            if lb >= lam:
                LZ.end_leaf(y)
                state["last"] = (ylist, cuts)
                eff["sep_hist"][rnd] = eff["sep_hist"].get(rnd, 0) + 1
                if rnd >= HINT_ROUNDS:
                    eff["hints"].append([state["leafno"], [key for key, _ in cuts]])
                return lb
            if early:                      # early-stopped dual not good enough: solve this round to convergence
                LZ.set_objbound(None)
                continue
        rnd += 1
        if LZ.ensure_cuts(cutpool.separate(x, LZ, return_keys=True)) == 0:
            break
        LZ.set_objbound(float(lam) + 1e-6)
    return best


HINT_ROUNDS = int(os.environ.get("VT_HINT_ROUNDS", 4))     # leaves needing >= this many separation rounds get hints (VT_HINTS_DIR)
REUSE = bool(os.environ.get("VT_REUSE"))                   # try the previous leaf's dual first (measured: no hits)
DUMP_DIR = os.environ.get("VT_DUMP_DIR")                   # [dump] write filled job files here
_CERT = [None]                                             # [dump] (ylist, extra) of the last exact-path oracle leaf


def dump_leaf(spec, reg, rowkeys, colkeys, lam, lb, ylist, cuts, mode):
    """[dump] The L record of an accepted tree-only leaf.  mode "int": the dual of the IntBound check (rows rounded to
    m/2^64, cuts floored to m/2^128: the values IntBound evaluated); mode "exact": exact binary64 row duals, cuts floored
    to m/2^128, bound re-evaluated exactly (must reach lam)."""
    idx, vals = [], []
    for k, y in ylist:
        q = Fr(round(float(y) * 2.0 ** 64), 2 ** 64) if mode == "int" else Fr(y)
        if q == 0:
            continue
        f = float(q)
        if Fr(f) != q:
            raise AssertionError("dump: row dual is not binary64")
        idx.append(int(k)); vals.append(f)
    extra = []
    for key, yq in cuts:
        mq = Fr(yq) * 2 ** 128
        q = Fr(mq.numerator // mq.denominator, 2 ** 128)
        if q != 0:
            extra.append([key, str(q)])
    if mode != "int":
        lb = leaf_bound(spec, reg, rowkeys, colkeys, idx, vals, [(k, v) for k, v in extra])
        if lb < lam:
            raise AssertionError("dump: rounded exact-path dual does not reach lam")
    rec = ["L", float(lb), idx, vals]
    if extra:
        rec.append(extra)
    return rec


def load_hints(path_file):
    """Optional hints (TREE_FORMAT.md section 4): CERTDIR/hints/<job file name>.hints.json = [[U-leaf ordinal (1-based, in
    record order), [square-cut keys]], ...].  Untrusted suggestions: each key is validated when used, and a hint can only
    help a leaf to pass the exact check, never replace it."""
    hp = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(path_file))), "hints",
                      os.path.basename(path_file) + ".hints.json")
    if not os.path.exists(hp):
        return {}
    out = {}
    try:
        for item in json.load(open(hp)):
            if isinstance(item, list) and len(item) == 2 and type(item[0]) is int and isinstance(item[1], list):
                out[item[0]] = item[1]
    except (ValueError, OSError):
        return {}
    return out


def verify_job(path_file, spec, lam, rowkeys, colkeys, verbose=False):
    """Verify one job log. Returns (stats, delegated_paths, root_path)."""
    if spec.n not in _IMP:
        _IMP[spec.n] = Implied(spec, rowkeys)
    imp = _IMP[spec.n]
    hints = load_hints(path_file); uleaf = 0
    op = gzip.open if path_file.endswith(".gz") else open
    with op(path_file, "rt") as fh:
        hline = fh.readline()
        header = json.loads(hline)
        dump = None
        if DUMP_DIR:
            if os.environ.get("VT_SOFT"):
                raise SystemExit("VT_DUMP_DIR and VT_SOFT cannot be combined")
            os.makedirs(DUMP_DIR, exist_ok=True)
            dump = gzip.open(os.path.join(DUMP_DIR, os.path.basename(path_file)), "wt")
            dump.write(hline if hline.endswith("\n") else hline + "\n")
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
        cuts = {}

        def resolve(ex):
            if not isinstance(ex, list):
                raise ValueError("bad extra rows")
            outx = []
            for t in ex:
                if not (isinstance(t, list) and len(t) == 2):
                    raise ValueError("bad extra row")
                key = t[0]
                if type(key) is int:
                    if key not in cuts:
                        raise ValueError(f"undefined cut id {key}")
                    key = cuts[key]
                outx.append([key, t[1]])
            return outx
        for line in fh:
            rec = json.loads(line)
            out_line = line if line.endswith("\n") else line + "\n"
            if isinstance(rec, list) and rec and rec[0] == "K":
                if len(rec) != 3 or type(rec[1]) is not int or rec[1] in cuts:
                    raise ValueError(f"bad K record {rec!r}")
                spec.sq_row(rec[2])          # validates the key
                cuts[rec[1]] = rec[2]
                if dump:
                    dump.write(out_line)
                continue
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
                if len(rec) not in (4, 5) or len(rec[2]) != len(rec[3]) or any(type(k) is not int or not (0 <= k < len(rowkeys)) for k in rec[2]):
                    raise ValueError("bad L record")
                extra = resolve(rec[4]) if len(rec) == 5 else []
                lb = leaf_bound(spec, reg, rowkeys, colkeys, rec[2], rec[3], extra)
                if lb < lam:
                    raise AssertionError(f"leaf bound {float(lb)} < lam at path {path}")
                stats["leaves"] += 1
                stats["minlb"] = lb if stats["minlb"] is None else min(stats["minlb"], lb)
            elif kind in ("C", "D"):
                if kind == "C":
                    if len(rec) not in (4, 5) or len(rec[2]) != len(rec[3]):
                        raise ValueError("bad C record")
                    idx = rec[2]; ys = [parse_frac(v) for v in rec[3]]; ex = resolve(rec[4]) if len(rec) == 5 else []
                else:
                    if len(rec) not in (5, 6) or type(rec[2]) is not int or not (0 <= rec[2] <= 512) or len(rec[3]) != len(rec[4]):
                        raise ValueError("bad D record")
                    if any(type(v) is not int for v in rec[4]):
                        raise ValueError("bad D record integers")
                    idx = rec[3]; ys = [Fr(v, 2 ** rec[2]) for v in rec[4]]; ex = resolve(rec[5]) if len(rec) == 6 else []
                if any(type(k) is not int or not (0 <= k < len(rowkeys)) or k in imp.aux for k in idx) or len(set(idx)) != len(idx):
                    raise ValueError("bad compressed leaf row list")
                if not isinstance(ex, list) or any(not (isinstance(t, list) and len(t) == 2) for t in ex):
                    raise ValueError("bad compressed leaf extra rows")
                given = list(zip(idx, ys)); extra = [(t[0], parse_frac(t[1])) for t in ex]
                aux = complete_duals(spec, reg, rowkeys, imp, given, extra)
                lb = leaf_bound_exact(spec, reg, rowkeys, given + aux, extra)
                if lb < lam:
                    raise AssertionError(f"compressed leaf bound {float(lb)} < lam at path {path}")
                stats["leaves"] += 1
                stats["minlb"] = lb if stats["minlb"] is None else min(stats["minlb"], lb)
            elif kind == "U":
                if len(rec) != 1:
                    raise ValueError("bad U record")
                if "pool" not in locals():
                    pool = CutPool(spec, rounds=int(os.environ.get("VT_MAX_ROUNDS", 20))); lzstate = {}
                uleaf += 1
                lb = tree_leaf_bound_lazy(spec, reg, rowkeys, pool, lam, lzstate)
                src = "lazy"
                if (lb is None or lb < lam) and uleaf in hints:
                    # retry 2: the certificate's hint cuts (validated by sq_row; an invalid key only fails the retry)
                    try:
                        lb2 = tree_leaf_bound(spec, reg, rowkeys, imp, hints[uleaf], lam)
                    except ValueError:
                        lb2 = None
                    if lb2 is not None and (lb is None or lb2 > lb):
                        lb = lb2
                        src = "hint"
                    stats["hint_used"] = stats.get("hint_used", 0) + 1
                if (lb is None or lb < lam) and os.environ.get("VT_SOFT"):      # diagnostics only: count, never VERIFIED
                    stats["soft_fail"] = stats.get("soft_fail", 0) + 1
                    stats["leaves"] += 1
                    continue
                if lb is None or lb < lam:
                    raise AssertionError(f"tree leaf (own cuts): no certifying dual found (best {None if lb is None else float(lb)}) at path {path}")
                stats["leaves"] += 1
                stats["minlb"] = lb if stats["minlb"] is None else min(stats["minlb"], lb)
                if dump:
                    if src == "lazy":
                        yl, cu = lzstate["last"]
                        out_line = json.dumps(dump_leaf(spec, reg, rowkeys, colkeys, lam, lb, yl, cu, "int")) + "\n"
                    else:
                        yl, cu = _CERT[0]
                        out_line = json.dumps(dump_leaf(spec, reg, rowkeys, colkeys, lam, lb, yl, cu, "exact")) + "\n"
            elif kind == "T":
                if len(rec) not in (1, 2) or (len(rec) == 2 and (not isinstance(rec[1], list) or any(type(c) is not int for c in rec[1]))):
                    raise ValueError("bad T record")
                ids = rec[1] if len(rec) == 2 else []
                if any(c not in cuts for c in ids):
                    raise ValueError("undefined cut id in T record")
                lb = tree_leaf_bound(spec, reg, rowkeys, imp, [cuts[c] for c in ids], lam)
                if lb is None or lb < lam:
                    raise AssertionError(f"tree leaf: no certifying dual found (best {None if lb is None else float(lb)}) at path {path}")
                stats["leaves"] += 1
                stats["minlb"] = lb if stats["minlb"] is None else min(stats["minlb"], lb)
                if dump:
                    yl, cu = _CERT[0]
                    out_line = json.dumps(dump_leaf(spec, reg, rowkeys, colkeys, lam, lb, yl, cu, "exact")) + "\n"
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
            if dump:
                dump.write(out_line)
        if stack:
            raise AssertionError(f"{len(stack)} nodes left without records")
        if dump:
            dump.close()
    if "lzstate" in locals() and "eff" in lzstate:
        e = lzstate["eff"]
        stats["reuse"] = e["reuse"]; stats["solves"] = e["solves"]; stats["nonfinite"] = e["nonfinite"] + _NONFINITE[0]
        stats["sep_hist"] = {str(k): v for k, v in sorted(e["sep_hist"].items())}
        stats["hints"] = len(e["hints"])
        hd = os.environ.get("VT_HINTS_DIR")
        if hd and e["hints"]:
            os.makedirs(hd, exist_ok=True)
            with open(os.path.join(hd, os.path.basename(path_file) + ".hints.json"), "w") as fh:
                json.dump(e["hints"], fh)
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
    if os.environ.get("VT_SOFT") and (args.summary is not None or args.combine is not None):
        sys.exit("VT_SOFT (diagnostics) cannot be combined with --summary/--combine")
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
    eff = {"reuse": 0, "solves": 0, "nonfinite": 0, "hints": 0}; hist = {}
    for st, dl, rp in results:
        for k in eff:
            eff[k] += st.get(k, 0)
        for k, v in st.get("sep_hist", {}).items():
            hist[k] = hist.get(k, 0) + v
    print("EFFORT (U leaves): reuse hits %d, oracle solves %d, separation rounds histogram %s, non-finite duals zeroed %d, "
          "leaves with >= %d rounds %d" % (eff["reuse"], eff["solves"], dict(sorted(hist.items(), key=lambda t: int(t[0]))),
                                           eff["nonfinite"], HINT_ROUNDS, eff["hints"]), flush=True)
    nsoft = sum(st.get("soft_fail", 0) for st, dl, rp in results)
    if os.environ.get("VT_SOFT"):
        print(f"SOFT MODE (diagnostics, not a verification): leaves without a certifying dual: {nsoft} of "
              f"{sum(st['leaves'] for st, dl, rp in results)}")
        sys.exit(1)
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
