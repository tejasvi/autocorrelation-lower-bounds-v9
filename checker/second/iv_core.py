"""iv_core: exact core of a second verifier for the C1 window-bound certificates (V_n >= lam).

Written from the specification (docs/CERT_FORMAT.md, format 2, of the C1 release) and the mathematics of the C1
paper, without copying from the first checker or the search program.  Shared definitions, each taken from the
specification (section numbers of CERT_FORMAT.md):
  * the block tree and its preorder numbering, columns, column bounds, regions and their propagation (3);
  * the row semantics, the square-cut semantics and the validation ranges of row keys (4);
  * the record stream of a job (5), the Neumaier-Shcherbina bound and the completion of D records (6), and the
    partition rule (7); the canonical row list (4) that D records require.
Everything in this file is exact (fractions.Fraction); floats never enter a decision.
"""
from fractions import Fraction

ZERO = Fraction(0)
ONE = Fraction(1)
TMAX = Fraction(3)


class SpecError(ValueError):
    """Malformed or inadmissible certificate data."""


def is_int(v):
    return type(v) is int


def rational(v):
    """Exact rational from a JSON integer or a rational string 'p' / 'p/q' (no floats, no booleans)."""
    if is_int(v):
        return Fraction(v)
    if isinstance(v, str):
        s = v.strip()
        num, slash, den = s.partition('/')
        try:
            if slash:
                p, q = int(num), int(den)
                if q <= 0:
                    raise SpecError(f'bad rational {v!r}')
                return Fraction(p, q)
            return Fraction(int(num))
        except ValueError:
            raise SpecError(f'bad rational {v!r}')
    raise SpecError(f'not an integer or rational string: {v!r}')


def number(v):
    """Exact value of a dual entry (section 5, L/F records): a JSON number (a float means the exact value of the
    parsed IEEE double; it must be finite) or a rational string."""
    if type(v) is float:
        if v != v or v in (float('inf'), float('-inf')):
            raise SpecError(f'non-finite number {v!r}')
        return Fraction(v)
    return rational(v)


# ----------------------------------------------------------------------------------------------------------------
# block tree (section 3): balanced binary tree over bins 0..n-1, preorder numbering, children [lo, mid), [mid, hi)
class Blocks:
    def __init__(self, n):
        if not (is_int(n) and n >= 2):
            raise SpecError('n must be an integer >= 2')
        self.n = n
        lo, hi, parent, kids = [], [], [], []
        todo = [(0, n, -1)]
        while todo:
            a, b, par = todo.pop()
            me = len(lo)
            lo.append(a); hi.append(b); parent.append(par); kids.append([])
            if par >= 0:
                kids[par].append(me)          # the left child is always created before the right one
            if b - a > 1:
                m = (a + b) // 2
                todo.append((m, b, me))       # popped after the whole left subtree (preorder)
                todo.append((a, m, me))
        self.lo, self.hi, self.parent, self.kids = lo, hi, parent, kids
        self.nB = len(lo)
        if self.nB != 2 * n - 1:
            raise SpecError('block tree size')
        self.internal = [b for b in range(self.nB) if kids[b]]
        self.size = [hi[b] - lo[b] for b in range(self.nB)]
        self.leaf_of_bin = [None] * n
        for b in range(self.nB):
            if self.size[b] == 1:
                self.leaf_of_bin[lo[b]] = b

    def is_leaf(self, b):
        return self.size[b] == 1

    def pair(self, d, e):
        """canon_pair: the product column of blocks d and e."""
        if d > e:
            d, e = e, d
        if self.is_leaf(d) and self.is_leaf(e):
            i, j = self.lo[d], self.lo[e]
            if i > j:
                i, j = j, i
            return ('Z', i, j)
        return ('ZA', d, e)


# ----------------------------------------------------------------------------------------------------------------
# regions (section 3)
def propagate(T, L, U):
    """exact interval propagation of m_b = m_c1 + m_c2 and m_root = 1; returns (L, U) or None if empty."""
    L = list(L); U = list(U)
    L[0] = max(L[0], ONE); U[0] = min(U[0], ONE)
    for _sweep in range(64):
        moved = False
        for b in T.internal:
            c1, c2 = T.kids[b]
            Lb, Ub, L1, U1, L2, U2 = L[b], U[b], L[c1], U[c1], L[c2], U[c2]
            nb = (max(Lb, L1 + L2), min(Ub, U1 + U2),
                  max(L1, Lb - U2), min(U1, Ub - L2),
                  max(L2, Lb - U1), min(U2, Ub - L1))
            if nb != (Lb, Ub, L1, U1, L2, U2):
                moved = True
                L[b], U[b], L[c1], U[c1], L[c2], U[c2] = nb
        if not moved:
            break
    else:
        raise SpecError('propagation did not converge in 64 sweeps')
    for b in range(T.nB):
        if L[b] > U[b]:
            return None
    return L, U


def root_region(T):
    r = propagate(T, [ZERO] * T.nB, [ONE] * T.nB)
    if r is None:
        raise SpecError('empty root region')
    return r


def split(T, region, b, s, side):
    """child of the region at block b and value s (side 0: m_b <= s, side 1: m_b >= s); None if empty."""
    L, U = region
    if not (is_int(b) and 0 <= b < T.nB):
        raise SpecError(f'bad split block {b!r}')
    if side not in (0, 1) or type(side) is not int:
        raise SpecError(f'bad side {side!r}')
    if not (L[b] < s < U[b]):
        raise SpecError(f'split value {s} not inside ({L[b]}, {U[b]}) at block {b}')
    L = list(L); U = list(U)
    if side == 0:
        U[b] = s
    else:
        L[b] = s
    return propagate(T, L, U)


# ----------------------------------------------------------------------------------------------------------------
# rows (section 4)
class Rows:
    """Exact row semantics.  Static rows (all kinds except 'mc') are region independent and cached."""

    def __init__(self, T, rowkeys):
        self.T = T
        n = T.n
        self.keys = [self._validate(k) for k in rowkeys]
        self.static = {}
        for r, k in enumerate(self.keys):
            if k[0] != 'mc':
                self.static[r] = self._static_row(k)
        self.index = {k: r for r, k in enumerate(self.keys)}
        self.canonical = (self.keys == canonical_rowkeys(T))
        za = [r for r, k in enumerate(self.keys) if k[0] == 'ZA']
        self.za_order = sorted(za, key=lambda r: (-(T.size[self.keys[r][1]] + T.size[self.keys[r][2]]), r))

    # strict validation of a row key (section 4, last paragraph)
    def _validate(self, k):
        T = self.T; n = T.n
        if not (isinstance(k, (list, tuple)) and len(k) >= 1 and isinstance(k[0], str)):
            raise SpecError(f'malformed row key {k!r}')
        kind = k[0]; a = list(k[1:])
        if not all(is_int(x) for x in a):
            raise SpecError(f'non-integer in row key {k!r}')
        ok = False
        if kind == 'win':
            ok = len(a) == 2 and 0 <= a[0] <= a[1] <= 2 * n - 2
        elif kind in ('P', 'G'):
            ok = len(a) == 1 and 0 <= a[0] <= 2 * n - 2
        elif kind == 'tree':
            ok = len(a) == 1 and 0 <= a[0] < T.nB and not T.is_leaf(a[0])
        elif kind == 'ZA':
            ok = (len(a) == 3 and all(0 <= x < T.nB for x in a) and a[2] in (a[0], a[1]) and not T.is_leaf(a[2]))
        elif kind == 'rlt':
            ok = len(a) == 1 and 0 <= a[0] < n
        elif kind == 'sym':
            ok = len(a) == 0
        elif kind == 'mc':
            ok = len(a) == 3 and 0 <= a[0] < T.nB and 0 <= a[1] < T.nB and 0 <= a[2] <= 3
        if not ok:
            raise SpecError(f'invalid row key {k!r}')
        return (kind,) + tuple(a)

    def _static_row(self, k):
        T = self.T; n = T.n
        kind = k[0]
        ent = {}

        def add(col, v):
            ent[col] = ent.get(col, ZERO) + v
        if kind == 'win':
            c1, c2 = k[1], k[2]
            w = Fraction(2 * n, c2 - c1 + 2)
            add(('G', c2), w)
            if c1 > 0:
                add(('G', c1 - 1), -w)
            add(('t',), -ONE)
            return None, ZERO, ent
        if kind == 'P':
            c = k[1]
            add(('P', c), ONE)
            for i in range(n):
                j = c - i
                if i <= j < n:
                    add(('Z', i, j), -ONE if i == j else Fraction(-2))
            return ZERO, ZERO, ent
        if kind == 'G':
            c = k[1]
            add(('G', c), ONE); add(('P', c), -ONE)
            if c > 0:
                add(('G', c - 1), -ONE)
            return ZERO, ZERO, ent
        if kind == 'tree':
            b = k[1]
            c1, c2 = T.kids[b]
            add(('m', b), ONE); add(('m', c1), -ONE); add(('m', c2), -ONE)
            return ZERO, ZERO, ent
        if kind == 'ZA':
            D, E, s = k[1], k[2], k[3]
            s1, s2 = T.kids[s]
            add(T.pair(D, E), ONE)
            if D == E:
                add(T.pair(s1, s1), -ONE); add(T.pair(s1, s2), Fraction(-2)); add(T.pair(s2, s2), -ONE)
            else:
                o = E if s == D else D
                add(T.pair(s1, o), -ONE); add(T.pair(s2, o), -ONE)
            return ZERO, ZERO, ent
        if kind == 'rlt':
            i = k[1]
            for j in range(n):
                add(('Z', min(i, j), max(i, j)), ONE)
            add(('m', T.leaf_of_bin[i]), -ONE)
            return ZERO, ZERO, ent
        if kind == 'sym':
            for i in range(n):
                if 2 * i != n - 1:
                    add(('m', T.leaf_of_bin[i]), Fraction(2 * i - (n - 1)))
            return None, ZERO, ent
        raise SpecError(f'no static row for {k!r}')

    def mc_row(self, k, L, U):
        """McCormick row (section 4) for the region (L, U)."""
        T = self.T
        D, E, q = k[1], k[2], k[3]
        z = T.pair(D, E); mD = ('m', D); mE = ('m', E)
        LD, UD, LE, UE = L[D], U[D], L[E], U[E]
        if D == E:
            if q == 0:
                return None, LD * LD, {z: -ONE, mD: 2 * LD}
            if q == 1:
                return None, UD * UD, {z: -ONE, mD: 2 * UD}
            return None, -LD * UD, {z: ONE, mD: -(LD + UD)}
        if q == 0:
            return None, LD * LE, {z: -ONE, mD: LE, mE: LD}
        if q == 1:
            return None, UD * UE, {z: -ONE, mD: UE, mE: UD}
        if q == 2:
            return None, -LD * UE, {z: ONE, mD: -UE, mE: -LD}
        return None, -UD * LE, {z: ONE, mD: -LE, mE: -UD}

    def row(self, r, L, U):
        if r in self.static:
            return self.static[r]
        return self.mc_row(self.keys[r], L, U)


def square_cut(T, key):
    """square cut (section 4): validated key -> (lo, up, ent) with lo = -v0^2, up = None."""
    if not (isinstance(key, list) and len(key) == 3 and key[0] == 'sq' and is_int(key[1]) and isinstance(key[2], list)
            and len(key[2]) >= 1):
        raise SpecError(f'bad square-cut key {key!r}')
    v0 = key[1]
    seen = set(); terms = []
    for t in key[2]:
        if not (isinstance(t, list) and len(t) == 2 and is_int(t[0]) and is_int(t[1])):
            raise SpecError(f'bad square-cut term {t!r}')
        B, v = t
        if not (1 <= B < T.nB) or B in seen:
            raise SpecError(f'bad square-cut block {t!r}')
        seen.add(B)
        if v != 0:
            terms.append((B, v))
    if not terms:
        raise SpecError('square cut without a nonzero coefficient')
    ent = {}

    def add(col, v):
        ent[col] = ent.get(col, ZERO) + v
    for a, (Ba, va) in enumerate(terms):
        add(T.pair(Ba, Ba), Fraction(va * va))
        for Bc, vc in terms[a + 1:]:
            add(T.pair(Ba, Bc), Fraction(2 * va * vc))
        add(('m', Ba), Fraction(2 * v0 * va))
    return Fraction(-v0 * v0), None, ent


def canonical_rowkeys(T):
    """the canonical row list of section 4 (required for D records), in order."""
    n = T.n; out = []
    for c1 in range(2 * n - 1):
        for c2 in range(c1, 2 * n - 1):
            out.append(('win', c1, c2))
    out += [('P', c) for c in range(2 * n - 1)]
    out += [('G', c) for c in range(2 * n - 1)]
    out += [('tree', b) for b in sorted(T.internal)]
    pairs = [(D, E) for D in range(1, T.nB) for E in range(D, T.nB)]
    for D, E in pairs:
        if T.is_leaf(D) and T.is_leaf(E):
            continue
        if T.is_leaf(D):
            s = E
        elif T.is_leaf(E):
            s = D
        else:
            s = D if T.size[D] >= T.size[E] else E
        out.append(('ZA', D, E, s))
    out += [('rlt', i) for i in range(n)]
    out.append(('sym',))
    for D, E in pairs:
        for q in range(4):
            out.append(('mc', D, E, q))
    return out


def _admissible(lo, up, y):
    return y != 0 and not (y > 0 and lo is None) and not (y < 0 and up is None)


def complete_d(T, rows, region, row_duals, cut_duals):
    """completion of a D record (section 6), exact: with C(col) = sum of y_r a_{r,col} over the listed rows and cuts of
    admissible sign, returns [(row index, dual)] for every G, P and ZA row such that the reduced cost of every G, P and
    ZA column is 0:  y[G_c] = y[G_{c+1}] - C(G_c) (c = 2n-2 .. 0, y[G_{2n-1}] = 0);  y[P_c] = y[G_c] - C(P_c);  ZA rows in
    decreasing size(D) + size(E), ties by increasing row index: y = -C([D E]) - sum over the ZA rows r' already done that
    contain [D E] as a child term of coef(r', [D E]) y[r'].  Requires rows.keys to be the canonical list."""
    L, U = region
    Cc = {}
    for r, y in row_duals:
        lo, up, ent = rows.row(r, L, U)
        if _admissible(lo, up, y):
            for col, a in ent.items():
                Cc[col] = Cc.get(col, ZERO) + y * a
    for (lo, up, ent), y in cut_duals:
        if _admissible(lo, up, y):
            for col, a in ent.items():
                Cc[col] = Cc.get(col, ZERO) + y * a
    n = T.n; idx = rows.index; out = []
    yG = ZERO
    for c in range(2 * n - 2, -1, -1):
        yG = yG - Cc.get(('G', c), ZERO)
        out.append((idx[('G', c)], yG))
        out.append((idx[('P', c)], yG - Cc.get(('P', c), ZERO)))
    child = {}
    for r in rows.za_order:
        D, E, s = rows.keys[r][1:]
        col = T.pair(D, E)
        y = -Cc.get(col, ZERO) - child.get(col, ZERO)
        out.append((r, y))
        if y:
            for c2, a in rows.static[r][2].items():
                if c2 != col:
                    child[c2] = child.get(c2, ZERO) + a * y
    return out


def col_bounds(col, L, U):
    kind = col[0]
    if kind == 'm':
        return L[col[1]], U[col[1]]
    if kind in ('Z', 'ZA', 'P', 'G'):
        return ZERO, ONE
    if kind == 't':
        return ZERO, TMAX
    raise SpecError(f'unknown column {col!r}')


def ns_bound(rows, region, row_duals, cut_duals, objective=True):
    """Neumaier-Shcherbina bound (section 6), exact.  row_duals: [(row index, Fraction)],
    cut_duals: [((lo, up, ent), Fraction)].  Rows with an inadmissible sign are dropped (as y = 0)."""
    L, U = region
    red = {}
    rowpart = ZERO
    items = [(rows.row(r, L, U), y) for r, y in row_duals] + list(cut_duals)
    for (lo, up, ent), y in items:
        if y == 0:
            continue
        if y > 0:
            if lo is None:
                continue
            rowpart += y * lo
        else:
            if up is None:
                continue
            rowpart += y * up
        for col, a in ent.items():
            red[col] = red.get(col, ZERO) - y * a
    if objective:
        red[('t',)] = red.get(('t',), ZERO) + ONE
    colpart = ZERO
    for col, rc in red.items():
        if rc:
            lb, ub = col_bounds(col, L, U)
            colpart += min(rc * lb, rc * ub)
    return rowpart + colpart
