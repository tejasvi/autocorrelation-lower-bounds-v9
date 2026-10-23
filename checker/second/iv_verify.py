"""iv_verify: second verifier for tree-only certificates of V_n >= lam (C1 window bound).
v5.1 = v5 (501d24f1) with one change: job headers are parsed without rejecting non-standard JSON constants in their
ignored keys (loads_header); n, lam and path are validated as before, and records are parsed strictly as before.

Claim (CERT_FORMAT.md section 1): for every p in Delta_n with sum_i (2i-(n-1)) p_i <= 0,
    F(p) = max_{c1<=c2} 2n/(c2-c1+2) sum_{c1<=i+j<=c2} p_i p_j >= lam;  reversal covers the other half-space.

Certificate: CERTDIR/meta.json (n, lam, rowkeys) and CERTDIR/jobs/*.jsonl.gz (CERT_FORMAT.md sections 2 and 5).
Supported records (TREE_FORMAT.md section 2, plus D): I (split), S (delegation), K (square-cut definition), U (leaf
without data), T (leaf with suggested cut ids), L (explicit leaf, cut list A), F (Farkas leaf) and, new in v5, D
(compressed leaf, CERT_FORMAT.md section 5) in its 5- and 6-field forms only (the subset of DRECORD_SPEC.txt; the
7-field form with cut list B, E and C records reject the certificate).  A D record requires meta.rowkeys to be the
canonical row list of section 4.

What is trusted (all exact, fractions.Fraction, written from the specifications): row-key validation, rows,
square cuts, regions and propagation (iv_core), the record stack of each job, the partition rule of section 7, and
the Neumaier-Shcherbina bound (iv_core.ns_bound).  A U/T leaf is accepted only if the exact bound of some dual vector
over the rows of meta.rowkeys and square cuts of this program's own choosing is >= lam, or if an exact Farkas test
shows that the leaf's LP is infeasible.  An L leaf is accepted if its stored dual passes the same exact test, an F
leaf if its stored ray does; a D leaf if its stored dual, completed on the G, P and ZA rows by this program's own
exact completion (section 6, iv_core.complete_d), passes it; otherwise the leaf is certified like a U leaf.  Strict: a
leaf that cannot be certified rejects the certificate.

Own-LP re-solves of D leaves (a cross-check by this program's own LP, reported, not needed for acceptance): --d-own-p P --d-own-R HEX
selects D leaves by SHA256(SHA256("C1-D-ownLP-v1" || R) || job || "/" || k) < P * 2^64 (R fixed in advance);
--own-lp-list FILE adds listed leaves ("jobname k" lines, e.g. the lowest-margin 0.1% from --margins-out files).
A selected leaf is also certified by this program's own LP, whatever its stored dual gives; shortfalls are listed.

What is not trusted (it only proposes duals, rays and cut keys): the HiGHS oracle in iv_lp.  Its strategy (lazy window,
McCormick and cut rows, Devex pricing, objective bound lam + 1e-6, 3x3 moment-matrix separation with keys rounded at
2^-20) follows the description in TREE_FORMAT.md section 4; the code is this program's own.

Runs: a structure pre-pass (records, regions, delegations, and the partition when the whole certificate is read) and
then the leaf pass, over a process pool.  --shard I/K verifies every K-th job file (--out required for combining);
--combine OUT... accepts the shard outputs only if all were written by this exact verifier (sha256 of its three files)
for this meta.json, cover every job file exactly once with unchanged contents (sha256), have no failure, and pass the
partition check.

Sampled mode (SAMPLED_VERIFICATION.md; NOT a full check, never prints VERIFIED): --sample-p P --sample-R HEX
[--thin-jobs FILE] [--thin-leaves FILE].  The structure pass and the partition stay complete; only the selected leaves
(part A lists, Bernoulli(P) by SHA256(seed || job || k), and each job's min-hash leaf) are certified, with
seed = SHA256("C1-tree-sample-v1" || H || R) and H the certificate hash (meta.json and every job file's sha256).

Usage: python3 -I iv_verify.py CERTDIR [--workers K] [--failfast] [--out FILE] [--shard I/K] [--combine OUT ...]
                                       [--sample N (first N jobs only, leaf-level test)] [--oracle lazy|full]
                                       [--sample-p P --sample-R HEX [--thin-jobs F] [--thin-leaves F]]
                                       [--d-own-p P --d-own-R HEX] [--own-lp-list FILE] [--margins-out FILE.npz]
"""
import sys, os, io, json, gzip, zlib, glob, time, hashlib, argparse
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iv_core as C
import iv_lp as P

if not __debug__:
    raise SystemExit('iv_verify.py must not run with python -O')

W = {}          # per-process state


def load_meta(certdir):
    meta = json.loads(open(os.path.join(certdir, 'meta.json')).read(), parse_constant=_no_constant)
    if not isinstance(meta, dict):
        raise C.SpecError('meta.json is not an object')
    n = meta.get('n')
    if not (C.is_int(n) and n >= 2):
        raise C.SpecError('bad n')
    if not isinstance(meta.get('lam'), str):
        raise C.SpecError('lam must be a rational string')
    lam = C.rational(meta['lam'])
    if not (0 < lam <= C.TMAX):
        raise C.SpecError('lam must satisfy 0 < lam <= 3')
    if not isinstance(meta.get('rowkeys'), list):
        raise C.SpecError('rowkeys missing')
    return n, lam, meta['rowkeys']


def init_worker(certdir, rounds, cap, maxage, kind='lazy', sample=None, dsel=None, ownlist=None):
    n, lam, rowkeys = load_meta(certdir)
    T = C.Blocks(n)
    rows = C.Rows(T, rowkeys)
    if maxage is None:
        maxage = 8 if kind == 'lazy' else 60
    W.update(certdir=certdir, n=n, lam=lam, T=T, rows=rows, orc=None, rounds=rounds, cap=cap, maxage=maxage,
             lamf=float(lam), kind=kind, nfarkas=0, sample=sample, dsel=dsel, ownlist=ownlist or set())


def leaf_hash(seed, job, k):
    """64-bit pseudo-random value of leaf k of job file `job` (SAMPLED_VERIFICATION.md section 2)."""
    return int.from_bytes(hashlib.sha256(seed + job.encode() + b'/' + str(k).encode()).digest()[:8], 'big')


def oracle():
    if W['orc'] is None:
        if W['kind'] == 'lazy':
            W['orc'] = P.LazyOracle(W['T'], W['rows'], W['lam'], maxage=W['maxage'])
        else:
            W['orc'] = P.Oracle(W['T'], W['rows'])
        W['age'] = []
    return W['orc']


def certify(region, hint_keys=()):
    """returns (ok, best exact bound or None, LP solves beyond the first).  A leaf that the lazy oracle cannot close
    gets a second chance with the full-LP oracle (speed only; acceptance is the same exact test)."""
    if W['kind'] == 'lazy':
        res = certify_lazy(region, hint_keys)
        if res[0]:
            return res
        W['second'] = W.get('second', 0) + 1
        if W.get('orc_full') is None:
            W['orc_full'] = P.Oracle(W['T'], W['rows']); W['age_full'] = []
        orc, age = W['orc'], W['age']
        W['orc'], W['age'], W['kind'] = W['orc_full'], W['age_full'], 'full'
        try:
            res2 = certify_full(region, hint_keys)
        finally:
            W['orc_full'], W['age_full'] = W['orc'], W['age']
            W['orc'], W['age'], W['kind'] = orc, age, 'lazy'
        return res2 if res2[0] else (False, max((b for b in (res[1], res2[1]) if b is not None), default=None),
                                     res[2] + res2[2])
    return certify_full(region, hint_keys)


def certify_lazy(region, hint_keys=()):
    """row generation (window and McCormick rows), then square-cut rounds; every acceptance is an exact test."""
    orc = oracle(); lam = W['lam']
    orc.set_region(region)
    if hint_keys:
        orc.add_cuts(list(hint_keys))
    best = None; seps = 0
    for rnd in range(4 * W['rounds'] + 40):
        res = orc.solve()
        if res is None:
            break
        if isinstance(res, str):                    # the relaxation is infeasible: verify a Farkas ray exactly
            ray = orc.farkas()
            if ray is not None and orc.exact_farkas(region, ray) > 0:
                W['nfarkas'] += 1
                orc.end_leaf(None); orc.early_stop(True)
                return True, lam, rnd
            break
        obj, x, y = res
        if obj >= W['lamf'] - 1e-9:
            lb = orc.exact_bound(region, y)
            best = lb if best is None or lb > best else best
            if lb >= lam:
                orc.end_leaf(y); orc.early_stop(True)
                return True, lb, rnd
            orc.early_stop(False)                   # the early dual was not good enough: converge for this leaf
        add = orc.violated(x)
        if add:
            orc.add_rows(add)
            continue
        seps += 1
        keys = orc.separate(x) if seps <= W['rounds'] else []
        if not keys or orc.add_cuts(keys) == 0:
            break
    orc.end_leaf(None); orc.early_stop(True)
    return False, best, rnd


def certify_full(region, hint_keys=()):
    orc = oracle(); lam = W['lam']
    orc.set_region(region)
    if hint_keys:
        orc.add_cuts(list(hint_keys))
    best = None
    for rnd in range(W['rounds'] + 1):
        res = orc.solve()
        if res is None:
            break
        if isinstance(res, str):                    # LP infeasible: verify a Farkas certificate exactly
            ray = orc.farkas()
            if ray is not None and P.exact_farkas_value(orc, region, ray) > 0:
                W['nfarkas'] += 1
                manage_pool(orc, None)
                return True, lam, rnd
            break
        obj, x, y = res
        if obj >= W['lamf'] - 1e-9:
            lb = P.exact_leaf_bound(orc, region, y)
            best = lb if best is None or lb > best else best
            if lb >= lam:
                manage_pool(orc, y)
                return True, lb, rnd
        keys = orc.separate(x)
        if not keys or orc.add_cuts(keys) == 0:
            break
    manage_pool(orc, None)
    return False, best, W['rounds']


def manage_pool(orc, y):
    """cut pool policy (untrusted, only affects speed): reset the age of cuts with dual weight, drop old ones."""
    age = W['age']
    while len(age) < len(orc.cuts):
        age.append(0)
    nb = orc.nrow
    for i in range(len(orc.cuts)):
        if y is not None and y[nb + i] != 0.0:
            age[i] = 0
        else:
            age[i] += 1
    drop = [i for i in range(len(orc.cuts)) if age[i] > W['maxage']]
    if len(orc.cuts) - len(drop) > W['cap']:
        rest = sorted((i for i in range(len(orc.cuts)) if i not in set(drop)), key=lambda i: -age[i])
        drop += rest[: len(orc.cuts) - len(drop) - W['cap']]
    if drop:
        dset = set(drop)
        orc.drop_cuts(drop)
        W['age'] = [a for i, a in enumerate(age) if i not in dset]


def _no_constant(name):
    raise C.SpecError(f'JSON constant {name} is not allowed')


def loads(line):
    return json.loads(line, parse_constant=_no_constant)


def loads_header(line):
    """job header (section 5): only n, lam and path are read and they are validated strictly below; the other keys
    are ignored, so a non-standard JSON constant inside them (the n=39 writer stores "minlb": Infinity in the header
    statistics of jobs without leaves) is tolerated (v5.1).  Records keep the strict parser."""
    return json.loads(line)


def cut_list_a(lst, cuts):
    """cut list A (section 5): non-empty list of [ref, value]; ref a K-defined cut id (pairwise distinct) or an inline
    square-cut key; value a JSON number or rational string (exact)."""
    T = W['T']
    if not (isinstance(lst, list) and lst):
        raise C.SpecError('bad cut list A')
    refs = set(); out = []
    for e in lst:
        if not (isinstance(e, list) and len(e) == 2):
            raise C.SpecError('bad cut list A entry')
        ref, v = e
        if C.is_int(ref):
            if ref not in cuts or ref in refs:
                raise C.SpecError('bad cut reference in cut list A')
            refs.add(ref)
            key = cuts[ref]
        else:
            key = ref
        out.append((C.square_cut(T, key), C.number(v)))
    return out


def d_leaf(rec, reg, cuts, st):
    """D record, 5- or 6-field form (section 5): y[idx[j]] = ints[j] / 2^F on rows that are not P, G or ZA rows, cut
    list A; this program's completion of the G, P and ZA duals (section 6) and the exact bound.  If the stored dual
    does not close the region, the region is certified like a U leaf.  Returns (ok, bound, rounds, stored bound)."""
    T, rows, lam = W['T'], W['rows'], W['lam']
    if not rows.canonical:
        raise C.SpecError('D record, but meta.rowkeys is not the canonical row list (section 4)')
    if len(rec) not in (5, 6):
        raise C.SpecError('bad D record: only the 5- and 6-field forms are accepted')
    info, F, idx, ints = rec[1], rec[2], rec[3], rec[4]
    if type(info) not in (int, float):
        raise C.SpecError('bad D record: lb is not a number')
    if not (C.is_int(F) and 0 <= F <= 1024):
        raise C.SpecError(f'bad D record: F = {F!r}')
    if not (isinstance(idx, list) and isinstance(ints, list) and len(idx) == len(ints)):
        raise C.SpecError('bad D record: idx and ints')
    nrow = len(rows.keys); seen = set(); row_duals = []; den = 1 << F
    for k, v in zip(idx, ints):
        if not (C.is_int(k) and 0 <= k < nrow) or k in seen:
            raise C.SpecError(f'bad D row index {k!r}')
        if rows.keys[k][0] in ('P', 'G', 'ZA'):
            raise C.SpecError('a D record lists a P, G or ZA row')
        if not C.is_int(v):
            raise C.SpecError(f'bad D dual {v!r}')
        seen.add(k)
        row_duals.append((k, Fraction(v, den)))
    cut_duals = cut_list_a(rec[5], cuts) if len(rec) == 6 else []
    comp = C.complete_d(T, rows, reg, row_duals, cut_duals)
    lb = C.ns_bound(rows, reg, row_duals + comp, cut_duals)
    if lb >= lam:
        st['stored'] += 1
        return True, lb, 0, lb
    st['fallback'] += 1
    ok, lb2, rnd = certify(reg)
    return ok, lb2, rnd, lb


def explicit_leaf(rec, reg, cuts, st):
    """L and F records (section 5): the stored dual is evaluated exactly (section 6, no completion); if it does not
    close the region, the region is certified like a U leaf (any admissible dual is a proof).  Returns
    (ok, bound, rounds); the bound reported for an F leaf closed by its stored ray is lam."""
    T, rows, lam = W['T'], W['rows'], W['lam']
    nrow = len(rows.keys)
    if rec[0] == 'L':
        if len(rec) not in (4, 5):
            raise C.SpecError('bad L record')
        idx, vals = rec[2], rec[3]
    else:
        if len(rec) != 3:
            raise C.SpecError('bad F record')
        idx, vals = rec[1], rec[2]
    if not (isinstance(idx, list) and isinstance(vals, list) and len(idx) == len(vals)):
        raise C.SpecError(f'bad {rec[0]} record')
    row_duals = []
    for k, v in zip(idx, vals):
        if not (C.is_int(k) and 0 <= k < nrow):
            raise C.SpecError(f'bad row index {k!r}')
        row_duals.append((k, C.number(v)))
    cut_duals = cut_list_a(rec[4], cuts) if rec[0] == 'L' and len(rec) == 5 else []
    if rec[0] == 'L':
        lb = C.ns_bound(rows, reg, row_duals, cut_duals)
        if lb >= lam:
            st['stored'] += 1
            return True, lb, 0
    else:
        if C.ns_bound(rows, reg, row_duals, [], objective=False) > 0:
            st['stored'] += 1
            return True, lam, 0
    st['fallback'] += 1
    return certify(reg)


def path_key(path):
    return tuple((b, str(s), side) for b, s, side in path)


def structure_job(fname):
    """pre-pass: records, regions and delegations only (no leaf is certified)."""
    return verify_job(fname, leaves=False)


def verify_job(fname, leaves=True):
    T, lam = W['T'], W['lam']
    st = dict(file=os.path.basename(fname), sha256=None, leaves=0, internal=0, empty=0, delegated=0, rounds=0, stored=0,
              fallback=0, second=0, farkas=0, sampled=0, skipped=0, minlb=None, fail=None, root=None, deleg=[], secs=0.0,
              dleaves=0, own_try=0, own_ok=0, own_short=[], own_minlb=None, dmk=[], dmv=[])
    t0 = time.time(); second0 = W.get('second', 0); farkas0 = W['nfarkas']
    smp = W['sample'] if leaves else None
    job = os.path.basename(fname); kleaf = -1
    cand = [None, None]                         # [min leaf hash so far, its deferred leaf (or None if certified)]

    def selected(k):
        """sampling decision for leaf k (always True for a full check); updates the part-C candidate."""
        if smp is None:
            return True, None
        h = leaf_hash(smp['seed'], job, k)
        sel = (job in smp['thin_jobs'] or (job, k) in smp['thin_leaves'] or h * smp['pden'] < smp['pnum'] << 64)
        return sel, h

    def certify_leaf(kind, rec, reg, pth, hints, cuts, k):
        if kind in ('U', 'T'):
            ok, lb, rnd = certify(reg, hints)
        elif kind == 'D':
            st['dleaves'] += 1
            ok, lb, rnd, slb = d_leaf(rec, reg, cuts, st)
            if slb >= lam:
                st['dmk'].append(k); st['dmv'].append(float(slb - lam))
            ds = W['dsel']
            if (ds is not None and leaf_hash(ds['seed'], job, k) * ds['pden'] < ds['pnum'] << 64) or (job, k) in W['ownlist']:
                st['own_try'] += 1
                ok2, lb2, rnd2 = certify(reg)
                st['rounds'] += rnd2
                if ok2:
                    st['own_ok'] += 1
                    st['own_minlb'] = lb2 if st['own_minlb'] is None or lb2 < st['own_minlb'] else st['own_minlb']
                else:
                    st['own_short'].append([k, None if lb2 is None else str(lb2)])
        else:
            ok, lb, rnd = explicit_leaf(rec, reg, cuts, st)
        st['rounds'] += rnd
        if not ok:
            raise C.SpecError(f'{kind} leaf not certified (best exact bound {None if lb is None else float(lb)}) at path {path_key(pth)}')
        st['sampled'] += 1
        st['minlb'] = lb if st['minlb'] is None or lb < st['minlb'] else st['minlb']

    def leaf(kind, rec, reg, pth, hints, cuts):
        nonlocal kleaf
        kleaf += 1
        st['leaves'] += 1
        if not leaves:
            return
        sel, h = selected(kleaf)
        if sel:
            certify_leaf(kind, rec, reg, pth, hints, cuts, kleaf)
            if h is not None and (cand[0] is None or h < cand[0]):
                cand[0], cand[1] = h, None
        else:
            st['skipped'] += 1
            if cand[0] is None or h < cand[0]:
                cand[0], cand[1] = h, (kind, rec, reg, pth, hints, dict(cuts), kleaf)
    try:
        raw = open(fname, 'rb').read()
        st['sha256'] = hashlib.sha256(raw).hexdigest()
        with io.TextIOWrapper(gzip.GzipFile(fileobj=io.BytesIO(raw)), encoding='utf-8') as fh:
            head = loads_header(fh.readline())
            if not isinstance(head, dict):
                raise C.SpecError('bad job header')
            if not C.is_int(head.get('n')) or head['n'] != W['n'] or not isinstance(head.get('lam'), str) \
                    or C.rational(head['lam']) != lam:
                raise C.SpecError('job header n/lam differ from meta.json')
            if not isinstance(head.get('path'), list):
                raise C.SpecError('job header without a path')
            path = []
            region = C.root_region(T)
            for e in head['path']:
                if not (isinstance(e, list) and len(e) == 3):
                    raise C.SpecError('bad header path entry')
                if not isinstance(e[1], str):
                    raise C.SpecError('path value must be a rational string')
                b, s, side = e[0], C.rational(e[1]), e[2]
                region = C.split(T, region, b, s, side)
                if region is None:
                    raise C.SpecError('empty job root region')
                path.append((b, s, side))
            st['root'] = path_key(path)
            stack = [(region, tuple(path))]
            cuts = {}
            for line in fh:
                rec = loads(line)
                if not (isinstance(rec, list) and rec and isinstance(rec[0], str)):
                    raise C.SpecError('bad record')
                kind = rec[0]
                if kind == 'K':
                    if len(rec) != 3 or not C.is_int(rec[1]) or rec[1] in cuts:
                        raise C.SpecError('bad K record')
                    C.square_cut(T, rec[2])
                    cuts[rec[1]] = rec[2]
                    continue
                if not stack:
                    raise C.SpecError('record without a node (empty stack)')
                reg, pth = stack.pop()
                if kind == 'I':
                    if len(rec) != 3 or not C.is_int(rec[1]) or not isinstance(rec[2], str):
                        raise C.SpecError('bad I record')
                    b, s = rec[1], C.rational(rec[2])
                    st['internal'] += 1
                    kids = []
                    for side in (0, 1):
                        ch = C.split(T, reg, b, s, side)
                        if ch is None:
                            st['empty'] += 1
                        else:
                            kids.append((ch, pth + ((b, s, side),)))
                    stack.extend(kids)              # child 0 pushed first, child 1 processed next
                elif kind == 'S':
                    if len(rec) != 1:
                        raise C.SpecError('bad S record')
                    st['delegated'] += 1
                    st['deleg'].append(path_key(pth))
                elif kind in ('U', 'T'):
                    hints = []
                    if kind == 'U':
                        if len(rec) != 1:
                            raise C.SpecError('bad U record')
                    else:
                        if len(rec) not in (1, 2) or (len(rec) == 2 and not (isinstance(rec[1], list) and all(C.is_int(c) for c in rec[1]))):
                            raise C.SpecError('bad T record')
                        ids = rec[1] if len(rec) == 2 else []
                        if any(c not in cuts for c in ids):
                            raise C.SpecError('undefined cut id')
                        hints = [cuts[c] for c in ids]
                    leaf(kind, rec, reg, pth, hints, cuts)
                elif kind in ('L', 'F', 'D'):
                    leaf(kind, rec, reg, pth, [], cuts)
                else:
                    raise C.SpecError(f'unsupported record kind {kind!r}')
            if stack:
                raise C.SpecError(f'{len(stack)} nodes without records')
            if cand[1] is not None:                 # part C: the job's min-hash leaf, deferred to the end
                kind, rec, reg, pth, hints, cuts, kc = cand[1]
                st['skipped'] -= 1
                certify_leaf(kind, rec, reg, pth, hints, cuts, kc)
    except (C.SpecError, ValueError, KeyError, TypeError, OverflowError, json.JSONDecodeError, OSError, EOFError,
            gzip.BadGzipFile, zlib.error, UnicodeDecodeError) as ex:
        st['fail'] = f'{type(ex).__name__}: {ex}'
    st['secs'] = time.time() - t0
    st['second'] = W.get('second', 0) - second0
    st['farkas'] = W['nfarkas'] - farkas0
    if st['minlb'] is not None:
        st['minlb'] = str(st['minlb'])
    if st['own_minlb'] is not None:
        st['own_minlb'] = str(st['own_minlb'])
    return st


def partition_check(results):
    roots = {}
    for r in results:
        if r['root'] in roots:
            raise C.SpecError('two jobs with the same root path')
        roots[r['root']] = r
    deleg = [d for r in results for d in r['deleg']]
    expected = [()] + deleg
    if len(set(expected)) != len(expected):
        raise C.SpecError('a region was delegated twice')
    if set(expected) != set(roots):
        raise C.SpecError(f'job set mismatch: {len(set(expected) - set(roots))} missing, {len(set(roots) - set(expected))} orphans')
    seen = set(); todo = [()]
    while todo:
        k = todo.pop()
        if k in seen:
            raise C.SpecError('cycle in delegations')
        seen.add(k)
        todo.extend(roots[k]['deleg'])
    if seen != set(roots):
        raise C.SpecError('unreachable jobs')


def as_key(v):
    return tuple((b, x, side) for b, x, side in v)


def certificate_hash(certdir_meta, allfiles):
    """H = SHA256(meta.json || sorted lines 'name sha256(file)'), the certificate hash of SAMPLED_VERIFICATION.md."""
    lines = sorted(f'{os.path.basename(f)} {hashlib.sha256(open(f, "rb").read()).hexdigest()}\n' for f in allfiles)
    return hashlib.sha256(open(certdir_meta, 'rb').read() + ''.join(lines).encode()).hexdigest()


def sampling_config(a, allfiles):
    """(config for the workers or None, printable description or None)."""
    if a.sample_p is None:
        if a.sample_R or a.thin_jobs or a.thin_leaves:
            sys.exit('--sample-R/--thin-* need --sample-p')
        return None, None
    p = C.rational(a.sample_p)
    if not (0 <= p <= 1) or not a.sample_R:
        sys.exit('--sample-p must be in [0, 1] and --sample-R is required')
    R = bytes.fromhex(a.sample_R)
    H = certificate_hash(os.path.join(a.certdir, 'meta.json'), allfiles)
    seed = hashlib.sha256(b'C1-tree-sample-v1' + bytes.fromhex(H) + R).digest()
    thin_jobs, thin_leaves, tj, tl = set(), set(), None, None
    if a.thin_jobs:
        raw = open(a.thin_jobs, 'rb').read(); tj = hashlib.sha256(raw).hexdigest()
        thin_jobs = set(x.strip() for x in raw.decode().split('\n') if x.strip())
    if a.thin_leaves:
        raw = open(a.thin_leaves, 'rb').read(); tl = hashlib.sha256(raw).hexdigest()
        for x in raw.decode().split('\n'):
            if x.strip():
                nm, k = x.split(); thin_leaves.add((nm, int(k)))
    info = dict(p=str(p), H=H, R=a.sample_R.lower(), seed=seed.hex(), thin_jobs=tj, n_thin_jobs=len(thin_jobs),
                thin_leaves=tl, n_thin_leaves=len(thin_leaves))
    cfg = dict(seed=seed, pnum=p.numerator, pden=p.denominator, thin_jobs=thin_jobs, thin_leaves=thin_leaves)
    return cfg, info


def own_config(a):
    """(dsel for the workers or None, set of listed (job, k), printable description or None)."""
    dsel = None; ownlist = set(); info = {}
    if a.d_own_p is not None:
        p = C.rational(a.d_own_p)
        if not (0 <= p <= 1) or not a.d_own_R:
            sys.exit('--d-own-p must be in [0, 1] and --d-own-R is required')
        seed = hashlib.sha256(b'C1-D-ownLP-v1' + bytes.fromhex(a.d_own_R)).digest()
        dsel = dict(seed=seed, pnum=p.numerator, pden=p.denominator)
        info.update(p=str(p), R=a.d_own_R.lower(), seed=seed.hex())
    if a.own_lp_list:
        raw = open(a.own_lp_list, 'rb').read()
        for x in raw.decode().split('\n'):
            if x.strip():
                nm, k = x.split(); ownlist.add((nm, int(k)))
        info.update(list=hashlib.sha256(raw).hexdigest(), n_list=len(ownlist))
    return dsel, ownlist, (info or None)


def own_report(results):
    t = sum(r['own_try'] for r in results); ok = sum(r['own_ok'] for r in results)
    short = [(r['file'], k, lb) for r in results for k, lb in r['own_short']]
    m = [Fraction(r['own_minlb']) for r in results if r['own_minlb'] is not None]
    return (f'own-LP re-solves of D leaves: {ok} of {t} certified by this program\'s own LP (min own bound '
            f'{float(min(m)) if m else None}); {len(short)} shortfalls (those leaves stand on their stored duals)'
            + (f', e.g. {short[:3]}' if short else ''))


def combine(outs, allfiles, n, lam, vh, mh, sinfo=None, oinfo=None):
    """Accept the shard outputs only if they were written by this verifier for this meta.json, cover every job file
    of the certificate exactly once with the current file contents, contain no failure, and pass the partition check."""
    byname = {}
    for o in outs:
        with open(o) as fh:
            head = json.loads(fh.readline())
            if head.get('verifier') != vh or head.get('meta') != mh or head.get('n') != n or head.get('lam') != str(lam):
                print(f'NOT VERIFIED: {o} was written by another verifier version or for another meta.json')
                return 1
            if not head.get('complete') or head.get('sample'):
                print(f'NOT VERIFIED: {o} is incomplete or a sample')
                return 1
            if head.get('sampling') != sinfo:
                print(f'NOT VERIFIED: {o} was run with other sampling settings ({head.get("sampling")})')
                return 1
            if head.get('own_lp') != oinfo:
                print(f'NOT VERIFIED: {o} was run with other own-LP settings ({head.get("own_lp")})')
                return 1
            cnt = 0
            for line in fh:
                r = json.loads(line); cnt += 1
                if r['file'] in byname:
                    print(f'NOT VERIFIED: job {r["file"]} appears twice')
                    return 1
                r['root'] = as_key(r['root']) if r['root'] is not None else None
                r['deleg'] = [as_key(d) for d in r['deleg']]
                byname[r['file']] = r
            if cnt != head.get('jobs'):
                print(f'NOT VERIFIED: {o} is truncated')
                return 1
    names = {os.path.basename(f): f for f in allfiles}
    if set(byname) != set(names):
        print(f'NOT VERIFIED: shard outputs cover {len(set(byname) & set(names))} of {len(names)} job files '
              f'({len(set(byname) - set(names))} unknown)')
        return 1
    for nm, f in names.items():
        if hashlib.sha256(open(f, 'rb').read()).hexdigest() != byname[nm]['sha256']:
            print(f'NOT VERIFIED: job file {nm} changed since it was verified')
            return 1
    results = list(byname.values())
    fails = [r for r in results if r['fail']]
    if fails:
        print(f'NOT VERIFIED: {len(fails)} jobs failed, e.g. {fails[0]["file"]}: {fails[0]["fail"]}')
        return 1
    tot = {k: sum(r[k] for r in results) for k in ('leaves', 'internal', 'empty', 'delegated', 'rounds', 'stored', 'fallback', 'second', 'farkas', 'sampled', 'skipped', 'dleaves')}
    lbs = [Fraction(r['minlb']) for r in results if r['minlb'] is not None]
    print(f'{tot}; min exact leaf bound {float(min(lbs)) if lbs else None}')
    print(own_report(results))
    try:
        partition_check(results)
    except C.SpecError as ex:
        print(f'NOT VERIFIED: partition: {ex}')
        return 1
    if sinfo:
        print(f'SAMPLED-OK (not a full check): structure and partition complete for {tot["leaves"]} leaves; '
              f'{tot["sampled"]} leaves certified exactly, 0 failures; combined from {len(outs)} shard outputs; {sinfo}')
        return 0
    print(f'VERIFIED: V_{n} >= {lam} ({float(lam)}); jobs={len(results)} (combined from {len(outs)} shard outputs)')
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certdir')
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--rounds', type=int, default=30)
    ap.add_argument('--cap', type=int, default=800)
    ap.add_argument('--maxage', type=int, default=None, help='leaves without dual weight before a lazy row or cut is '
                    'dropped (default 8 for the lazy oracle, 60 for the full one)')
    ap.add_argument('--sample', type=int, default=0, help='verify only N jobs (leaf-level test; no partition check)')
    ap.add_argument('--out', default=None, help='write per-job results (JSON lines)')
    ap.add_argument('--failfast', action='store_true', help='stop at the first failing job (for tamper tests)')
    ap.add_argument('--oracle', choices=('lazy', 'full'), default='lazy', help='LP oracle (untrusted; speed only)')
    ap.add_argument('--no-prepass', action='store_true', help='skip the structure pre-pass')
    ap.add_argument('--shard', default=None, help='I/K: verify the jobs with index = I mod K (sorted file list); with --out')
    ap.add_argument('--combine', nargs='+', default=None, help='combine --out files of shards: coverage, hashes, partition')
    ap.add_argument('--sample-p', default=None, help='SAMPLED check (not a proof): Bernoulli probability per leaf, '
                    'a rational string such as 1/100 (SAMPLED_VERIFICATION.md)')
    ap.add_argument('--sample-R', default=None, help='hex of the random value R drawn after the certificate hash H was fixed')
    ap.add_argument('--thin-jobs', default=None, help='file: job file names whose leaves are all certified (part A)')
    ap.add_argument('--thin-leaves', default=None, help='file: lines "jobname k" of leaves always certified (part A)')
    ap.add_argument('--d-own-p', default=None, help='own-LP re-solve probability per D leaf (rational string, e.g. 1/50)')
    ap.add_argument('--d-own-R', default=None, help='hex of the random value R fixed in advance (own-LP selection seed)')
    ap.add_argument('--own-lp-list', default=None, help='file: lines "jobname k" of D leaves also re-solved by the own LP')
    ap.add_argument('--margins-out', default=None, help='write the stored-dual margins of the D leaves (npz: job, k, margin)')
    a = ap.parse_args()
    try:
        n, lam, rowkeys = load_meta(a.certdir)
        C.Rows(C.Blocks(n), rowkeys)                  # strict validation of every row key before any work
    except (C.SpecError, ValueError, KeyError, TypeError, json.JSONDecodeError, OSError) as ex:
        print(f'NOT VERIFIED: meta.json: {type(ex).__name__}: {ex}')
        sys.exit(1)
    allfiles = sorted(glob.glob(os.path.join(a.certdir, 'jobs', '*.jsonl.gz')))
    files = allfiles
    if a.sample:
        files = files[: a.sample]
    shard = None
    if a.shard:
        i, k = (int(x) for x in a.shard.split('/'))
        if not (0 <= i < k):
            sys.exit('bad --shard')
        files = files[i::k]; shard = f'{i}/{k}'
    files = sorted(files, key=lambda f: -os.path.getsize(f))      # largest jobs first: shorter tail (order is free)
    me = os.path.dirname(os.path.abspath(__file__))
    vh = hashlib.sha256(b''.join(open(os.path.join(me, f), 'rb').read() for f in ('iv_core.py', 'iv_lp.py', 'iv_verify.py'))).hexdigest()
    mh = hashlib.sha256(open(os.path.join(a.certdir, 'meta.json'), 'rb').read()).hexdigest()
    print(f'n={n} lam={lam} jobs={len(files)} verifier={vh[:16]} meta={mh[:16]}' + (f' shard={shard}' if shard else ''), flush=True)
    sample, sinfo = sampling_config(a, allfiles)
    if sample:
        print(f'SAMPLED MODE (not a full check): {sinfo}', flush=True)
    dsel, ownlist, oinfo = own_config(a)
    if oinfo:
        print(f'own-LP re-solves of D leaves: {oinfo}', flush=True)
    if a.combine:
        sys.exit(combine(a.combine, allfiles, n, lam, vh, mh, sinfo, oinfo))
    t0 = time.time()
    results = []

    def collect(it, label):
        out = []; nxt = 0.05
        for r in it:
            out.append(r)
            if a.failfast and r['fail']:
                return out, False
            if len(out) >= nxt * len(files):
                print(f'  {label}: {len(out)}/{len(files)} jobs, {sum(x["leaves"] for x in out)} leaves, '
                      f'{time.time() - t0:.0f}s', flush=True)
                nxt += 0.05
        return out, True

    def phases(mapper):
        """structure pre-pass (records, regions, delegations; partition when the whole certificate is read), then
        the leaf pass.  Returns (results, complete, early verdict or None)."""
        if not a.no_prepass:
            pre, done = collect(mapper(structure_job), 'structure')
            bad = [r for r in pre if r['fail']]
            if bad:
                return pre, done, f'structure: {len(bad)} jobs failed, e.g. {bad[0]["file"]}: {bad[0]["fail"]}'
            if not (a.sample or shard):
                try:
                    partition_check(pre)
                except C.SpecError as ex:
                    return pre, done, f'partition: {ex}'
            print(f'  structure pass OK: {sum(r["leaves"] for r in pre)} leaves, {sum(r["internal"] for r in pre)} '
                  f'internal nodes, {time.time() - t0:.0f}s', flush=True)
        res, done = collect(mapper(verify_job), 'leaves')
        return res, done, None
    if a.workers > 1:
        import multiprocessing as mp
        with mp.get_context('fork').Pool(a.workers, initializer=init_worker, initargs=(a.certdir, a.rounds, a.cap, a.maxage, a.oracle, sample, dsel, ownlist)) as pool:
            results, complete, early = phases(lambda f: pool.imap_unordered(f, files, chunksize=1))
    else:
        init_worker(a.certdir, a.rounds, a.cap, a.maxage, a.oracle, sample, dsel, ownlist)
        results, complete, early = phases(lambda f: (f(x) for x in files))
    if early:
        print(f'NOT VERIFIED: {early}')
        sys.exit(1)
    if a.margins_out:
        names = [r['file'] for r in results]; cnt = [len(r['dmk']) for r in results]
        np.savez(a.margins_out, job=np.array(names), count=np.array(cnt, dtype=np.int64),
                 k=np.array([k for r in results for k in r['dmk']], dtype=np.int64),
                 margin=np.array([v for r in results for v in r['dmv']], dtype=np.float64))
    for r in results:
        r.pop('dmk', None); r.pop('dmv', None)
    if a.out:
        with open(a.out, 'w') as fo:
            fo.write(json.dumps(dict(verifier=vh, meta=mh, n=n, lam=str(lam), shard=shard, sample=a.sample,
                                     complete=complete, jobs=len(results), sampling=sinfo, own_lp=oinfo)) + '\n')
            for r in results:
                fo.write(json.dumps(r) + '\n')
    fails = [r for r in results if r['fail']]
    tot = {k: sum(r[k] for r in results) for k in ('leaves', 'internal', 'empty', 'delegated', 'rounds', 'stored', 'fallback', 'second', 'farkas', 'sampled', 'skipped', 'dleaves')}
    lbs = [Fraction(r['minlb']) for r in results if r['minlb'] is not None]
    print(f'{tot}; min exact leaf bound {float(min(lbs)) if lbs else None}; {time.time() - t0:.1f}s', flush=True)
    if oinfo:
        print(own_report(results), flush=True)
    if fails:
        for r in fails[:10]:
            print('FAIL', r['file'], r['fail'])
        print(f'NOT VERIFIED: {len(fails)} jobs failed' + ('' if complete else ' (stopped at the first failure)'))
        sys.exit(1)
    if a.sample or shard:
        print(('SHARD ' + shard if shard else 'SAMPLE') + ' OK (leaf-level checks only; partition not checked)')
        sys.exit(0)
    try:
        partition_check(results)
    except C.SpecError as ex:
        print(f'NOT VERIFIED: partition: {ex}')
        sys.exit(1)
    if sample:
        print(f'SAMPLED-OK (not a full check): structure and partition complete for {tot["leaves"]} leaves; '
              f'{tot["sampled"]} leaves certified exactly, 0 failures; {sinfo}')
        sys.exit(0)
    print(f'VERIFIED: V_{n} >= {lam} ({float(lam)}); jobs={len(files)}')
    sys.exit(0)


if __name__ == '__main__':
    main()
