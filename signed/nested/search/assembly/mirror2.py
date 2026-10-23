# Exact reflection z -> conj(z), t -> -t of nested-certificate data (6.4).  S(conj z) = conj S(z) and the mass constraint is
# invariant under t -> -t, so G_{w~}(conj z) = conj G_w(z) with w~(t) = w(-t): a certificate for T1 arc k maps to one for arc
# 4095 - k.  Tiles: 'up' <-> 'dn' (ci -> -ci), tile parameter q -> 1 - q; complex multipliers are conjugated; masses, tau_rep,
# sigma and mu are unchanged.  Unknown node shapes raise (never guess).
# V22d (2026-10-23): mirror.py 3f993d24 rejected the emitter's empty leaves, which carry "boxes": [] (AssertionError ['boxes']);
# this version accepts an EMPTY "boxes" list there and keeps it in the mirrored leaf.  It also mirrored every phase-B record
# including failed ones, whose "entries" is null (TypeError); a failed record now mirrors to a failed record.  Nothing else changed.
from fractions import Fraction as Fr

def _swap(nm):
    if nm.endswith("up"): return nm[:-2] + "dn"
    if nm.endswith("dn"): return nm[:-2] + "up"
    raise ValueError("tile name without up/dn: " + nm)

def _q(x): return str(1 - Fr(x))
def _neg(x): return str(-Fr(x))

def mirror_tree(t):
    if not isinstance(t, dict): raise ValueError("node is not a dict")
    if "ivsplit" in t:
        assert set(t) == {"ivsplit", "at", "kids"}, sorted(t)
        lo, hi = t["kids"]
        return {"ivsplit": t["ivsplit"], "at": _q(t["at"]), "kids": [mirror_tree(hi), mirror_tree(lo)]}
    typ = t.get("type")
    if typ == "W":
        known = {"boxes", "type", "tile", "tau_rep", "tile_arcs", "wrep_t", "wrep_m", "sigma", "mus"}
        assert set(t) <= known, sorted(set(t) - known)
        assert not t.get("boxes"), "boxes not supported"
        out = {"boxes": [], "type": "W", "tile": _swap(t["tile"]), "tau_rep": t["tau_rep"]}
        arcs = []
        for a in t["tile_arcs"]:
            if isinstance(a, dict):
                assert set(a) <= {"hard", "kind", "child"}, sorted(a)
                arcs.append({"hard": [_q(a["hard"][1]), _q(a["hard"][0])], "kind": a.get("kind", "disc"), "child": mirror_tree(a["child"])})
            else:
                q0, q1, rest = a[0], a[1], a[2:]
                assert len(rest) % 2 == 0
                m = [q for i, x in enumerate(rest) for q in ([x] if i % 2 == 0 else [_neg(x)])]   # (re, im) pairs -> (re, -im)
                arcs.append([_q(q1), _q(q0)] + m)
        out["tile_arcs"] = arcs
        out["wrep_t"] = [_neg(x) for x in t["wrep_t"]]; out["wrep_m"] = list(t["wrep_m"])
        if "sigma" in t: out["sigma"] = t["sigma"]
        if "mus" in t: out["mus"] = [[_q(q), mu] for q, mu in t["mus"]]
        return out
    if typ == "empty":
        known = {"boxes", "type", "v", "y", "vt", "tau_rep"}          # V22d: the emitter writes "boxes": [] in empty leaves
        assert set(t) <= known, sorted(set(t) - known)
        assert not t.get("y"), "box multipliers not supported"
        assert not t.get("boxes"), "boxes not supported"
        out = ({"boxes": []} if "boxes" in t else {})
        out.update({"type": "empty", "v": [t["v"][0], _neg(t["v"][1])], "y": [], "vt": [[a, _neg(b)] for a, b in t.get("vt", [])]})
        if "tau_rep" in t: out["tau_rep"] = t["tau_rep"]
        return out
    raise ValueError("unknown node: " + str(sorted(t))[:200])

def mirror_task(task):
    """phase-B task spec for the mirror arc: k -> 4095 - k (nH = 4096), tile up<->dn, [q0, q1] -> [1 - q1, 1 - q0], ts -> -ts."""
    return {"k": 4095 - task["k"], "tile": _swap(task["tile"]), "q0": _q(task["q1"]), "q1": _q(task["q0"]),
            "ts": [_neg(x) for x in task["ts"]], "ms": list(task["ms"])}

def mirror_output(r):
    """phase-B output record (entries = hard sub-arcs with child trees) for the mirrored task."""
    # V22d: a failed piece (ok false) carries "entries": null; its mirror is a failed record too (the assembler skips both)
    ents = None if r["entries"] is None else \
        [{"hard": [_q(e["hard"][1]), _q(e["hard"][0])], "kind": e.get("kind", "iv"), "child": mirror_tree(e["child"])} for e in r["entries"]]
    assert (ents is not None) == bool(r["ok"]), "entries/ok mismatch"
    return {"k": 4095 - r["k"], "q0": _q(r["q1"]), "q1": _q(r["q0"]), "ok": r["ok"], "entries": ents, "stats": r.get("stats", {}), "dt": r.get("dt", 0)}

def mirror_stub_record(r):
    """phase-A stub record of an 'up' arc k -> the stub record of arc 4095 - k (root W leaf without hard children + task list)."""
    s = r["stub"]
    known = {"boxes", "hard", "mus", "sigma", "stub", "tau_rep", "tile", "type", "w1_arcs", "wrep_m", "wrep_t"}
    assert set(s) <= known and s.get("type") == "W" and not s.get("boxes") and not s.get("mus"), sorted(s)
    w1 = []
    for a in s["w1_arcs"]:
        q0, q1, rest = a[0], a[1], a[2:]
        assert len(rest) % 2 == 0
        w1.append([_q(q1), _q(q0)] + [x if i % 2 == 0 else _neg(x) for i, x in enumerate(rest)])
    iv = lambda L: sorted(([_q(b), _q(a)] for a, b in L), key=lambda p: Fr(p[0]))
    stub = {"boxes": [], "hard": iv(s["hard"]), "mus": [], "sigma": s["sigma"], "stub": True, "tau_rep": s["tau_rep"],
            "tile": _swap(s["tile"]), "type": "W", "w1_arcs": w1, "wrep_m": list(s["wrep_m"]), "wrep_t": [_neg(x) for x in s["wrep_t"]]}
    return {"k": 4095 - r["k"], "stub": stub, "tasks": iv(r["tasks"]), "stats": {"mirror_of": r["k"]}, "dt": 0.0}

if __name__ == "__main__":
    # usage: mirror.py 'A_GLOB' 'B_GLOB' OUT_A OUT_B
    #  OUT_A: all phase-A records except the original stub records of the lower half (k >= 2048), plus the mirror of every
    #         upper-half stub record (k < 2048); closed lower-half arcs (E / N results) are kept as computed.
    #  OUT_B: the given phase-B records (upper-half tasks) plus their mirrors.
    import sys, json, glob
    Ag, Bg, outA, outB = sys.argv[1:5]
    up = {}; dn_stub_tasks = {}; nkeep = 0
    with open(outA, "w") as fa:
        for fn in sorted(glob.glob(Ag)):
            for l in open(fn):
                r = json.loads(l); k = r["k"]
                if "stub" in r:
                    assert r["stub"]["tile"].endswith("up" if k < 2048 else "dn"), (k, r["stub"]["tile"])
                    if k >= 2048: dn_stub_tasks[k] = r["tasks"]; continue
                    up[k] = r
                fa.write(l if l.endswith("\n") else l + "\n"); nkeep += 1
        nm = 0
        for k, r in sorted(up.items()):
            m = mirror_stub_record(r)
            assert m["k"] in dn_stub_tasks, f"no lower-half stub at {m['k']} (phase A not symmetric)"
            assert [tuple(map(Fr, t)) for t in m["tasks"]] == sorted(tuple(map(Fr, t)) for t in dn_stub_tasks[m["k"]]), f"task intervals differ at {m['k']}"
            fa.write(json.dumps(m) + "\n"); nm += 1
    assert nm == len(dn_stub_tasks), (nm, len(dn_stub_tasks))
    nb = 0
    with open(outB, "w") as fb:
        for fn in sorted(glob.glob(Bg)):
            for l in open(fn):
                r = json.loads(l)
                assert r["k"] < 2048, "phase-B input must be upper-half tasks only"
                fb.write(json.dumps(r) + "\n"); fb.write(json.dumps(mirror_output(r)) + "\n"); nb += 1
    print(f"phase A: kept {nkeep} records, mirrored {nm} stub records (lower-half stubs replaced, task intervals equal); phase B: {nb} records + {nb} mirrors")
