# tasks for phase B from phase A outputs; optional shuffle + sharding: mk_tasks.py OUT_TASKS_PREFIX NSHARDS A1.jsonl [A2 ...]
import sys, json, random
pre = sys.argv[1]; nsh = int(sys.argv[2]); tasks = []
for fn in sys.argv[3:]:
    for l in open(fn):
        r = json.loads(l)
        if "stub" in r:
            st = r["stub"]
            for q0, q1 in r["tasks"]:
                tasks.append({"k": r["k"], "tile": st["tile"], "q0": q0, "q1": q1, "ts": st["wrep_t"], "ms": st["wrep_m"]})
random.Random(12345).shuffle(tasks)
for i in range(nsh):
    with open(f"{pre}_{i:03d}.jsonl", "w") as fh:
        for t in tasks[i::nsh]: fh.write(json.dumps(t) + "\n")
print(len(tasks), "tasks in", nsh, "shards")
