#!/usr/bin/env python3
"""Random perturbations of Antithesis's recorded streams, with TLC's verdict on each, for the
differential test (diff_test.go). mutate.py's 60 mutations are each a targeted fault; these are
blind ones (an event dropped, repeated, moved, or a field changed), which reach the binding's
guards that no honest stream and no targeted mutation fails.

    EFR=/path/to/etcd-raft-formalized python3 -I testdata/gen-fuzz.py [COUNT] [SEED]

Needs what gen-fixtures.sh needs. Writes testdata/fuzz/<n>.ndjson.gz (the stream cut 300 events
after the change, then cut after the event TLC stops at) and testdata/verdicts-fuzz.txt (the
format of verdicts.txt; source `fuzz`).
"""
import gzip
import json
import os
import random
import subprocess
import sys
import tempfile

here = os.path.dirname(os.path.abspath(__file__))
fm = os.path.join(os.environ["EFR"], "antithesis-fm")
count = int(sys.argv[1]) if len(sys.argv) > 1 else 300
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)


def manifest(name):  # as validator-tests.sh
    m = "manifest"
    if name.startswith("m-"):
        m += "-m"
    elif "5" in name:
        m += "5"
    if name.endswith("-empty"):
        m += "-empty"
    return m


def verdict(lines, m, tmp):
    s = os.path.join(tmp, "s.ndjson")
    for f in os.listdir(tmp):
        os.remove(os.path.join(tmp, f))
    with open(s, "w") as f:
        f.writelines(lines)
    open(s + ".eof", "w").close()
    out = subprocess.run([sys.executable, "-I", os.path.join(fm, "tracekit/check/streamcheck.py"),
                          os.path.join(fm, "spec", m + ".json"), s], capture_output=True, text=True).stdout
    return out.splitlines()[0][:300] if out else "ERROR no output"


NODES = ["raft1", "raft2", "raft3", "raft4", "raft5"]


def perturb(e):
    """Change one field of event e (in place); False if it has none to change."""
    tgt = e
    if "msg" in e and rng.random() < 0.6:
        tgt = e["msg"]
    ints = [k for k, v in tgt.items() if isinstance(v, int) and not isinstance(v, bool) and k not in ("k", "seq", "hint")]
    choices = []
    if ints:
        choices.append("int")
    if any(isinstance(v, bool) for v in tgt.values()):
        choices.append("bool")
    if "vote" in tgt or "from" in tgt or "to" in tgt:
        choices.append("name")
    if "role" in tgt:
        choices.append("role")
    if "type" in tgt and tgt is e.get("msg"):
        choices.append("type")
    if tgt.get("entries"):
        choices.append("entries")
    if "by" in tgt:
        choices.append("by")
    for opt in ("first", "entries", "cause", "b", "a", "applied", "voters"):
        if opt in tgt:
            choices.append("drop:" + opt)
    if not choices:
        return False
    c = rng.choice(choices)
    if c == "int":
        k = rng.choice(ints)
        tgt[k] += rng.choice([-2, -1, 1, 1, 2])
    elif c == "bool":
        k = rng.choice([k for k, v in tgt.items() if isinstance(v, bool)])
        tgt[k] = not tgt[k]
    elif c == "name":
        k = rng.choice([k for k in ("vote", "from", "to") if k in tgt])
        tgt[k] = rng.choice(NODES[:3] + [""])
    elif c == "role":
        tgt["role"] = rng.choice(["follower", "candidate", "leader", "precandidate"])
    elif c == "type":
        tgt["type"] = rng.choice(["app", "appresp", "vote", "voteresp", "hb", "hbresp", "snap", "prevote"])
    elif c == "entries":
        es = tgt["entries"]
        j = rng.randrange(len(es))
        op = rng.choice(["term", "value", "drop", "dup"])
        if op == "term":
            es[j]["term"] += rng.choice([-1, 1])
        elif op == "value":
            es[j]["value"] = "ff" if not isinstance(es[j]["value"], dict) else ""
        elif op == "drop":
            del es[j]
        else:
            es.insert(j, dict(es[j]))
    elif c == "by":
        tgt["by"] = rng.choice(["recv", "tick", "campaign", "propose", "boot"])
    else:
        del tgt[c.split(":")[1]]
    return True


def main():
    traces = sorted(d for d in os.listdir(os.path.join(fm, "traces")))
    os.makedirs(os.path.join(here, "fuzz"), exist_ok=True)
    out = open(os.path.join(here, "verdicts-fuzz.txt"), "w")
    with tempfile.TemporaryDirectory() as tmp:
        n = 0
        while n < count:
            name = rng.choice(traces)
            lines = [l for l in open(os.path.join(fm, "traces", name, "stream.ndjson")) if l.strip()]
            k = rng.randrange(len(lines))
            L = [json.loads(l) for l in lines[:k + 300]]
            op = rng.choice(["perturb", "perturb", "perturb", "drop", "dup", "swap"])
            at = k + 1
            if op == "perturb":
                if not perturb(L[k]):
                    continue
            elif op == "drop":
                del L[k]
            elif op == "dup":
                L.insert(k + 1, json.loads(json.dumps(L[k])))
                at = k + 2
            else:
                j = next((j for j in range(k + 1, len(L)) if L[j]["node"] == L[k]["node"]), None)
                if j is None:
                    continue
                L[k], L[j] = L[j], L[k]
            text = [json.dumps(e, separators=(",", ":")) + "\n" for e in L]
            m = manifest(name)
            v = verdict(text, m, tmp)
            fs = v.split()
            if fs[0] in ("REJECTED", "VIOLATED"):
                text = text[:int(fs[1])]
            n += 1
            rel = "fuzz/%d.ndjson.gz" % n
            with gzip.open(os.path.join(here, rel), "wt") as f:
                f.writelines(text)
            cfg = json.load(open(os.path.join(fm, "spec", m + ".json")))["stream_config"]
            out.write("fuzz %s %s %d %s\n" % (rel, cfg, at, v))
            out.flush()
            print(n, name, op, at, v[:100], flush=True)


main()
