"""Compare the `#print axioms` results of raft's Results.lean between two checkouts.

Usage: python3 -I compare-axioms.py A B
where each of A, B is either a checkout whose Results.lean was compiled by Lake itself
(its `.lake/build/lib/lean/Proof/go_etcd_io/raft/v3/Results.trace` holds the messages; a
build restored from Lake's artifact cache holds none), or a text file with the output of
`lake env lean Proof/go_etcd_io/raft/v3/Results.lean` (or its gzip, `.gz`). Messages are normalized (a leading
`file:line:col: ` dropped, the trace's command-line entry skipped) and compared as the set of
`'<name>' depends on axioms: [...]` results. Exits 0 if identical.
"""
import gzip, json, os, re, sys

def results(src):
    if os.path.isdir(src):
        d = json.load(open(src + "/.lake/build/lib/lean/Proof/go_etcd_io/raft/v3/Results.trace"))
        text = "\n".join(str(e.get("message", "")) for e in d["log"])
    else:
        text = (gzip.open(src, 'rt') if src.endswith('.gz') else open(src)).read()
    text = re.sub(r"^\S+\.lean:\d+:\d+: ", "", text, flags=re.M)
    out = {}
    for blk in re.split(r"\n(?=')", text):
        m = re.match(r"'([^']+)' depends on axioms: (\[.*?\])", blk, re.S)
        if m:
            out[m.group(1)] = sorted(x.strip() for x in m.group(2)[1:-1].split(","))
    return out

a, b = results(sys.argv[1]), results(sys.argv[2])
print(f"A: {len(a)} results, B: {len(b)} results")
print("sorryAx in A:", any("sorryAx" in v for v in a.values()),
      "in B:", any("sorryAx" in v for v in b.values()))
diff = sorted(k for k in a.keys() | b.keys() if a.get(k) != b.get(k))
if not diff and a:
    print("IDENTICAL"); sys.exit(0)
for k in diff[:20]:
    print("differs:", k, "\n  A:", a.get(k), "\n  B:", b.get(k))
sys.exit(1)
