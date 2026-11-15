#!/usr/bin/env python3
"""Stage B0's census (`/shared/tmp/stageB/scope-r5.md` §3, §6.1): read-only facts from the sources
that the token accounting of per-type stage B rests on. It reads only `Spec/`, `Proof/` and the pinned
Go source in the module cache; it builds nothing.

Sections:
  bounds    the Spec files stating `threadBound GF ≤ 2^28` (premise text) or
            `[ThreadBoundLe GF (2 ^ 28)]` (instance binder), and which of them reach a gRPC serve
            (`grpc.serve`/`grpc.serveStream`) through the call graph;
  pools     every thread-pool site (definition, `init*`, `borrow*`, `giveBack*`) with the token it
            is borrowed with (`threadTok`, `levelTok N`, `£`);
  lessor    every borrower of `lessorRdPool` and of `isLeaseObj`'s pools (`leasePoolN`,
            `leaseExpPoolN`), the Spec functions reaching it, and the goroutine roots above them
            (GoAttach'd functions in the Go source, the apply thread, gRPC handlers);
  handlers  for each served handler, the level and pool operations in its call tree;
  start     Start's uses of `E.RD`/`leadTimeMu` readers (etcdstart);
  consts    the constants of the per-lock rows.

The call graph: a node is a Spec file; `F → G` when `F`'s proof file (same path under `Proof/`)
imports `G`'s Spec module, or imports a non-function module (lemmas) that does, or `F`'s Spec module
itself imports `G`'s (a Spec module may state several functions' specs; an over-approximation). A node's "text" is
its proof file and the non-function modules its proof imports (transitively, not through Spec
modules), so a pattern used in a lemma file counts for the proofs that import it.

Usage: etc/stageb-census.py [SECTION...] (default: all).
"""
import glob
import os
import re
import sys
from functools import lru_cache

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
GOSRC = os.path.expanduser(
    "~/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261107170612-a4d2bb1720b9")

IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)


def mod_to_path(m):
    p = m.replace(".", "/") + ".lean"
    return p if os.path.exists(p) else None


def path_to_mod(p):
    return p[:-5].replace("/", ".")


@lru_cache(None)
def read(p):
    try:
        with open(p, encoding="utf-8") as f:
            return f.read()
    except OSError:
        return ""


@lru_cache(None)
def imports(p):
    return [x for x in (mod_to_path(m) for m in IMPORT_RE.findall(read(p))) if x]


def is_spec(p):
    return p.startswith("Spec/")


def proof_of(spec):
    q = "Proof/" + spec[len("Spec/"):]
    return q if os.path.exists(q) else None


def is_fn_proof(p):
    return p.startswith("Proof/") and os.path.exists("Spec/" + p[len("Proof/"):])


@lru_cache(None)
def text_closure(p):
    """The files whose text counts for proof file `p`: itself and its lemma imports."""
    seen, stack = [], [p]
    while stack:
        q = stack.pop()
        if q in seen:
            continue
        seen.append(q)
        for r in imports(q):
            if r.startswith("Proof/") and not is_fn_proof(r) and r not in seen \
                    and not r.startswith("Proof/runtime") and "/Link" not in r:
                stack.append(r)
    return tuple(seen)


@lru_cache(None)
def callees(spec):
    pf = proof_of(spec)
    if not pf:
        return ()
    out = set()
    # a Spec module may hold several functions' specs (`Main` with `Run`): its own Spec imports count
    for r in imports(spec):
        if is_spec(r) and r != spec:
            out.add(r)
    for q in text_closure(pf):
        for r in imports(q):
            if is_spec(r) and r != spec:
                out.add(r)
    return tuple(sorted(out))


def node_text(spec):
    pf = proof_of(spec)
    return "\n".join(read(q) for q in text_closure(pf)) if pf else ""


@lru_cache(None)
def reach(spec):
    seen, stack = set(), [spec]
    while stack:
        s = stack.pop()
        if s in seen:
            continue
        seen.add(s)
        stack.extend(callees(s))
    return frozenset(seen)


ALL_SPECS = sorted(glob.glob("Spec/**/*.lean", recursive=True))
SERVE_RE = re.compile(r"\bgrpc\.serve(Stream)?\b")


@lru_cache(None)
def serves_direct(spec):
    return bool(SERVE_RE.search(node_text(spec)))


def section_bounds():
    print("## bounds: Spec files carrying the 2^28 upper bound, and whether they reach a serve\n")
    text_re = re.compile(r"threadBound[^≤\n]*≤ 2 ?\^ ?28")
    inst_re = re.compile(r"ThreadBoundLe GF \(2 \^ 28\)")
    rows = []
    for s in ALL_SPECS:
        t = read(s)
        forms = []
        if text_re.search(t):
            forms.append("premise")
        if inst_re.search(t):
            forms.append("instance")
        if not forms:
            continue
        srv = sorted(x for x in reach(s) if serves_direct(x))
        rows.append((s, "+".join(forms), srv))
    n_srv = sum(1 for r in rows if r[2])
    print(f"{len(rows)} files ({sum('premise' in r[1] for r in rows)} premise, "
          f"{sum('instance' in r[1] for r in rows)} instance); {n_srv} reach a serve.\n")
    for s, f, srv in rows:
        mark = "SERVES" if srv else "-"
        via = (" via " + ", ".join(os.path.basename(x)[:-5] for x in srv[:3])
               + (" ..." if len(srv) > 3 else "")) if srv else ""
        print(f"- [{mark}] {s} ({f}){via}")
    print()


POOL_RE = re.compile(
    r"(threadPool\.(?:isThreadPoolL?|initL?|init_lc|borrowL?(?:_lc|_timeless)?|giveBackL?)\b"
    r"|\b\w+Pool_borrowL?\b|\b\w+_(?:outer|inner)Borrow\b|\bisThreadPoolL?\b)")


def section_pools():
    print("## pools: thread-pool sites in Proof/ (etcd server, lease, mvcc, etcdstart, grpc)\n")
    dirs = ["Proof/go_etcd_io/etcd/server", "Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart",
            "Proof/go_etcd_io/etcd/client/v3", "Proof/google_golang_org/grpc",
            "Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull",
            "Proof/github_com/mit_pdos/etcd_grove/examples/mvccrand"]
    for d in dirs:
        for p in sorted(glob.glob(d + "/**/*.lean", recursive=True)):
            for i, line in enumerate(read(p).splitlines(), 1):
                if line.strip().startswith("--"):
                    continue
                m = POOL_RE.search(line)
                if not m:
                    continue
                tok = re.findall(r"levelTok \d+|levelTok \w+|threadTok|£ \d+", line)
                print(f"- {p}:{i}: {m.group(1)}" + (f"  [{', '.join(tok)}]" if tok else ""))
    print()


LESSOR_BORROW = re.compile(r"lessorRdPool_borrow|threadPool\.borrow\w* leasePoolN|"
                           r"threadPool\.borrow\w* leaseExpPoolN|leasePool\w*_borrow")


def goattach_roots():
    """GoAttach'd functions in the pinned etcdserver Go source (name of the closure's callee)."""
    roots = []
    for g in sorted(glob.glob(GOSRC + "/etcdserver/*.go")):
        if g.endswith("_test.go"):
            continue
        lines = read(g).splitlines()
        for i, line in enumerate(lines):
            if "GoAttach(" in line and "func (s *EtcdServer) GoAttach" not in line:
                body = " ".join(lines[i:i + 12])
                roots.append((os.path.basename(g), i + 1, re.sub(r"\s+", " ", body)[:160]))
    return roots


def section_lessor():
    print("## lessor: borrowers of lessorRdPool / isLeaseObj's pools\n")
    borrowers = []
    for p in sorted(glob.glob("Proof/**/*.lean", recursive=True)):
        for i, line in enumerate(read(p).splitlines(), 1):
            if LESSOR_BORROW.search(line) and not line.strip().startswith("--"):
                borrowers.append((p, i, line.strip()[:120]))
    for p, i, l in borrowers:
        print(f"- {p}:{i}: {l}")
    bspecs = set()
    for p, _, _ in borrowers:
        s = "Spec/" + p[len("Proof/"):]
        if os.path.exists(s):
            bspecs.add(s)
    lemma_files = {p for p, _, _ in borrowers if not is_fn_proof(p)}
    print("\nSpec functions whose call tree reaches a borrower (callers of the borrowing functions,"
          " and proofs importing a borrowing lemma file):")
    callers = {}
    for s in ALL_SPECS:
        pf = proof_of(s)
        hit = sorted(x for x in reach(s) if x in bspecs)
        lem = sorted(q for q in (text_closure(pf) if pf else ()) if q in lemma_files)
        if hit or lem:
            callers[s] = (hit, lem)
    for s, (hit, lem) in sorted(callers.items()):
        why = [os.path.basename(x)[:-5] for x in hit] + [os.path.basename(x)[:-5] + " (lemma)" for x in lem]
        print(f"- {s}: {', '.join(why[:4])}{' ...' if len(why) > 4 else ''}")
    print("\nGoAttach'd goroutines in the Go source (each must not borrow at a level it already holds):")
    for f, i, body in goattach_roots():
        print(f"- {f}:{i}: {body}")
    print()


HANDLERS = [
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__Range.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__Put.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__DeleteRange.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__Txn.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/quotaKVServer__Put.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/quotaKVServer__Txn.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseGrant.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseRevoke.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseTimeToLive.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseLeases.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/quotaLeaseServer__LeaseGrant.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/watchServer__Watch.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthServer__Authenticate.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthServer__AuthEnable.lean",
    "Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthServer__UserAdd.lean",
]
LEVEL_RE = re.compile(r"levelTok \d+|borrowL\w*|\w+_borrowL?\b|\w+_(?:outer|inner)Borrow|"
                      r"GoAttach|wg\.Add|WaitGroup\.Add|threadPool\.borrow\w*|wp_fork\w*")


def section_handlers():
    print("## handlers: level/pool/fork operations in each served handler's call tree\n")
    present = [h for h in HANDLERS if os.path.exists(h)]
    missing = [h for h in HANDLERS if not os.path.exists(h)]
    for h in present:
        ops = {}
        for s in sorted(reach(h)):
            t = node_text(s)
            for m in LEVEL_RE.findall(t):
                ops.setdefault(m, set()).add(os.path.basename(s)[:-5])
        print(f"- {h} ({len(reach(h))} functions in its tree)")
        for op, fs in sorted(ops.items()):
            fs = sorted(fs)
            print(f"    {op}: {', '.join(fs[:6])}{' ...' if len(fs) > 6 else ''}")
    if missing:
        print("\n(not found, check the names: " + ", ".join(os.path.basename(m) for m in missing) + ")")
    print()


def section_start():
    print("## start: E.RD / leadTimeMu / reader stocks in etcdstart\n")
    d = "Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart"
    pat = re.compile(r"\.RD\b|srvLeadTimeReader|leadTime|memberReadN|srvServeBuilt|srvWatchReaders|"
                     r"List\.replicate \(?\d+")
    for p in sorted(glob.glob(d + "/*.lean")):
        for i, line in enumerate(read(p).splitlines(), 1):
            if pat.search(line) and not line.strip().startswith("--"):
                print(f"- {p}:{i}: {line.strip()[:140]}")
    print()


CONSTS = ["rdPoolN", "authRdN", "mvccReaderN", "srvKeepRdN", "httpProcSlots", "srvRevokePoolN",
          "srvRevokeK", "rdStockN", "srvStartReadN", "memberReadN", "lessorPoolN", "leasePoolN",
          "leaseExpPoolN", "actualMaxReaders"]


def section_consts():
    print("## consts: definitions of the per-lock constants\n")
    for c in CONSTS:
        pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:abbrev|def)\s+(?:[\w.]*\.)?"
                         + re.escape(c) + r"\b[^\n]*", re.M)
        found = False
        for p in glob.glob("Proof/**/*.lean", recursive=True) + glob.glob(
                ".lake/packages/perennial/Perennial/**/*.lean", recursive=True):
            for m in pat.finditer(read(p)):
                ln = read(p)[:m.start()].count("\n") + 1
                print(f"- {c}: {p}:{ln}: {m.group(0).strip()[:140]}")
                found = True
        if not found:
            print(f"- {c}: (no definition found)")
    print()


SECTIONS = {"bounds": section_bounds, "pools": section_pools, "lessor": section_lessor,
            "handlers": section_handlers, "start": section_start, "consts": section_consts}

if __name__ == "__main__":
    want = sys.argv[1:] or list(SECTIONS)
    for w in want:
        SECTIONS[w]()
