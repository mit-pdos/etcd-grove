#!/usr/bin/env python3
"""The DaemonSet example's worklist: every function `dsmain.Main` reaches, by layer of the plan
(notes/k8s-daemonset-plan.md, "The cut"), each classified by the Goose translation in this tree.

usage: etc/k8s-worklist.py [--tsv FILE] [-o FILE.md]

Runs etc/k8s-callgraph (VTA over RTA, `go run`, needs a Go toolchain that loads the example's
module: GOTOOLCHAIN=go1.27.1) on examples/k8sdaemonset's `./dsmain`, root `Main`, and walks the
graph from Main: every function of a verified layer that is reached is listed (its callees are
followed), and so is every function outside them that a verified one calls (the boundary: the
specs the proofs take from Perennial, as trust-boundary axioms, or from a later translation).
A verified function reached only through the boundary's interior (a callback: `wg.Go(f)`,
`wait.UntilWithContext(ctx, dsc.runWorker, ...)`, an event handler the informer calls) is marked
`^`. A function is `body` (its `.impl` is in `Code/`, here or Perennial's), `trusted` (in
`TrustedCode/`), `names` (its package is translated, the function names only) or
`untranslated`; `*` marks one with a spec file here (`Spec/<pkg>/<fn>.lean`); a gap of
notes/k8s-clientgo-goose.md (C*) or notes/k8s-daemonset-goose.md (D*) is named.

The call graph over-approximates: interface calls go to every type that flows there. The API
groups the program never touches (the model serves pods, nodes, daemonsets and
controllerrevisions; the informer factory builds only their informers) and kube's internal API
types are pruned (their DeepCopyObject and the factory's `newFunc` callbacks reach them); what
remains is listed as found. Writes the summary and the list as Markdown (stdout or -o), and with
--tsv one line per function.
"""
import argparse
import collections
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
PER = os.path.join(ROOT, ".lake", "packages", "perennial", "Perennial")

# the layers the plan verifies (followed), by Go path prefix, with their phase
VERIFIED = [
    ("dsmain", "github.com/mit-pdos/etcd-grove/examples/k8sdaemonset/dsmain", "6"),
    ("apimodel", "github.com/mit-pdos/etcd-grove/examples/k8sdaemonset/apimodel", "3"),
    ("controller", "k8s.io/kubernetes", "5"),
    ("controller", "k8s.io/component-helpers/scheduling", "5"),
    ("leaf", "k8s.io/client-go/util/workqueue", "2"),
    ("leaf", "k8s.io/client-go/util/consistency", "2"),
    ("leaf", "k8s.io/client-go/util/flowcontrol", "2"),
    ("leaf", "k8s.io/client-go/util/retry", "2"),
    ("leaf", "k8s.io/client-go/features", "2"),
    ("leaf", "k8s.io/client-go/listers", "2"),
    ("informers", "k8s.io/client-go/tools/cache", "4"),
    ("informers", "k8s.io/client-go/informers", "4"),
]

# the gaps (names only in the translation because of them)
GAPS = {
    ("k8s.io/kubernetes/pkg/api/v1/pod", "", "VisitContainers"): "D1",
    ("k8s.io/kubernetes/pkg/controller/daemon", "DaemonSetsController", "syncDaemonSet"): "D2",
    ("k8s.io/kubernetes/pkg/controller", "", "ComputeHash"): "D2",
    ("k8s.io/apimachinery/pkg/util/resourceversion", "", "isWellFormed"): "C1",
    ("k8s.io/client-go/util/flowcontrol", "Backoff", "Next"): "C4",
    ("k8s.io/client-go/tools/cache", "threadSafeMap", "Transaction"): "C4",
}
for _r, _n in [("RealPodControl", "createPods"), ("RealPodControl", "DeletePod"),
               ("RealPodControl", "PatchPod"), ("RealRSControl", "PatchReplicaSet"),
               ("RealControllerRevisionControl", "PatchControllerRevision"),
               ("", "AddOrUpdateTaintOnNode"), ("", "RemoveTaintOffNode"), ("", "PatchNodeTaints"),
               ("", "AddOrUpdateLabelsOnNode")]:
    GAPS[("k8s.io/kubernetes/pkg/controller", _r, _n)] = "D2"
for _r, _n in [("LazyErrorNodeSelector", "Match"), ("PreferredSchedulingTerms", "Score"),
               ("", "extractNodeFields"), ("RequiredNodeAffinity", "Match")]:
    GAPS[("k8s.io/component-helpers/scheduling/corev1/nodeaffinity", _r, _n)] = "D2"
for _r in ("delayingType", "rateLimitingType"):
    for _n in ("Add", "Len", "Get", "Done", "ShutDown", "ShutDownWithDrain", "ShuttingDown", "AddAfter"):
        GAPS[("k8s.io/client-go/util/workqueue", _r, _n)] = "C2"

KEEP_GROUPS = ("apps/v1", "core/v1")
INTERNAL = ("k8s.io/kubernetes/pkg/apis/core", "k8s.io/kubernetes/pkg/apis/apps",
            "k8s.io/kubernetes/pkg/apis/autoscaling", "k8s.io/kubernetes/pkg/apis/certificates")


def unreachable(pkg):
    if pkg in INTERNAL:
        return True
    for pre in ("k8s.io/api/", "k8s.io/client-go/informers/", "k8s.io/client-go/listers/",
                "k8s.io/client-go/kubernetes/typed/", "k8s.io/client-go/applyconfigurations/"):
        if pkg.startswith(pre):
            rest = pkg[len(pre):]
            if "/" in rest and rest not in KEEP_GROUPS:
                return True
    return False


def layer(pkg):
    for name, p, phase in VERIFIED:
        if pkg == p or pkg.startswith(p + "/"):
            return name, phase
    return None, None


def mangle(p):
    return p.replace(".", "_").replace("-", "_")


_text = {}


def text(path):
    if path not in _text:
        _text[path] = open(path, encoding="utf-8").read() if os.path.isfile(path) else None
    return _text[path]


def classify(pkg, recv, name):
    comps = ([recv] if recv else []) + [name]
    pat = re.compile(r"def %s\.impl\b" % r"\.".join("«?%s»?" % re.escape(c) for c in comps))
    for base in (os.path.join(ROOT, "TrustedCode"), os.path.join(PER, "TrustedCode")):
        for m in (mangle(pkg), pkg):
            t = text(os.path.join(base, m + ".lean"))
            if t and pat.search(t):
                return "trusted"
    for base in (os.path.join(ROOT, "Code"), os.path.join(PER, "Code")):
        for m in (mangle(pkg), pkg):
            t = text(os.path.join(base, m + ".lean"))
            if t is not None:
                return "body" if pat.search(t) else "names"
    return "untranslated"


def has_spec(pkg, recv, name):
    f = (recv + "__" if recv else "") + name + ".lean"
    return os.path.isfile(os.path.join(ROOT, "Spec", mangle(pkg), f))


def callgraph():
    env = dict(os.environ)
    env.setdefault("GOTOOLCHAIN", "go1.27.1")
    out = subprocess.run(["go", "run", ".", os.path.join(ROOT, "examples", "k8sdaemonset"), "./dsmain", "Main"],
                         cwd=os.path.join(ROOT, "etc", "k8s-callgraph"), env=env, check=True,
                         capture_output=True, text=True).stdout
    nodes, edges = {}, collections.defaultdict(list)
    for line in out.splitlines():
        p = line.split("\t")
        if p[0] == "F":
            i, pkg, recv, name, parent, pos, lines, syn = p[1:9]
            nodes[int(i)] = dict(pkg=pkg, recv=recv, name=name, parent=None if parent == "-" else int(parent),
                                 pos=pos, lines=int(lines), syn=syn)
        elif p[0] == "E":
            edges[int(p[1])].append(int(p[2]))
    return nodes, edges


def walk(nodes, edges):
    def top(i):
        while nodes[i]["parent"] is not None:
            i = nodes[i]["parent"]
        return i

    def key(i):
        return (nodes[i]["pkg"], nodes[i]["recv"], nodes[i]["name"])
    reach = collections.OrderedDict({key(0): dict(node=0, layer="dsmain", phase="6", via="root")})
    first, pruned, seen, q = {}, set(), {0}, [0]
    while q:
        i = q.pop(0)
        t = top(i)
        lay, _ = layer(nodes[t]["pkg"])
        for j in edges[i]:
            tj = top(j)
            kj = key(tj)
            if unreachable(kj[0]):
                pruned.add(kj)
                continue
            lj, pj = layer(kj[0])
            if kj not in reach and (lay is not None or lj is not None):
                reach[kj] = dict(node=tj, layer=lj, phase=pj, via="direct" if lay is not None else "boundary")
                first[kj] = key(t)
            if j not in seen:
                seen.add(j)
                q.append(j)
    rows = []
    for k, info in reach.items():
        n = nodes[info["node"]]
        if n["syn"] != "-" and n["pos"] == "-":
            continue  # wrappers
        pkg, recv, name = k
        c = first.get(k)
        rows.append(dict(pkg=pkg, recv=recv, name=name, status=classify(pkg, recv, name), gap=GAPS.get(k, ""),
                         spec=has_spec(pkg, recv, name), layer=info["layer"] or "boundary",
                         phase=info["phase"] or "-", lines=n["lines"], via=info["via"],
                         pos=re.sub(r"^.*/pkg/mod/", "", n["pos"]),
                         caller="" if c is None else c[0].split("/")[-1] + "." + ".".join(x for x in c[1:] if x)))
    return rows, pruned


ORDER = ["dsmain", "controller", "leaf", "informers", "apimodel", "boundary"]
TITLE = {"dsmain": "Main's package (phase 6)", "controller": "The controller (phase 5)",
         "leaf": "client-go's leaf libraries (phase 2)", "informers": "The informers (phase 4)",
         "apimodel": "The model API server (phase 3; trusted Go)",
         "boundary": "The boundary (what the verified layers call outside them)"}
STATUS = [("body", "bodies"), ("trusted", "trusted model"), ("names", "names only"),
          ("untranslated", "not translated")]


def markdown(rows, pruned):
    out = []
    summ, lines = collections.Counter(), collections.Counter()
    for r in rows:
        summ[(r["layer"], r["status"])] += 1
        lines[(r["layer"], r["status"])] += r["lines"]
    out.append("%d functions (%d more pruned: other API groups, internal API types).\n" % (len(rows), len(pruned)))
    out.append("| layer | " + " | ".join(lab for _, lab in STATUS) + " |")
    out.append("|---|" + "---|" * len(STATUS))
    for l in ORDER:
        out.append("| %s | " % l + " | ".join("%d (%d lines)" % (summ[(l, s)], lines[(l, s)]) if summ[(l, s)] else "-"
                                              for s, _ in STATUS) + " |")
    bylp = collections.defaultdict(lambda: collections.defaultdict(list))
    for r in rows:
        fn = (r["recv"] + "." if r["recv"] else "") + r["name"]
        tag = fn + ("*" if r["spec"] else "") + ("^" if r["via"] == "boundary" else "") + \
            (" (%s)" % r["gap"] if r["gap"] else "")
        bylp[(r["layer"], r["pkg"])][r["status"]].append(tag)
    for l in ORDER:
        pk = sorted(p for (ll, p) in bylp if ll == l)
        if not pk:
            continue
        out.append("\n#### %s\n" % TITLE[l])
        for p in pk:
            d = bylp[(l, p)]
            parts = ["%s (%d): %s" % (lab, len(d[s]), ", ".join(sorted(d[s]))) for s, lab in STATUS if d.get(s)]
            out.append("- `%s`: %s." % (p, "; ".join(parts)))
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tsv")
    ap.add_argument("-o")
    args = ap.parse_args()
    rows, pruned = walk(*callgraph())
    md = markdown(rows, pruned)
    if args.o:
        open(args.o, "w", encoding="utf-8").write(md)
    else:
        sys.stdout.write(md)
    if args.tsv:
        with open(args.tsv, "w", encoding="utf-8") as f:
            f.write("layer\tphase\tpackage\tfunction\tstatus\tgap\tspec\tlines\tvia\tsource\tfirst caller\n")
            for r in sorted(rows, key=lambda r: (r["layer"], r["pkg"], r["recv"], r["name"])):
                fn = (r["recv"] + "." if r["recv"] else "") + r["name"]
                f.write("\t".join([r["layer"], r["phase"], r["pkg"], fn, r["status"], r["gap"],
                                   "spec" if r["spec"] else "", str(r["lines"]), r["via"], r["pos"],
                                   r["caller"]]) + "\n")


if __name__ == "__main__":
    main()
