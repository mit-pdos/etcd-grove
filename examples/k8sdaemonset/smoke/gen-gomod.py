"""Writes this directory's go.mod: the smoke test over a Kubernetes checkout.

Usage: python3 -I gen-gomod.py /path/to/kubernetes

k8s.io/kubernetes replaces its staging modules (k8s.io/api, k8s.io/client-go, ...) by
./staging/src/k8s.io/<name>; a module importing it must do the same, here by the checkout's
directories. The model module (..) is replaced by its directory.
"""
import os
import re
import sys

k8s = os.path.abspath(sys.argv[1])
here = os.path.dirname(os.path.abspath(__file__))
text = open(os.path.join(k8s, "go.mod")).read()
staging = re.findall(r"^\s+(k8s\.io/[a-z0-9-]+) => \./(staging/src/k8s\.io/[a-z0-9-]+)\s*$", text, re.M)
if not staging:
    sys.exit("no staging replace directives in %s/go.mod" % k8s)
lines = [
    "module github.com/mit-pdos/etcd-grove/examples/k8sdaemonset/smoke",
    "",
    "go 1.27.1",
    "",
    "require (",
    "\tgithub.com/mit-pdos/etcd-grove/examples/k8sdaemonset v0.0.0",
    "\tk8s.io/kubernetes v0.0.0",
    ")",
    "",
    "replace (",
    "\tgithub.com/mit-pdos/etcd-grove/examples/k8sdaemonset => ..",
    "\tk8s.io/kubernetes => " + k8s,
]
for mod, path in staging:
    lines.append("\t%s => %s" % (mod, os.path.join(k8s, path)))
lines.append(")")
open(os.path.join(here, "go.mod"), "w").write("\n".join(lines) + "\n")
print("wrote go.mod (%d staging modules from %s)" % (len(staging), k8s))
