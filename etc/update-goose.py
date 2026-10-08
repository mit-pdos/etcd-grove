#!/usr/bin/env python3
"""Regenerate the Goose translation of etcd-raft (EtcdGrove/Code, EtcdGrove/GeneratedProof).

Perennial carried this translation until 2026-10-08 (its c5c3a575d moved etcd
verification out); it is now this repository's, under the Lean module root
`EtcdGrove` (`goose -lean-root go.etcd.io=EtcdGrove`), with the package
configuration in EtcdGrove/Code/go_etcd_io/raft/*.toml. Needs `goose` and
`proofgen` from the pinned Perennial (`go install ./goose/cmd/goose
./goose/cmd/proofgen` in .lake/packages/perennial) and a checkout of the Go
sources, upamanyus/etcd-raft branch `goose`.

usage: etc/update-goose.py --etcd-raft PATH
"""
import argparse
import os
import subprocess
from os import path

PKGS = [
    ".",
    "go.etcd.io/raft/v3/confchange",
    "go.etcd.io/raft/v3/quorum",
    "go.etcd.io/raft/v3/raftpb",
    "go.etcd.io/raft/v3/tracker",
]

parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
parser.add_argument("--etcd-raft", required=True, metavar="PATH",
                    help="checkout of upamanyus/etcd-raft, branch goose")
parser.add_argument("-v", "--verbose", action="store_true")
args = parser.parse_args()

here = path.dirname(path.abspath(__file__))
root = path.join(here, "..")
code = path.join(root, "EtcdGrove", "Code")
proof = path.join(root, "EtcdGrove", "GeneratedProof")
gopath = os.getenv("GOPATH") or path.join(path.expanduser("~"), "go")
for tool, out in [("goose", code), ("proofgen", proof)]:
    cmd = [path.join(gopath, "bin", tool), "-lean", "-lean-root", "go.etcd.io=EtcdGrove",
           "-out", out, "-configdir", code, "-dir", args.etcd_raft] + PKGS
    if args.verbose:
        print(" ".join(cmd))
    subprocess.run(cmd, check=True)
