#!/bin/bash
# Run the semantics examples over the rig's veth links, and the measurements of AcceptAnyOrder and
# TimeoutOnBreak (veth_test.go). Builds the rig's topology with the rig's own code (rig.py,
# Net.up, tag "netsem": namespaces dsrig-netsem-hub and dsrig-netsem-n0..n2, 10.77.0.10-12 on
# veth into a bridge), runs the test as root in a private network namespace of its own (each
# socket is made in node 0's or node 1's namespace by a thread that joined it), and removes the
# namespaces on exit. Needs sudo; nothing is created in or changed in the host's namespace.
set -euo pipefail
cd "$(dirname "$0")"
export GOFLAGS=-mod=mod GOPROXY=off GOTOOLCHAIN=local
export PATH=${GO_BIN:-$HOME/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.27.3.linux-amd64/bin}:$PATH
RIG=../rig
T=$(mktemp -d)
trap 'python3 "$RIG/rig.py" cleanup --tag netsem >/dev/null; rm -rf "$T"' EXIT
go test -c -o "$T/netsem.test" .
python3 "$RIG/rig.py" cleanup --tag netsem >/dev/null
python3 -c "import sys; sys.path.insert(0, '$RIG'); import rig; rig.Net('netsem', 2).up()"
sudo -n env NETSEM_VETH=1 unshare -n "$T/netsem.test" -test.v -test.count=1 -test.run TestVeth |
  grep -v '^=== RUN'
