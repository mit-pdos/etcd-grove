#!/bin/bash
# Run the semantics examples on this host and print what each one observed (doc.go records the
# results). The network variant runs in a private network namespace, then run-veth.sh runs the
# examples and the AcceptAnyOrder and TimeoutOnBreak measurements over the rig's veth links (both
# need sudo; the host's network is not touched).
set -euo pipefail
cd "$(dirname "$0")"
export GOFLAGS=-mod=mod GOPROXY=off GOTOOLCHAIN=local
export PATH=${GO_BIN:-$HOME/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.27.3.linux-amd64/bin}:$PATH
go version; uname -sr
go test -count=1 -v -run TestExamples . | grep -v '^=== RUN'
T=$(mktemp -d)
go test -c -o "$T/netsem.test" .
sudo -n env NETSEM_NETNS=1 unshare -n "$T/netsem.test" -test.v -test.count=1 -test.run 'TestBreakInNetwork|TestNodeIdentity' |
  grep -v '^=== RUN'
rm -rf "$T"
./run-veth.sh
