#!/usr/bin/env bash
# Regenerate raftpb/raft.pb.go in a raft checkout (protobuf-go v2, as scripts/genproto.sh does):
# protoc 3.20.3 and protoc-gen-go v1.36.11, then gofmt -s and goimports.
#   regen-raftpb.sh <raft checkout> [<tool dir>]
# With no tool dir, protoc and protoc-gen-go are fetched into a temporary one.
set -euo pipefail
src=$(cd "$1" && pwd)
tools=${2:-$(mktemp -d)}
if [ ! -x "$tools/bin/protoc" ]; then
  curl -sSLo "$tools/p.zip" https://github.com/protocolbuffers/protobuf/releases/download/v3.20.3/protoc-3.20.3-linux-x86_64.zip
  (cd "$tools" && unzip -qo p.zip)
fi
if [ ! -x "$tools/bin/protoc-gen-go" ]; then
  (cd "$src" && GOBIN="$tools/bin" go install google.golang.org/protobuf/cmd/protoc-gen-go@v1.36.11)
fi
cd "$src/raftpb"
"$tools/bin/protoc" --go_out=. -I=".:$tools/include" --plugin=protoc-gen-go="$tools/bin/protoc-gen-go" \
  --go_opt=paths=source_relative ./raft.proto
gofmt -s -w raft.pb.go
go run golang.org/x/tools/cmd/goimports@v0.51.0 -w raft.pb.go
