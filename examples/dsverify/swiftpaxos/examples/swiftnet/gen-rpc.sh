#!/bin/sh
# Regenerates the kit's net/rpc codec (models/net/rpc/rpcgen.py over rpc.toml), then drops
# rpc_gen.go's import of the master package, which rpcgen emits for every receiver's package
# although rpc_gen.go uses it only when the package also holds a codec type (the master's does
# not: an rpcgen finding, notes/dsv-swiftpaxos.md; models/ is not this kit's to change).
set -e
cd "$(dirname "$0")"
R=$(git rev-parse --show-toplevel)
cd "$R"
python3 models/net/rpc/rpcgen.py examples/dsverify/swiftpaxos/examples/swiftnet/rpc.toml \
  examples/dsverify/swiftpaxos/examples/swiftnet --pkg swiftnet
sed -i '/^\tmaster "github.com\/imdea-software\/swiftpaxos\/master"$/d' \
  examples/dsverify/swiftpaxos/examples/swiftnet/rpc_gen.go
