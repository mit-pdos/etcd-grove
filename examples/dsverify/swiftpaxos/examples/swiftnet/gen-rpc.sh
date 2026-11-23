#!/bin/sh
# Regenerates the kit's net/rpc codec (models/net/rpc/rpcgen.py over rpc.toml).
set -e
cd "$(dirname "$0")"
R=$(git rev-parse --show-toplevel)
cd "$R"
python3 models/net/rpc/rpcgen.py examples/dsverify/swiftpaxos/examples/swiftnet/rpc.toml \
  examples/dsverify/swiftpaxos/examples/swiftnet --pkg swiftnet
