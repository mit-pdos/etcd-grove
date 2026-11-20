# dsverify-lab's network harness (reference, not built)

Copies from dsverify-lab (`mit-pdos/dsverify-lab`, GitHub `master` `348a866`, fetched 2026-11-17;
same authors as this repository, which has no licence file of its own to differ), kept as the
reference for porting dsverify-lab's network kits onto this repository's net extension
(`notes/dsverify-net-port-plan.md`). Nothing reaches this directory: no `lean_lib` glob of
`lakefile.toml`, no script of `etc/`, no Go module of this repository (the copied `go.mod` files
are their own modules and nothing builds them). The paths below `old/dsverify/` are the lab's own.

Their Lean files are written against Perennial `4c8617a` (the lab's pin, older than ours) and the
lab's module roots (`Harness.*`); they are not expected to build here as they are.

**What is here.**

- `harness/lean/Harness/GooseLang/Ext/NetConn/`: the lab's network extension (`Impl`, `Specs`,
  `Tests`), compared with ours in `notes/net-tcp-dsverify-final.md`.
- `harness/lean/Harness/{TrustedCode/net.lean,Code/net.toml}`: its `net` model and Goose
  configuration.
- `harness/lean/Harness/{Spec,Proof}/net/`: the `net` specs the kits use (`addrProto`, `sendTok`,
  `recvTok`, `connEnd`, `newConnResult`, `connErr`; phase 4 proves these statements over our
  extension), and the proved models of `net/rpc` and `net/http` (`Proof/net/rpc`, `Proof/net/http`).
- `harness/lean/Harness/Proof/{grpc,encoding,jsoncodec,bufio}/`: the gRPC model's proofs (unary;
  `ClientConn.Invoke.spec`, `handlerOk`, `GrpcWorld`), the codecs', `bufio` over connections.
- `harness/lean/Harness/{NetLib,SafeDist,Driver,DistLemma}.lean`: the kits' statement
  (`SafeDist`, `NetConfig.WellFormed`, `driver_dist_safe`).
- `harness/lean/Harness/Proof/dsverify_lab/harness/netprobe/`, `harness/netprobe/`: the echo probe
  proved end to end (phase 4's first client).
- `harness/rpcmodel/{grpc,protobuf,src}`: the Go models (gRPC unary as module
  `google.golang.org/grpc`; protobuf; the standard library's `net/rpc`, `net/http`,
  `encoding/json`, `encoding/gob`, `log`); `harness/rpcmodel/{difftest,grpcdifftest}`: their
  differential tests against the real libraries.
- `harness/{pbcodec,jsoncodec,kitgen}`: the generated codecs' runtime and the generators
  (`kitgen/pbgen.py`, `jsongen.py`, `rpcgen.py`).
- `harness/netsem/`: the lab's Go evidence for its `net` decisions.
- `notes/`: `grpc-model.md` (the gRPC model's decisions), `conform.md` (the lab's conformance
  checker and its findings F1-F3), `harness-m2-netconn.md`, `harness-m2a.md` (the network
  extension's design).
