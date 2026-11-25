/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the top-level robustness result, stated

**gRPC's driver, closed** (`examples/lib/grpcdriver`, notes/library-drivers.md): two machines,
neither of which crashes -- the server (`cmd/server`: registers the driver's service `svc.Driver`,
written as protoc-gen-go-grpc generates one over protobuf's `StringValue`, on a `grpc.NewServer()`
and serves it at `Addr`) and the client (`cmd/client`: one `ClientConn`, unary calls and streams of
every kind from random goroutines with random payloads, metadata and contexts, then `Close` and a
call after it; it panics if an outcome contradicts what gRPC guarantees: the driver's sections
error-set, unary-reply, status-roundtrip, metadata, ctx-canceled, server-stream, client-stream,
bidi-stream, concurrent-calls, close) -- deployed at `grpcAddrs` (`DistDeploy`: the address valid, no
connection, no listener). In every execution of fewer than `grpcSteps` steps along which every
machine keeps fewer than `grpcThreads` live threads (the two bounds, with why, in
`TopLevelDefs.lean`), no thread of either machine is stuck and none has a top-level panic (`Robust`,
`Robustness/Statement.lean`), each machine a fresh Go process (`Robust`'s premise). Since the client
panics when a property of gRPC fails, this says each holds, under every fault the net extension
allows (cut, reset or delayed connections, refused dials).

**Premises**: only the deployment's start (`DistDeploy`) and the program's typing facts (the
commands' `Assumptions`, `net.FieldAssumptions`, `go.BasicIntoValInj`). What it rests on beyond the
proofs, besides the net extension's semantics and the grpc model's trusted claims: the trust-base
collection `etc/tcb-collections/grpcdriver.txt`.
Proved in `Proof/github_com/mit_pdos/etcd_grove/examples/lib/grpcdriver/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- See the file header. -/
def grpcdriver_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [srv_sem : cmd.server.Assumptions] [cli_sem : cmd.client.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σs σc : state) (g : GlobalState),
    DistDeploy grpcAddrs (system σs σc) g →
    Robustness.Robust [] (system σs σc) g grpcThreads grpcSteps

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
