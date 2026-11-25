/-
Package initialization of `google_golang_org.grpc.health`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports, allocates `logger` and
`producerBuilderSingleton`, runs its translated initializer of `logger`, `grpclog.Component(...)` (phase7-inits batch 2,
2026-11-25, until then the trust-boundary axiom `opaqueInitsOk`; `Component`'s proof, through
`grpclog`'s fact), and runs its two translated `init`s (phase7-inits
batch 2, 2026-11-25; until then the trust-boundary axiom `initFuncsOk`): `client.go`'s stores
`clientHealthCheck` in `internal.HealthCheckFunc` and `producer.go`'s sets `producerBuilderSingleton` to a
new `producerBuilder` and stores `registerClientSideHealthCheckListener` in
`internal.RegisterClientHealthCheckListener`, both through `internal`'s invariants (`grpc/internal/Hooks.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.BaseGrpc
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
public import Proof.google_golang_org.grpc.connectivity.Init
public import Proof.google_golang_org.grpc.grpclog.Init
public import Proof.google_golang_org.grpc.health.grpc_health_v1.Init
public import Proof.google_golang_org.grpc.internal.Init
public import Proof.google_golang_org.grpc.internal.Hooks

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end Perennial
