/-
`(*health.Server).SetServingStatus(service, status)` (grpc-go, assumed: `health/server.go`).

Users: `v3rpc.healthNotifier.startServe`/`stopServe` (this batch).

Why true: under its mutex, records the status and notifies the watchers (after a `Shutdown` it is
ignored); any number of concurrent callers.

Changes: from `specs-ref/Spec/google_golang_org/grpc/health/Server__SetServingStatus.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api
public import GeneratedProof.google_golang_org.grpc.health
public import SpecPlan.Spec.PkgInit.google_golang_org.grpc.health

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `hs.SetServingStatus(svc, st)`: returns. -/
def health.Server.SetServingStatus.spec : Prop :=
  ∀ (hs : Loc) (svc : GoString) (st : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.health ∗ healthAt hs }}
    (App (App (Val (hs @!! go.GoType.PointerType google_golang_org.grpc.health.Server.ty @!! go!"SetServingStatus"))
      (Val #svc)) (Val #st))
  {{ RET #(); True }}

end spec

end Grpc
end EtcdGrove
end Perennial
