/-
`(*health.Server).SetServingStatus(service, status)` (names only; item 4, the server start): the
health notifier sets the server's status.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.google_golang_org.grpc.health

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `hs.SetServingStatus(service, status)` on grpc's health server returns. -/
abbrev health.Server.SetServingStatus.spec : Prop :=
  ∀ (hs : Loc) (service : GoString) (status : val),
  {{ grpcHealthSrv (GF := GF) hs }}
    (App (App (Val (hs @!! go.GoType.PointerType google_golang_org.grpc.health.Server.ty @!! go!"SetServingStatus"))
      (Val #service)) (Val status))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
