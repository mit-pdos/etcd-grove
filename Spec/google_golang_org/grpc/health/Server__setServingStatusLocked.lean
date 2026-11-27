/-
`(*health.Server).setServingStatusLocked(service, status)` (grpc-health, 2026-11-26): under the lock,
records the status and notifies the service's watchers (`server.go`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcHealth

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

/-- `hs.setServingStatusLocked(service, status)`, with the server's status map `S` (at `mS`, the
lock's predicate) and no watcher (`updates` at `mU`, empty: `grpcHealthSrv`'s), records `status` for
`service`. -/
abbrev health.Server.setServingStatusLocked.spec : Prop :=
  ∀ (hs mS mU : Loc) (S : GMap GoString w32) (service : GoString) (status : w32),
  {{ structFieldRef google_golang_org.grpc.health.Server go!"statusMap" hs ↦□ mS ∗
      structFieldRef google_golang_org.grpc.health.Server go!"updates" hs ↦□ mU ∗
      ownMap (GF := GF) mU DFrac.discard (∅ : GMap GoString GoMap) ∗ ownMap mS (DFrac.own 1) S }}
    (App (App (Val (hs @!! go.GoType.PointerType google_golang_org.grpc.health.Server.ty
      @!! go!"setServingStatusLocked")) (Val #service)) (Val #status))
  {{ RET #(); ownMap mS (DFrac.own 1) (<[service := status]> S) }}

end spec

end EtcdGrove
end Perennial
