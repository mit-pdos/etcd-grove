module

public import Spec.google_golang_org.grpc.health.Server__SetServingStatus
public import Spec.google_golang_org.grpc.health.Server__setServingStatusLocked
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.health.Assumptions]

/-- grpc's `SetServingStatus` (`server.go`; until 2026-11-26 a trust-boundary axiom): locks the
server's mutex for writing, finds it not shut down (`grpcHealthSrv`'s `shutdown`), records the
status (`setServingStatusLocked`) and unlocks it (deferred). -/
theorem health.Server.SetServingStatus.wp_proof
    (hLocked : health.Server.setServingStatusLocked.spec (GF := GF) (hG := hG)) :
    health.Server.SetServingStatus.spec (GF := GF) (hG := hG) := by
  intro hs service status
  wp_start as Hsrv
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold grpcHealthSrv at Hsrv
  icases Hsrv with ⟨%mS, %mU, %uh, #Huh, #Hsd, #HfS, #HfU, #HU, #Hg⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hl, HR⟩
  (try wp_auto)
  unfold healthLockInv
  icases HR with ⟨%S, HS⟩
  wp_apply hLocked hs mS mU S service status $$ [HS] as HS
  · iframe #; iframe
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hl HS]
  · iframe #; inext; iexists _; iexact HS
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
