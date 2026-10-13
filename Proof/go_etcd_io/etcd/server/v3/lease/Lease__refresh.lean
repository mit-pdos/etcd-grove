/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__refresh.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__refresh
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__getRemainingTTL
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.refresh.wp_proof
    (hGRT : lease.Lease.getRemainingTTL.spec (GF := GF) (hG := hG)) :
    lease.Lease.refresh.spec (GF := GF) (hG := hG) := by
  intro l d r t dq1 dq2 e
  wp_start as ⟨Hr, Ht, He, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply hGRT $$ [$Hr $Ht] as ⟨Hr, Ht⟩
  (try wp_auto)
  wp_apply _root_.Perennial.time.wp_Now as %now -
  (try wp_auto)
  wp_apply _root_.Perennial.time.Time.wp_Add as %e' -
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold leaseExpiry at HR
  icases HR with ⟨%e2, He2⟩
  icases ptsto_halves_combine _ _ _ $$ [$He $He2] with ⟨%Heq, He⟩
  wp_auto
  icases ptsto_halves_split _ _ $$ He with ⟨He, He2⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk He2]
  · iframe #
    inext
    iunfold leaseExpiry
    iexists _
    iexact He2
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
