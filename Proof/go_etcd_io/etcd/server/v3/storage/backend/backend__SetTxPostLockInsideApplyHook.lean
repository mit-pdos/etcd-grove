/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__SetTxPostLockInsideApplyHook.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.backend.SetTxPostLockInsideApplyHook.wp_proof
    (hlock : backend.batchTx.lock.spec (GF := GF) (hG := hG))
    (hUnlock : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG)) :
    backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG) := by
  intro γ P WR b qo f hook
  wp_start as ⟨#Hb, Ho, Hpl, Htok⟩
  unfold bOpen
  icases Ho with ⟨Ho, Hcls⟩
  icases isBackend_b γ P WR b $$ Hb with
    ⟨%t, %rt, %db1, %lg2, #Ht, #-⟩
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_method_call
  wp_call
  wp_apply (hlock γ P WR b t qo.half) $$ [$Ho] as ⟨%st, Hl, %Hfo, HWR, Ho⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t1, %db, #Ht1, Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht1 gives %Heq1
  subst Heq1
  unfold plHook
  imod ghostVar_update_halves hook γ.hook f hk $$ Hpl Hhk with ⟨Hpl, Hhk⟩
  wp_auto
  wp_apply (hUnlock γ P WR b t st iprop(True)) $$ [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hg Htok HWR]
  · iframe #
    unfold batchLocked batchLockedAt batchPhys
    iframe Htok
    isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hg]
    · iexists t, db
      iframe Ht Hown Hg
      isplitl
      · iexists hook
        iframe
        iframe #
      · ipureintro
        exact Hwf
    · ileft
      iframe HWR
      ipureintro
      exact Hfo.1
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
