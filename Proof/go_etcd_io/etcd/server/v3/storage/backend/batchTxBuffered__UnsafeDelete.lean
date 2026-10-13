/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeDelete.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeDelete
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDelete

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
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTxBuffered.UnsafeDelete.wp_proof
    (hBT : backend.batchTx.UnsafeDelete.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi key kb dk Hhas Hp
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, Hkey⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  wp_auto
  wp_apply (hBT γ P W Pk b t st bk bi key kb dk) $$ [Htxf Hpend Hwtx $Hkey] as ⟨Hw, Hkey⟩
  · iframe #
    unfold btW
    iframe
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  iapply HΦ
  iframe Hkey
  iexists t, db
  iframe Ht' Hown
  ihave Hg := batchGhost_step γ P (st := st) (st' := (st.del bi kb)) rfl rfl rfl
    (pend_succ_nat Hwf Hp) (fun i => by simp [BSess.del, BSess.create, BSess.delBucket]) $$ Hg
  iframe Hg
  isplitl
  · iexists hk
    simp only [BSess.put, BSess.del, BSess.create, BSess.delBucket]
    iframe
    iframe #
  · ipureintro
    exact sessWf_del Hwf Hp

end proof

end EtcdGrove
end Perennial
