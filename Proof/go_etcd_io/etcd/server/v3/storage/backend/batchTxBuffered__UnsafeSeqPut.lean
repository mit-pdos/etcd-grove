/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeSeqPut.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeSeqPut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeSeqPut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__putSeq

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

theorem backend.batchTxBuffered.UnsafeSeqPut.wp_proof
    (hBT : backend.batchTx.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hBuf : backend.txWriteBuffer.putSeq.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi key value kb vb Hhas Hk0 Hk1 Hv Hlt Hp
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, #Hkey, #Hval⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  wp_auto
  wp_apply (hBT γ P W Pk b t st bk bi key value kb vb DFrac.discard Hk0 Hk1 Hv)
    $$ [Htxf Hpend Hwtx] as ⟨Hw, -⟩
  · iframe #
    unfold btW
    iframe
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  ihave %Hbb := batchGhostAt_bound γ P st false HP Hwf $$ Hg
  have Hlen : (bkOf st.W.bks bi.id).length < bufBound := by have := Hbb bi.id; omega
  wp_apply (hBuf (wbOf t) st.W bk bi key value kb vb Hlen Hlt) $$ [$HW] as HW
  · iframe #
  iapply HΦ
  iexists t, db
  iframe Ht' Hown
  ihave Hg := batchGhost_step γ P (st := st) (st' := (st.put bi kb vb true)) rfl rfl rfl
    (pend_succ_nat Hwf Hp) (fun i => put_W_le st bi kb vb true i) $$ Hg
  iframe Hg
  isplitl
  · iexists hk
    simp only [BSess.put, BSess.del, BSess.create, BSess.delBucket]
    iframe
    iframe #
  · ipureintro
    exact sessWf_put HP Hwf Hhas (by simpa using Hlt) Hp

end proof

end EtcdGrove
end Perennial
