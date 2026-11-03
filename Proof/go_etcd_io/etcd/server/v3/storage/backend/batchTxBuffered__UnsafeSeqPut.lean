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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTxBuffered.UnsafeSeqPut.wp_proof
    (hBT : backend.batchTx.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hBuf : backend.txWriteBuffer.putSeq.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi key value kb vb Hhas Hk0 Hk1 Hlt Hp Hhk Hrb Hfk Hsb
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, #Hkey, #Hval, Hpvp⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  wp_auto
  wp_apply (hBT γ P W Pk b t st bk bi key value kb vb DFrac.discard Hk0 Hk1)
    $$ [Htxf Hpend Hwtx] as ⟨Hw, -⟩
  · iframe #
    unfold btW
    iframe
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  ihave %Hbb := batchGhostAt_bound γ P st false HP Hwf $$ Hg
  have Hlen : (bkOf st.W.bks bi.id).length < bufBound := by have := Hbb bi.id; omega
  ihave Hhkp := hkPut_other γ P bi.name kb st.S Hhk
  ihave Hrbp := rbPut_other γ P bi.name st.S Hrb
  ihave Hfkp := fkPut_other γ bi.name kb Hfk
  ihave Hckp := ckPut_other γ bi.name kb st.S Hfk
  imod batchGhost_step_put γ P (st := st) (st' := (st.put bi kb vb true)) rfl rfl rfl
    (pend_succ_nat Hwf Hp) (fun i => put_W_le st bi kb vb true i) bi.name kb
    (hkData_put_other st bi kb vb true) (rbData_put_other st bi kb vb true)
    (fun h => sData_put_hook (S := st.S) kb vb h) (fun h => fkVals_put_other (S := st.S) vb h)
    (fun _ => fkOkG_put true HP Hhas Hfk) (fun h => absurd h Hfk)
    (fun _ => ⟨bi.id, Hhas⟩) (BSess.put_S_other st bi kb vb true)
    $$ Hg Hhkp Hrbp Hfkp Hpvp Hckp
    with ⟨Hg, -, -, -, Hpvp, -⟩
  wp_apply (hBuf (wbOf t) st.W bk bi key value kb vb Hlen Hlt) $$ [$HW] as HW
  · iframe #
  iapply HΦ
  iframe Hpvp
  iexists t, db
  iframe Ht' Hown
  iframe Hg
  isplitl
  · iexists hk
    simp only [BSess.put, BSess.del, BSess.create, BSess.delBucket]
    iframe
    iframe #
  · ipureintro
    exact sessWf_put HP Hwf Hhas (by simpa using Hlt) Hp Hsb

end proof

end EtcdGrove
end Perennial
