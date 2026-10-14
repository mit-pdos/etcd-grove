/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Txn
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.Txn.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hTxn : txn.Txn.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Txn.spec (GF := GF) (hG := hG) := by
  intro E p r skip rq t log Pre Q Post
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.txnPre at Hpre
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨%Hrq, #Hr, Hwt, ⟨Hrd, Hsw, Hlive⟩, Hres, Hcs⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu⟩
  icases txn.soleWriter_len' _ _ $$ Hsw with ⟨%Hl2, Hsw⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, #Hkv, #Hhook, #Hle, -⟩
  iStructNamed Hopts
  wp_auto
  wp_apply hTODO
  iunfold apply.isApplyKV at Hkv
  icases Hkv with ⟨#Hkv, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨#Hle, -⟩
  obtain ⟨ht, hk, hpre⟩ := Hrq
  wp_apply (hTxn.1 todoCtxVal mvcc.neverCd opts.Logger' r opts.TxnModeWriteWithSharedBuffer'
      opts.KV' opts.Lessor' skip E.s E.γ log t E.P Pre Q Post E.f L) $$ [$Hrd $Hsw $Hwt $Hcs $Hu]
    as %resp %trace %err ⟨Hrd, Hu, Hout⟩
  · iframe #
    isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply mvcc.neverDone_neverCd
    ipureintro; exact hpre
  iapply HΦ
  iunfold apply.kvPost
  icases Hout with (⟨%Herr, #He, Hsw, HPre⟩ | ⟨%Hok, #Hresp, Hhdr, Hsw, #Hknown', HPP⟩)
  · -- checkTxn's error
    iexists (.rejected .backend)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨t, ht, Or.inl rfl⟩
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hres He
    isplitl []
    · ipureintro; exact Herr.1
    isplitl [Hrd Hsw Hu]
    · iunfold apply.kvOwn; iframe Hrd Hsw; iunfold apply.leasesLive; iexists L; iframe Hknown Hu
    iright; iexact HPre
  · -- the run committed
    iexists (.applied (mvcc.commitLog log
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) false)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨t, ht, Or.inr ⟨rfl, Hok.2.2⟩⟩
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.noSpaceErrIs, apply.Outcome.logAfter,
      Bool.false_eq_true, ↓reduceIte, txn.srvRunTxn, apply.appliedHdr]
    iframe Hres Hresp Hhdr
    isplitl []
    · ipureintro; exact ⟨Hok.1, Hl2, hpre.1⟩
    isplitl [Hrd Hsw Hu]
    · iunfold apply.kvOwn; iframe Hrd Hsw; iunfold apply.leasesLive; iexists L; iframe Hknown' Hu
    cases txn.txnReadonly t
    · ileft; simp only [Bool.false_eq_true, ↓reduceIte]; iexact HPP
    · iright; simp only [↓reduceIte]; iexact HPP

end proof

end EtcdGrove
end Perennial
