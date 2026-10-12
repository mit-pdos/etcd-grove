/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__DeleteRange
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange
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

theorem apply.applierV3backend.DeleteRange.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hDel : txn.DeleteRange.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro E p r rq o log Pre Q Post
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.deletePre at Hpre
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨%Hrq, #Hr, ⟨Hrd, Hsw, Hknown⟩, Hres, Hcs⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, #Hkv, #Hhook, -⟩
  iStructNamed Hopts
  wp_auto
  wp_apply hTODO
  iunfold apply.isApplyKV at Hkv
  icases Hkv with ⟨#Hkv, -⟩
  obtain ⟨hdel, hk, hlen, hst⟩ := Hrq
  wp_apply (txn.deleteRange_soleWriter_of hDel todoCtxVal mvcc.neverCd opts.Logger' opts.KV'
      E.s E.γ r o log E.P Pre Q Post E.f hlen hst) $$ [$Hrd $Hsw $Hcs]
    as %resp %trace %err ⟨Hrd, %Htr, HPost, Hout⟩
  · iframe #
    iapply mvcc.txnCtx_todo
  iapply HΦ
  iunfold apply.kvPost
  icases Hout with (⟨%Herr, #Hresp, Hsw, %Hst⟩ | ⟨%Herr, Hsw⟩)
  · -- the delete committed
    iexists (.applied (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) o)) false)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨o, hdel, Or.inl rfl⟩
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, apply.Outcome.logAfter,
      Bool.false_eq_true, ↓reduceIte]
    iframe Hres Hresp
    isplitl []
    · ipureintro; exact Herr
    isplitl [Hrd Hsw Hknown]
    · iunfold apply.kvOwn
      iframe Hrd Hsw
      iapply apply.leasesKnown_commit_delete $$ Hknown
    ileft; iexact HPost
  · -- the range read failed
    iexists (.rejected .backend)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨o, hdel, Or.inr ⟨Herr.2.1, rfl⟩⟩
    simp only [apply.deleteOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hres
    isplitl []
    · ipureintro; exact ⟨Herr.2.2, Herr.1, Herr.2.1⟩
    isplitl [Hrd Hsw Hknown]
    · iunfold apply.kvOwn; iframe
    ileft; iexact HPost

end proof

end EtcdGrove
end Perennial
