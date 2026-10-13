/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Put
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Put
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

theorem apply.applierV3backend.Put.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hPut : txn.Put.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Put.spec (GF := GF) (hG := hG) := by
  intro E p r rq o log Pre Q Post
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.putPre at Hpre
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
  have hlen : log.length + 4 ≤ 2 ^ 63 := Hrq.2.2
  ihave #Hl := apply.leaseOk_ignore L (mvcc.stateAfter log) o $$ Hknown
  wp_apply (txn.put_soleWriter_of hPut todoCtxVal mvcc.neverCd opts.Logger' opts.Lessor' opts.KV'
      E.s E.γ r o log E.P Pre Q Post E.f L hlen) $$ [$Hrd $Hsw $Hwt $Hcs $Hu]
    as %resp %trace %err ⟨Hrd, Hu, %Htr, Hout⟩
  · iframe #
    iapply mvcc.txnCtx_todo
  iapply HΦ
  iunfold apply.kvPost
  obtain ⟨hput, hk, -⟩ := Hrq
  icases Hout with (⟨%Hn, #He, Hsw, HPre⟩ | ⟨%Hn, #He, Hsw, HPost⟩ |
    ⟨%Herr, #Hresp, Hhdr, Hsw, #Hlok, HPost, -⟩)
  · -- the lease not found
    iexists (.rejected .backend)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨o, hput, Or.inl ⟨Hn.1, rfl⟩⟩
    simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hres
    isplitl []
    · isplitl []
      · ipureintro; exact Hn.2
      ileft; iexact He
    isplitl [Hrd Hsw Hu]
    · iunfold apply.kvOwn; iframe Hrd Hsw; iunfold apply.leasesLive; iexists L; iframe Hknown Hu
    iright; iexact HPre
  · -- the previous key-value missing
    iexists (.rejected .backend)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨o, hput, Or.inr (Or.inl ⟨Hn.1, Hn.2.1, rfl⟩)⟩
    simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hres
    isplitl []
    · isplitl []
      · ipureintro; exact Hn.2.2
      iright; iexact He
    isplitl [Hrd Hsw Hu]
    · iunfold apply.kvOwn; iframe Hrd Hsw; iunfold apply.leasesLive; iexists L; iframe Hknown Hu
    ileft; iexact HPost
  · -- the put committed
    iexists (.applied (log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) false)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨o, hput, Or.inr (Or.inr rfl)⟩
    simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.noSpaceErrIs, apply.Outcome.logAfter, Bool.false_eq_true,
      ↓reduceIte, apply.appliedHdr]
    iframe Hres Hresp Hhdr
    isplitl []
    · ipureintro; exact ⟨Herr, Hl2, hlen⟩
    isplitl [Hrd Hsw Hu]
    · iunfold apply.kvOwn
      iframe Hrd Hsw
      iunfold apply.leasesLive
      iexists L
      iframe Hu
      iapply apply.leasesKnown_putChange
      iframe #
    ileft; iexact HPost

end proof

end EtcdGrove
end Perennial
