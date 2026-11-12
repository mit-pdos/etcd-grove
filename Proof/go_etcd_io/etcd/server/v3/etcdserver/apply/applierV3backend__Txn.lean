/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). (Strict M1, 2026-11-05: over
txn's restated `Txn.specSole`, its read update at the writer's read, its write updates built by
the server's builders, `envAus`, told that the checks passed (`PathsIgnOk`, txn's wand, decided
by the coordinator, 2026-11-06); `notes/mvcc-migration/server.md`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Txn
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVBuild
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3
open mvcc.api (MvccState)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.Txn.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hTxn : txn.Txn.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Txn.spec (GF := GF) (hG := hG) := by
  intro E p r skip rq t log F Pre Q Post info
  wp_start as ⟨#Hb, Hpre, #HF, Htt⟩
  iunfold apply.applyTok at Htt
  icases Htt with Hmr
  iunfold apply.txnPre at Hpre
  icases Hpre with ⟨%Hrq, #Hcp, #Hr, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨⟨%c, Hw⟩, Hlive, Hard, Hres, %B, Hbk, Hhk, Htie, Hcs⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu, HltL⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, #Hkv, -, #Haus, #Hle, -⟩
  iunfold apply.envAus at Haus
  icases Haus with ⟨#HauB, #HauR, #HauE, -, #Hfacts, #Hfloor⟩
  iunfold apply.isApplyKV at Hkv
  icases Hkv with #Hkv
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨#Hle, -⟩
  obtain ⟨ht, hk, hpre, hput⟩ := Hrq
  -- the writer's facts: its floor, its reachability
  imod Hfloor $$ %log %c %F Hw HF with ⟨Hw, %HFl⟩
  imod Hfacts $$ %log %c Hw with ⟨Hw, -, -, -, %Hreach⟩
  have h2 : 2 ≤ log.length := txn.reach_len (srvApi.stAt log c) Hreach.1
  have hlen : log.length + 4 ≤ 2 ^ 63 := hput
  -- the read update, at the writer's state
  ihave Hau0 := HauR $$ %log %c %(srvApi.wSt E.γs log c) Hw []
  · iintro Hw; iexact Hw
  ihave Hau : srvApi.auRead E.γ (fun σ => iprop(⌜σ.log = log⌝ ∗
      (fun σ => iprop(⌜σ = srvApi.stAt log c⌝ ∗ srvApi.wSt E.γs log c)) σ)) $$ [Hau0]
  · iapply apply.auRead_wand $$ Hau0
    iintro %σ ⟨%Hσ, Hw⟩
    subst Hσ
    isplitr
    · ipureintro; rfl
    dsimp only
    iframe Hw
    ipureintro; rfl
  -- the write updates, given once the checks passed
  ihave Hwand : iprop(if txn.txnReadonly t then iprop(True) else
      iprop(∀ σ : MvccState,
        ⌜txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t))⌝ -∗
        (fun σ => iprop(⌜σ = srvApi.stAt log c⌝ ∗ srvApi.wSt E.γs log c)) σ -∗
        txn.txnBeginAU E.γ log t (fun σ => iprop(⌜σ = srvApi.stAt log c⌝ ∗
          srvApi.wSt E.γs (mvcc.commitLog log (txn.txnChs log t)) c)))) $$ []
  · cases hro : txn.txnReadonly t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iintro %σ %hig ⟨%Hσ, Hw⟩
      subst Hσ
      unfold txn.txnBeginAU
      iapply (apply.beginAU_of_auBegin E.γ (srvApi.stAt log c))
      iapply HauB $$ %log %c %_ Hw
      iintro Hw
      isplitr
      · ipureintro; rfl
      iapply apply.commitAU_of_auEnd
      ihave Hnx := apply.certPre_backend_applied E rq log _ false
        (by unfold apply.backendStep; rw [hk]
            exact ⟨t, ht, Or.inr ⟨rfl, fun h => (by rw [hro] at h; cases h), hig⟩⟩) $$ Hcp
      ihave He := HauE $$ %log %c %_ Hw Hnx
      iapply apply.auEnd_wand $$ He
      iintro HY
      isplitr
      · ipureintro; first | rfl | trivial
      iexact HY
    · simp only [↓reduceIte]; itrivial
  iunfold srvApi.auRead at Hau
  ihave Hkb : txn.kvBackend E.γ 1 B (E.Pk B) E.f $$ [Hbk Hhk]
  · iunfold txn.kvBackend; iframe Hbk Hhk
  ihave Hcs : txn.csA (E.Pk B) E.f Pre Q Post $$ [Hcs]
  · iunfold srvApi.csContractA at Hcs; iunfold txn.csA; iexact Hcs
  iStructNamed Hopts
  wp_auto
  wp_apply hTODO
  wp_apply (hTxn.1 todoCtxVal mvcc.neverCd opts.Logger' r opts.TxnModeWriteWithSharedBuffer'
      opts.KV' opts.Lessor' skip E.γ log t 1 B (E.Pk B) Pre Q Post E.f L none false _ _)
      $$ [$Hkv $Hmr $Hkb $Hle $Hr $Hu $Hcs $Hau $Hwand]
    as %resp %trace %err ⟨Hmr, Hkb, %σr, -, Hout⟩
  · isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    isplitr
    · iapply mvcc.neverDone_neverCd
    iframe Hknown
    ipureintro; exact hpre
  iunfold txn.kvBackend at Hkb
  icases Hkb with ⟨Hbk, Hhk⟩
  iapply HΦ
  iunfold apply.applyTok
  iframe Hmr
  icases Hout with (⟨%Herr, #He, HPre, ⟨%Hσ, Hw⟩, Hu, -⟩ |
    ⟨%Hok, ⟨%te', Htrc⟩, -, #Hresp, Hhdr, #Hknown', Hu, HPP⟩)
  · -- checkTxn's error
    isplitl
    rotate_left
    · rw [Herr.2.1]; iapply apply.traceRes_null
    iapply apply.kvPostF_backend
    iexists (.rejected .backend)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨⟨t, ht, Or.inl ⟨rfl, fun hp hig => Herr.2.2.2 (txn.txnLeased_of_plain t hp)
        ⟨hig, txn.pathsLeaseOk_plain _ _ _ (txn.txnPlain_branch t _ hp)⟩⟩⟩, fun _ _ h => by cases h⟩
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hres He
    isplitl []
    · ipureintro; exact Herr.1
    isplitl [Hw Hbk Hhk Htie Hu Hard HltL]
    · iapply (apply.kvOwn_of_split E log B c)
      iframe Hw Htie
      iunfold apply.kvRest
      iframe Hbk Hhk Hard
      iunfold apply.leasesLive; iexists L; iframe Hknown Hu HltL
    iright; iexact HPre
  · -- the run committed
    isplitr [Htrc]
    rotate_left
    · iunfold apply.traceRes; iright; iexists te'; iexact Htrc
    iapply apply.kvPostF_backend
    iexists (.applied (mvcc.commitLog log
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) false)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨⟨t, ht, Or.inr ⟨rfl, Hok.2.2.1, Hok.2.2.2.1⟩⟩, fun _ _ _ => HFl⟩
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.noSpaceErrIs, apply.Outcome.logAfter,
      Bool.false_eq_true, ↓reduceIte, apply.appliedHdr]
    iframe Hres
    isplitl [Hhdr]
    · isplitr
      · isplitr
        · isimp only [txn.txnChs, txn.srvRunTxn] at Hresp
          simp only [txn.srvRunTxn]
          iexact Hresp
        ipureintro; exact Hok.1
      iframe Hhdr
      ipureintro; exact ⟨h2, hlen⟩
    cases hro : txn.txnReadonly t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases HPP with ⟨HPost, %σw, -, ⟨%Hσ, Hw⟩⟩
      isplitl [Hw Hbk Hhk Htie Hu Hard HltL]
      · iapply (apply.kvOwn_of_split E _ B c)
        iframe Hw Htie
        iunfold apply.kvRest
        iframe Hbk Hhk Hard
        iunfold apply.leasesLive; iexists L; iframe Hknown' Hu HltL
      ileft; iexact HPost
    · simp only [↓reduceIte]
      icases HPP with ⟨HPre, ⟨%Hσ, Hw⟩⟩
      have hchs : txn.txnChs log t = [] := Hok.2.2.1 hro
      have hcl : mvcc.commitLog log (txn.txnChs log t) = log := by
        rw [hchs]; unfold mvcc.commitLog; simp
      isplitl [Hw Hbk Hhk Htie Hu Hard HltL]
      · simp only [txn.txnChs] at hcl
        rw [hcl]
        iapply (apply.kvOwn_of_split E _ B c)
        iframe Hw Htie
        iunfold apply.kvRest
        iframe Hbk Hhk Hard
        iunfold apply.leasesLive; iexists L
        rw [hcl] at *
        iframe Hknown' Hu HltL
      iright; iexact HPre

end proof

end EtcdGrove
end Perennial
