/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). (Strict M1, 2026-11-05: over
txn's restated `Put.spec`, its updates built by the server's builders, `envAus`: the begin at the
writer's state, the end of the put's change with its witness, `KVBuild.lean`; the floor by
`envAus`'s writer floor.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Put
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Put
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

/-- A put's pending changes at the writer's state: none (the key missing for an ignore flag), else
its one change. -/
theorem apply.putPend_cases (o : OpFull) (log : mvcc.Log) (c : Int) :
    (txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none ∧
        txn.putPend o (srvApi.stAt log c) = []) ∨
      ((txn.needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome) ∧
        txn.putPend o (srvApi.stAt log c) =
          [txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]) := by
  unfold txn.putPend
  simp only [srvApi.stAt]
  by_cases h : txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none
  · left; exact ⟨h.1, h.2, by simp [h]⟩
  · right
    refine ⟨fun hn => ?_, by simp [h]⟩
    cases hf : mvcc.findKey o.key (mvcc.stateAfter log) with
    | none => exact absurd ⟨hn, hf⟩ h
    | some _ => rfl

theorem apply.applierV3backend.Put.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hPut : txn.Put.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Put.spec (GF := GF) (hG := hG) := by
  intro E p r rq o log F Pre Q Post info
  wp_start as ⟨#Hb, Hpre, #HF, Htt⟩
  iunfold apply.applyTok at Htt
  icases Htt with Hmr
  iunfold apply.putPre at Hpre
  icases Hpre with ⟨%Hrq, #Hcp, #Hr, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨⟨%c, Hw⟩, Hlive, Hard, Hres, %B, Hbk, Hhk, Htie, Hcs⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu, HltL⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨#Hlg, #Hkv, -, #Haus, #Hle, -⟩
  iunfold apply.envAus at Haus
  icases Haus with ⟨#HauB, -, #HauE, -, #Hfacts, #Hfloor⟩
  iunfold apply.isApplyKV at Hkv
  icases Hkv with #Hkv
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨#Hle, -⟩
  -- the writer's facts: its floor, its log's witness and reachability
  imod Hfloor $$ %log %c %F Hw HF with ⟨Hw, %HFl⟩
  imod Hfacts $$ %log %c Hw with ⟨Hw, -, #Hnx0, -, %Hreach⟩
  have hlen : log.length + 4 ≤ 2 ^ 63 := Hrq.2.2
  have h2 : 2 ≤ log.length := txn.reach_len (srvApi.stAt log c) Hreach.1
  -- the witness of the log the put commits
  ihave Hnx : E.Nx (mvcc.commitLog log (txn.putPend o (srvApi.stAt log c))) $$ []
  · rcases apply.putPend_cases o log c with ⟨-, -, hp⟩ | ⟨hn, hp⟩
    · rw [hp]; unfold mvcc.commitLog; simp only [↓reduceIte]; iexact Hnx0
    · rw [hp]
      unfold mvcc.commitLog
      simp only [reduceCtorEq, ↓reduceIte]
      iapply (apply.certPre_backend_applied E rq log _ false ?_) $$ Hcp
      unfold apply.backendStep; rw [Hrq.2.1]; exact ⟨o, Hrq.1, Or.inr (Or.inr ⟨hn, rfl⟩)⟩
  ihave #Hlok := apply.leaseOk_ignore L (mvcc.stateAfter log) o $$ Hknown
  -- the put's updates (only for a live lease; else the writer's half kept)
  ihave Hif : iprop((if decide (o.leaseID = W64 0 ∨ o.leaseID ∈ L) then
        txn.putAU E.γ o L (mvcc.leaseItemsOf (mvcc.stateAfter log))
          (fun σ => iprop(⌜σ = srvApi.stAt log c⌝ ∗
            srvApi.wSt E.γs (mvcc.commitLog log (txn.putPend o σ)) c))
      else iprop(True)) ∗
      (if decide (o.leaseID = W64 0 ∨ o.leaseID ∈ L) then iprop(True)
       else srvApi.wSt E.γs log c)) $$ [Hw Hnx]
  · by_cases hl : o.leaseID = W64 0 ∨ o.leaseID ∈ L
    · simp only [hl, decide_true, ↓reduceIte]
      isplitl [Hw Hnx]; rotate_left
      · itrivial
      unfold txn.putAU
      iapply (apply.beginAU_of_auBegin E.γ (srvApi.stAt log c))
      iapply HauB $$ %log %c %_ Hw
      iintro Hw
      isplitr
      · ipureintro; rfl
      isplitr
      · cases hig : o.ignoreLease
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        · simp only [↓reduceIte]
          simp only [srvApi.stAt]
          iapply Hlok; ipureintro; first | exact hig | trivial | rfl
      iapply apply.commitAU_of_auEnd
      ihave He := HauE $$ %log %c %_ Hw Hnx
      iapply apply.auEnd_wand $$ He
      iintro HY
      isplitr
      · ipureintro; rfl
      iexact HY
    · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
      isplitr
      · itrivial
      iexact Hw
  icases Hif with ⟨Hau, Hw0⟩
  ihave Hkb : txn.kvBackend E.γ 1 B (E.Pk B) E.f $$ [Hbk Hhk]
  · iunfold txn.kvBackend; iframe Hbk Hhk
  ihave Hcs : txn.csA (E.Pk B) E.f Pre Q Post $$ [Hcs]
  · iunfold srvApi.csContractA at Hcs; iunfold txn.csA; iexact Hcs
  iStructNamed Hopts
  wp_auto
  wp_apply hTODO
  ihave #HlgN := zapLoggerOk_orNil _ $$ Hlg
  wp_apply (hPut todoCtxVal mvcc.neverCd opts.Logger' opts.Lessor' opts.KV' E.γ r o 1 B (E.Pk B)
      Pre Q Post E.f L (mvcc.leaseItemsOf (mvcc.stateAfter log)) none false _)
      $$ [$Hkv $Hmr $Hle $Hu $Hr $HlgN $Hkb $Hcs $Hau]
    as %resp %trace %err ⟨Hmr, Hkb, %Htrn, ⟨%te', Htrc⟩, -, Hout⟩
  · isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    simp only [traceutil.ownTraceOpt]; itrivial
  iunfold txn.kvBackend at Hkb
  icases Hkb with ⟨Hbk, Hhk⟩
  iapply HΦ
  iunfold apply.applyTok
  iframe Hmr
  isplitr [Htrc]
  rotate_left
  · iunfold apply.traceRes; iright; iexists te'; iexact Htrc
  iapply apply.kvPostF_backend
  obtain ⟨hput, hk, -⟩ := Hrq
  icases Hout with (⟨⟨%Hnl, %Hnin, %Hrn⟩, #He, HPre, Hu⟩ |
    ⟨%σ₀, -, HPost, ⟨%Hσ, Hw'⟩, Hcase⟩)
  · -- the lease not found: nothing written, the writer's half kept
    have hd : ¬ (o.leaseID = W64 0 ∨ o.leaseID ∈ L) := fun h => h.elim Hnl Hnin
    simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte] at *
    iexists (.rejected .backend)
    isplitr
    · ipureintro
      unfold apply.chainStep apply.backendStep
      rw [hk]
      exact ⟨⟨o, hput, Or.inl ⟨Hnl, rfl⟩⟩, fun _ _ h => by cases h⟩
    simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hres
    isplitl []
    · isplitl []
      · ipureintro; exact Hrn
      ileft; iexact He
    isplitl [Hw0 Hbk Hhk Htie Hu Hard HltL]
    · iapply (apply.kvOwn_of_split E log B c)
      iframe Hw0 Htie
      iunfold apply.kvRest
      iframe Hbk Hhk Hard
      iunfold apply.leasesLive; iexists L; iframe Hknown Hu HltL
    iright; iexact HPre
  · subst Hσ
    rcases apply.putPend_cases o log c with ⟨hn, hf, hp⟩ | ⟨hn, hp⟩
    · -- the key missing: nothing written
      have hcl : mvcc.commitLog log (txn.putPend o (srvApi.stAt log c)) = log := by
        rw [hp]; unfold mvcc.commitLog; simp
      rw [hcl]
      icases Hcase with (⟨⟨-, -, %Hrn⟩, #He, Hu⟩ | ⟨⟨-, %Hnps⟩, -⟩)
      · iexists (.rejected .backend)
        isplitr
        · ipureintro
          unfold apply.chainStep apply.backendStep
          rw [hk]
          exact ⟨⟨o, hput, Or.inr (Or.inl ⟨hn, hf, rfl⟩)⟩, fun _ _ h => by cases h⟩
        simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
        iframe Hres
        isplitl []
        · isplitl []
          · ipureintro; exact Hrn
          iright; iexact He
        isplitl [Hw' Hbk Hhk Htie Hu Hard HltL]
        · iapply (apply.kvOwn_of_split E log B c)
          iframe Hw' Htie
          iunfold apply.kvRest
          iframe Hbk Hhk Hard
          iunfold apply.leasesLive; iexists L; iframe Hknown Hu HltL
        ileft; iexact HPost
      · exfalso
        have := Hnps hn
        simp only [srvApi.stAt] at this
        rw [hf] at this; simp at this
    · -- the put committed
      have hcl : mvcc.commitLog log (txn.putPend o (srvApi.stAt log c)) =
          log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]] := by
        rw [hp]; unfold mvcc.commitLog; simp
      rw [hcl]
      icases Hcase with (⟨⟨%Hnp, %Hfk, -⟩, -⟩ | ⟨⟨%Herr, -⟩, #Hresp, Hhdr, #Hlok', Hu⟩)
      · exfalso
        have := hn Hnp
        simp only [srvApi.stAt] at Hfk
        rw [Hfk] at this; simp at this
      iexists (.applied (log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) false)
      isplitr
      · ipureintro
        unfold apply.chainStep apply.backendStep
        rw [hk]
        exact ⟨⟨o, hput, Or.inr (Or.inr ⟨hn, rfl⟩)⟩, fun _ _ _ => HFl⟩
      simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.noSpaceErrIs, apply.Outcome.logAfter,
        Bool.false_eq_true, ↓reduceIte, apply.appliedHdr, srvApi.stAt]
      iframe Hres Hresp Hhdr
      isplitl []
      · ipureintro; exact ⟨Herr, h2, by omega⟩
      isplitl [Hw' Hbk Hhk Htie Hu Hard HltL]
      · iapply (apply.kvOwn_of_split E _ B c)
        iframe Hw' Htie
        iunfold apply.kvRest
        iframe Hbk Hhk Hard
        iunfold apply.leasesLive
        iexists L
        isplitr [Hu HltL]
        · iapply apply.leasesKnown_putChange
          iframe #
        rw [txn.stateAfter_snoc]
        simp only [srvApi.stAt] at hp
        rw [hp]
        iframe Hu HltL
      ileft; iexact HPost

end proof

end EtcdGrove
end Perennial
