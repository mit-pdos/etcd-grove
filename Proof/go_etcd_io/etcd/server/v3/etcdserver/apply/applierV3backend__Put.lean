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

theorem apply.applierV3backend.Put.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hPut : txn.Put.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Put.spec (GF := GF) (hG := hG) := by
  intro E p r rq o log F Pre Q Post info
  wp_start as ⟨#Hb, Hpre, #HF, Htt⟩
  iunfold apply.applyTok at Htt
  icases Htt with Hmr
  iunfold apply.putPre at Hpre
  icases Hpre with ⟨%Hrq, #Hr, %L, %Hwt, #Hcp, Hpre⟩
  iunfold apply.mPreAt at Hpre
  icases Hpre with ⟨⟨%c, Hw⟩, Hlive, Hard, Hres, %B, Hbk, Hhk, Htie, Hcs⟩
  iunfold apply.leasesLiveAt at Hlive
  icases Hlive with ⟨#Hknown, Hu, HltL, HWt⟩
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
  have hlen : log.length + 4 ≤ 2 ^ 63 := Hrq.2.2.1
  have h2 : 2 ≤ log.length := txn.reach_len (srvApi.stAt log c) Hreach.1
  ihave #Hlok := apply.leaseOk_ignore L (mvcc.stateAfter log) o $$ Hknown
  -- the put's updates (only for a live lease; else the writer's half kept)
  ihave Hif : iprop((if decide (o.leaseID = W64 0 ∨ o.leaseID ∈ L) then
        txn.putAUW E.γ E.win o L (mvcc.leaseItemsOf (mvcc.stateAfter log))
          (fun σ => iprop(⌜σ = srvApi.stAt log c⌝ ∗
            srvApi.wStQ E.γs E.stq (mvcc.commitLog log (txn.putPend o σ)) c ∗ E.Wt E.win))
      else iprop(True)) ∗
      (if decide (o.leaseID = W64 0 ∨ o.leaseID ∈ L) then iprop(True)
       else iprop(srvApi.wStQ E.γs E.stq log c ∗ E.Wt E.win))) $$ [Hw HWt]
  · by_cases hl : o.leaseID = W64 0 ∨ o.leaseID ∈ L
    · simp only [hl, decide_true, ↓reduceIte]
      -- the witness of the log the put commits: only now, the lease live (S3a2)
      ihave Hnx : E.Nx (mvcc.commitLog log (txn.putPend o (srvApi.stAt log c))) $$ []
      · rcases apply.putPend_cases o log c with ⟨-, -, hp⟩ | ⟨hn, hp⟩
        · rw [hp]; unfold mvcc.commitLog; simp only [↓reduceIte]; iexact Hnx0
        · rw [hp]
          unfold mvcc.commitLog
          simp only [reduceCtorEq, ↓reduceIte]
          iunfold apply.certPreT at Hcp
          ihave Hc := Hcp $$ %(apply.Outcome.applied
            (log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) false) %(by
              refine ⟨?_, ?_⟩
              · unfold apply.chainStep apply.backendStep; rw [Hrq.2.1]
                exact ⟨o, Hrq.1, Or.inr (Or.inr ⟨hn, rfl⟩)⟩
              · simp only [apply.leaseExactL, Hrq.2.1]
                intro op hop; rw [Hrq.1] at hop; cases hop
                exact ⟨fun h => (hl.elim h.1 h.2).elim, fun h => by cases h⟩)
          simp only [apply.Outcome.logAfter]
          iexact Hc
      isplitl [Hw Hnx HWt]; rotate_left
      · itrivial
      unfold txn.putAUW
      iapply (apply.beginAU_of_auBegin E.γ (srvApi.stAt log c))
      iapply HauB $$ %log %c %_ Hw
      iintro Hw
      isplitr
      · ipureintro
        refine ⟨rfl, fun hn => ?_⟩
        simp only [srvApi.stAt] at hn
        exact apply.putWinMove E.win rq o log L Hwt Hrq.1 Hrq.2.1 hl hn
      isplitr
      · cases hig : o.ignoreLease
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        · simp only [↓reduceIte]
          simp only [srvApi.stAt]
          iapply Hlok; ipureintro; first | exact hig | trivial | rfl
      iintro #Hwit
      ihave #Hwit' : Perennial.EtcdGrove.lease.winWit (mvcc.api.mvccLeases E.γ) E.win (mvcc.leaseItemsOf (mvcc.stateAfter
          (mvcc.commitLog log (txn.putPend o (srvApi.stAt log c))))) $$ [Hwit]
      · rw [← txn.pendItems_commitLog]; simp only [srvApi.stAt] at *; iexact Hwit
      iapply apply.commitAU_of_auEnd
      ihave He := HauE $$ %log %c %_ %E.win Hw HWt Hnx
        %(fun _ => apply.putWinTgt E.win rq o log c L Hwt Hrq.1 Hrq.2.1 hl) Hwit'
      iapply apply.auEnd_wand $$ He
      iintro HY
      isplitr
      · ipureintro; rfl
      iexact HY
    · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
      isplitr
      · itrivial
      iframe Hw HWt
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
      Pre Q Post E.f L (mvcc.leaseItemsOf (mvcc.stateAfter log)) none false _ E.win)
      $$ [$Hkv $Hmr $Hle $Hu $Hr $HlgN $Hkb $Hcs $Hau]
    as %resp %trace %err ⟨Hmr, Hkb, %Htrn, ⟨%te', Htrc⟩, -, Hout⟩
  · isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    ipureintro; exact Hrq.2.2.2
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
    · iexists L
      isplitl []
      · ipureintro
        simp only [apply.leaseExactL, hk]
        intro op hop; rw [hput] at hop; cases hop
        exact ⟨fun _ => rfl, fun _ => Or.inl ⟨Hnl, Hnin⟩⟩
      iapply (apply.kvOwnAt_of_split E log B c L)
      iframe Hw0 Htie Hbk Hhk Hard Hknown Hu HltL
    iright; iframe HPre; ipureintro
    (first | exact ⟨rfl, trivial⟩ | (simp only [apply.Outcome.logAfter]; exact ⟨rfl, trivial⟩) | simp_all [apply.Outcome.logAfter, apply.revokeIds_rejected, apply.grantRest_rejected, apply.revokeRest_rejected])
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
        · iexists L
          isplitl []
          · ipureintro
            simp only [apply.leaseExactL, hk]
            intro op hop; rw [hput] at hop; cases hop
            exact ⟨fun _ => rfl, fun _ => Or.inr ⟨hn, hf⟩⟩
          iapply (apply.kvOwnAt_of_split E log B c L)
          iframe Hw' Htie Hbk Hhk Hard Hknown Hu HltL
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
      -- the lease live: a dead one left the writer's half at `log` (`Hw0`)
      by_cases hl : o.leaseID = W64 0 ∨ o.leaseID ∈ L
      rotate_left
      · try isimp only [show decide (o.leaseID = W64 0 ∨ o.leaseID ∈ L) = false from decide_eq_false hl,
          Bool.false_eq_true, ↓reduceIte] at Hw0
        icases Hw0 with ⟨Hw0, -⟩
        icases Hw' with ⟨Hw', -⟩
        iexfalso
        iapply (apply.wSt_ne_false E.γs log
          (log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) c c
          (fun h => by have := congrArg List.length h; simp at this))
        iframe Hw0 Hw'
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
      · iexists L
        isplitl []
        · ipureintro
          simp only [apply.leaseExactL, hk]
          intro op hop; rw [hput] at hop; cases hop
          exact ⟨fun h => (hl.elim h.1 h.2).elim, fun h => by cases h⟩
        iapply (apply.kvOwnAt_of_split E _ B c L)
        iframe Hw' Htie Hbk Hhk Hard
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
