/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__run.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).run`: the main loop, forever (`shutdownCh` is never closed).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__run
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runFollower
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runCandidate
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runLeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader

@[expose] public section

set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

/-- A receive clause of a nonblocking select on a dead channel, without a later credit (the
invariant's content is only needed under the update's `▷`). -/
theorem dead_nb_clause' {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (γc : ChanNames) (ch : Loc) (body : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := V) γc ch (fun _ => iprop(False)) -∗
      chan.nonblockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro #Hb
  simp only [chan.nonblockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan γc ch _ $$ Hb
  unfold nonblockingRecvAu
  isplit
  · rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
    icases Hb with ⟨#Hch, #Hinv⟩
    iapply ncfupd_of_fupd
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    unfold chanBagInv
    icases Hi with ⟨%s, Hoc0, Hi⟩
    iexists s
    iframe Hoc0
    rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
    all_goals dsimp only
    all_goals first | itrivial | (iexfalso; iexact Hi) | skip
    all_goals first | (icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, -⟩; iexfalso; iexact HP) | skip
  · itrivial

/-- The main goroutine's half of the `state` ghost variable, out of `mainOwnAt`. -/
theorem mainOwnAt_state (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ ghostVar rc.names.state (1 : Qp).half st ∗
      (ghostVar rc.names.state (1 : Qp).half st -∗ mainOwnAt r γ rc i s st) := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, H1, -, H3, %H4, H5, Hst, H7⟩
  iframe Hst
  iintro Hst
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  iframe
  ipureintro; exact H4

theorem github_com.hashicorp.raft.Raft.run.wp_proof
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG))
    (wp_runFollower : github_com.hashicorp.raft.Raft.runFollower.spec (GF := GF) (hG := hG))
    (wp_runCandidate : github_com.hashicorp.raft.Raft.runCandidate.spec (GF := GF) (hG := hG))
    (wp_runLeader : github_com.hashicorp.raft.Raft.runLeader.spec (GF := GF) (hG := hG))
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.run.spec (GF := GF) (hG := hG) :=
  fun r γ rc i tid => by
  wp_start as ⟨#Hr, Hm, Hls, Htok⟩
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sch, #Hsch, %γsd, #Hsdb⟩
  ihave #Hsc := isRaft_stateCell r γ rc i $$ Hr
  wp_auto
  wp_for
  wp_apply_core chan.wp_select_nonblocking_nil
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply dead_nb_clause' γsd sch _ _ $$ Hsdb
    iapply BigAndL.bigAndL_nil.2
    itrivial
  wp_auto
  icases (mainOwn_unfold r γ rc i).1 $$ Hm with ⟨%s, %st, Hm, Hl0⟩
  icases mainOwnAt_state r γ rc i s st $$ Hm with ⟨Hst, Hm⟩
  wp_apply (wp_getState.1 r rc st) $$ [$Hsc $Hst] with Hst
  ihave Hm := Hm $$ Hst
  wp_if_destruct
  · wp_apply (wp_runFollower r γ rc i) $$ [Hm Hl0 Htok] with ⟨Hm, Htok⟩
    · iframe; iframe #; iapply mainOwn_intro; iframe
    wp_for_post
    iframe
  wp_if_destruct
  · wp_apply (wp_runCandidate r γ rc i s) $$ [Hm Htok] with ⟨Hm, Htok⟩
    · iframe; iframe #
    wp_for_post
    iframe
  wp_if_destruct
  · icases Hl0 with (%Hne | ⟨#Hlen0, Hcc2⟩)
    · exact absurd rfl Hne
    wp_apply (wp_runLeader r γ rc i s) $$ [Hm Hls Htok Hcc2] with ⟨Hm, Hls, Htok⟩
    · iframe; iframe #
    wp_for_post
    iframe
  wp_for_post
  iframe
  iapply mainOwn_intro; iframe

end proof

end Perennial
