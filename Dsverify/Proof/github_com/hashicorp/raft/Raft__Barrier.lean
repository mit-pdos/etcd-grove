/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__Barrier.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).Barrier` (stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__Barrier
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__init
public import Perennial.Spec.time.After

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.Raft.Barrier.wp_proof
    (wp_init : github_com.hashicorp.raft.deferError.init.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.Barrier.spec (GF := GF) (hG := hG) := by
  intro r γ rc i sc tmo
  wp_start as ⟨#Hr, #Hsc⟩
  wp_auto
  ihave Hch := isRaft_chans r γ rc i $$ Hr
  unfold raftChans deadField deadChan
  icases Hch with ⟨⟨%applyCh, #HapplyCh, %γa, #Hbag⟩, -, -, -, -, -, -, -, -, ⟨%sdCh, #HsdCh, %γsd, #Hsd⟩, -⟩
  wp_if_destruct
  focus
    ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
    · iPkgInit
    wp_apply time.After.spec_pkgInit wp_After _ $$ [$Htime] as %tch %γt #Ht
    ihave Htm : (∃ tch : Loc, timer_ptr ↦ tch ∗
        (⌜tch = chan.nil⌝ ∨ ∃ γt, isChanBag (V := time.Time) γt tch (fun _ => iprop(True)))) $$ [timer]
    · iexists tch; iframe; iright; iexists γt; iexact Ht
    iclear Ht
  rotate_left
  focus
    ihave Htm : (∃ tch : Loc, timer_ptr ↦ tch ∗
        (⌜tch = chan.nil⌝ ∨ ∃ γt, isChanBag (V := time.Time) γt tch (fun _ => iprop(True)))) $$ [timer]
    · iexists _; iframe; ileft; ipureintro; rfl
  all_goals
    icases Htm with ⟨%tch, Htimer, Htch⟩
    irename «$r0» => Hf
    generalize «$r0_ptr» = f at *
    iStructNamed Hf
    simp only [zeroValDef] at *
    iStructNamed deferError
    wp_apply (lc := 2) wp_init f (barrierQ γ rc i sc) null $$ [$errCh]
      as ⟨%ch, %γe, %Hne, HerrCh, #Hspsc, Hprod, Hcons⟩
    ipersist HerrCh
    ipersist ShutdownCh
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the timer
      icases Htch with (%Hnil | ⟨%γt, #Ht⟩)
      · iright
        iapply chan.nilClausePre_recv time.Time _ _ Hnil
      · ileft
        simp only [chan.blockingClausePre]
        iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Ht
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Ht
        inext
        iintro %t -
        icases isRaftErr_of_init .enqueueTimeout $$ Hpkg with ⟨%e, #He⟩
        ihave #Hg : (globalAddr ErrEnqueueTimeout ↦□ e : IProp GF) $$ []
        · have h := isRaftErr_global (GF := GF) .enqueueTimeout e
          rw [show RaftErr.enqueueTimeout.var = ErrEnqueueTimeout from rfl] at h
          iapply h $$ He
        ihave %Hne := isRaftErr_nonnil .enqueueTimeout e $$ He
        wp_auto
        iapply HΦ
        unfold futWait
        ileft
        iexists e
        isplitr
        · ipureintro; rfl
        unfold barrierQ
        ileft; ipureintro; exact Hne
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- shutdownCh: never closed, never sent on
      ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sdCh, γsd
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hsd
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsd
      inext
      iintro %t Hf
      iexfalso; iexact Hf
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the send on applyCh
      ileft
      simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, applyCh, γa, f
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbag [log response dispatch responded Hprod]
      · unfold applyP
        iright
        iexists _, _, sc
        iframe
        iframe #
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownSlice_nil
        isplitr
        · iexists []; iapply ownSlice_nil
        unfold deferResp
        iexists ch
        iframe #
        iright
        iframe
        ipureintro; exact Hne
      inext
      wp_auto
      iapply HΦ
      unfold futWait
      iright; ileft
      iexists f
      isplitr
      · ipureintro; rfl
      unfold deferWait
      iexists ch, γe
      iframe
      iframe #
      rw [show (chan.nil : GoChan) = null from rfl]
      iframe #
      isplitr; · ipureintro; exact Hne
      ileft; ipureintro; rfl
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
