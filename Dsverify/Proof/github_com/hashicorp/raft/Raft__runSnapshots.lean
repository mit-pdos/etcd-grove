/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__runSnapshots.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).runSnapshots`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runSnapshots
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__shouldSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__takeSnapshot
public import Dsverify.Proof.github_com.hashicorp.raft.SnapBase

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

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.runSnapshots.wp_proof
    (wp_shouldSnapshot : github_com.hashicorp.raft.Raft.shouldSnapshot.spec (GF := GF) (hG := hG))
    (wp_takeSnapshot : github_com.hashicorp.raft.Raft.takeSnapshot.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_randomTimeout : github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.runSnapshots.spec (GF := GF) (hG := hG) :=
  fun r γ rc i tid => by
  wp_start as ⟨#Hr, Htok⟩
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sch, #Hsch, %γs, #Hsbag⟩
  ihave #Hall := isRaft_chans r γ rc i $$ Hr
  unfold raftChans
  icases Hall with ⟨-, -, -, -, -, -, ⟨%usch, #Husch, %γus, #Husbag⟩, -⟩
  ihave #HnnE := isRaftErr_of_init RaftErr.nothingNewToSnapshot $$ Hpkg
  icases HnnE with ⟨%eNN, #HeNN⟩
  ihave #HgNN := isRaftErr_global RaftErr.nothingNewToSnapshot eNN $$ HeNN
  dsimp only [RaftErr.var]
  wp_auto
  wp_for
  wp_apply wp_config $$ [$Hr] as %c %Hc
  wp_apply (lc := 2) wp_randomTimeout as %tch Htch
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the timer
    icases Htch with (%Hnil | ⟨%γt, #Ht⟩)
    · iright
      iapply chan.nilClausePre_recv time.Time _ _ Hnil
    ileft
    dsimp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    ihave #Htc := is_bag_is_chan _ _ _ $$ Ht
    iframe Htc
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Ht
    inext
    iintro %v -
    wp_auto
    wp_apply wp_shouldSnapshot $$ [$Hr $Htok] as %b Htok
    cases b
    · wp_auto
      wp_for_post
      iframe
    wp_auto
    wp_apply wp_takeSnapshot $$ [$Hr $Htok] as %id %err ⟨Htok, Herr⟩
    icases Herr with (%Herr | #Herr | #Herr | %Herr)
    · subst Herr
      wp_auto
      wp_for_post
      iframe
    rotate_left
    rotate_left
    · -- (stage 4) the configuration-index error (an `errors.New` leaf)
      obtain ⟨x, rfl⟩ := Herr
      wp_auto
      wp_apply snapProof.wp_Is_errorString _ x eNN $$ [$HeNN] as %b2 -
      cases b2 <;> wp_auto
      all_goals (wp_for_post; iframe)
    · ihave %Hne := isRaftErr_nonnil _ _ $$ Herr
      try wp_auto
      obtain ⟨ex, rfl⟩ : ∃ ex, err = GoInterface.ok ex := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok ex => exact ⟨ex, rfl⟩
      wp_auto
      wp_apply snapProof.wp_Is_raftErr _ _ (GoInterface.ok ex) eNN $$ [$Herr $HeNN] as %b2 -
      cases b2 <;> wp_auto
      all_goals (wp_for_post; iframe)
    · ihave %Hne := isRaftErr_nonnil _ _ $$ Herr
      try wp_auto
      obtain ⟨ex, rfl⟩ : ∃ ex, err = GoInterface.ok ex := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok ex => exact ⟨ex, rfl⟩
      wp_auto
      wp_apply snapProof.wp_Is_raftErr _ _ (GoInterface.ok ex) eNN $$ [$Herr $HeNN] as %b2 -
      cases b2 <;> wp_auto
      all_goals (wp_for_post; iframe)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a user snapshot request
    ileft
    dsimp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, usch, γus
    isplitr
    · ipureintro; rfl
    ihave #Hsc := is_bag_is_chan _ _ _ $$ Husbag
    iframe Hsc
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Husbag
    inext
    iintro %f Hf
    unfold userSnapP
    icases Hf with ⟨⟨%op, Hop⟩, Hresp⟩
    wp_auto
    wp_apply wp_takeSnapshot $$ [$Hr $Htok] as %id %err ⟨Htok, Herr⟩
    icases Herr with (%Herr | #Herr | #Herr | %Herr)
    · subst Herr
      repeat' (first | wp_if_destruct | wp_auto)
      wp_apply snapFut.wp_uf_respond wp_respond f (fun _ => iprop(True)) interface.nil $$ [Hresp] as -
      · ileft; iframe
      wp_for_post
      iframe
    rotate_left
    rotate_left
    · -- (stage 4) the configuration-index error (an `errors.New` leaf)
      obtain ⟨x, rfl⟩ := Herr
      wp_auto
      wp_apply snapProof.wp_Is_errorString _ x eNN $$ [$HeNN] as %b2 -
      cases b2 <;> wp_auto
      all_goals
        wp_apply snapFut.wp_uf_respond wp_respond f (fun _ => iprop(True)) _ $$ [Hresp] as -
        · ileft; iframe
        wp_for_post
        iframe
    all_goals
      ihave %Hne := isRaftErr_nonnil _ _ $$ Herr
      try wp_auto
      obtain ⟨ex, rfl⟩ : ∃ ex, err = GoInterface.ok ex := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok ex => exact ⟨ex, rfl⟩
      wp_auto
      wp_apply snapProof.wp_Is_raftErr _ _ (GoInterface.ok ex) eNN $$ [$Herr $HeNN] as %b2 -
      cases b2 <;> wp_auto
      all_goals
        wp_apply snapFut.wp_uf_respond wp_respond f (fun _ => iprop(True)) (GoInterface.ok ex) $$ [Hresp] as -
        · ileft; iframe
        wp_for_post
        iframe

  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sch, γs
    isplitr
    · ipureintro; rfl
    ihave #Hsc := is_bag_is_chan _ _ _ $$ Hsbag
    iframe Hsc
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsbag
    inext
    iintro %v HF
    iexfalso; iexact HF
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
