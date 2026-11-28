/-
The proof of `service.API.Apply` (adapted from dsverify-lab's hr3 `apply.lean`, 241f27e): the
future's answer (`futDone`), classified by comparing the error with raft's error values (distinct
pointers, `isRaftErr_ne`); a nil error carries the committed entry and the FSM's response.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__Apply
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__Apply
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__Error
public import Dsverify.Spec.github_com.hashicorp.raft.errorFuture__Error
public import Dsverify.Spec.github_com.hashicorp.raft.logFuture__Response

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

set_option goose.wp.extras true
set_option linter.unusedSimpArgs false

theorem github_com.hashicorp.raft.examples.hraftnet.service.isRaftErr_shape (c : RaftErr) (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaftErr c e ⊢
      ⌜∃ l : Loc, e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #l⌝ := by
  iintro ⟨#Hpkg, #He⟩
  ihave #Hn := newVar_of_init c $$ Hpkg
  ihave #Hg := isRaftErr_global c e $$ He
  unfold errors.newVar
  icases Hn with ⟨%l, #Hl, -⟩
  icombine Hg Hl gives %h
  ipureintro; exact ⟨l, h⟩

theorem github_com.hashicorp.raft.examples.hraftnet.service.futureOwn_ok (γ : GNames) (rc : RCtx GF)
    (fi : GoInterface) (d : List w8) (m : Nat) :
    futureOwn γ rc fi d m ⊢ futureOwn γ rc fi d m ∗ ⌜∃ x, fi = GoInterface.ok x⌝ := by
  unfold futureOwn
  iintro (⟨%e, %hfi, H1, H2⟩ | ⟨%f, %hfi, H⟩)
  · isplitl
    · ileft; iexists e; iframe; ipureintro; exact hfi
    · ipureintro; exact ⟨_, hfi⟩
  · isplitl
    · iright; iexists f; iframe; ipureintro; exact hfi
    · ipureintro; exact ⟨_, hfi⟩

set_option hygiene false in
/-- `wp_auto`, deciding the comparisons of the error values (their pointers are distinct). -/
local macro "wp_errs" : tactic => `(tactic|
  (iterate 4 ((try wp_auto); (try simp only [d1, d2, d3, d4, d5, d6, d1', d2', d3', d4', d5', d6']))))

theorem github_com.hashicorp.raft.examples.hraftnet.service.API.Apply.wp_proof
    (wp_Apply : github_com.hashicorp.raft.Raft.Apply.spec (GF := GF) (hG := hG))
    (wp_waitFuture : github_com.hashicorp.raft.examples.hraftnet.service.waitFuture.spec (GF := GF) (hG := hG))
    (wp_dErr : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (wp_eErr : github_com.hashicorp.raft.errorFuture.Error.spec (GF := GF) (hG := hG))
    (wp_lResp : github_com.hashicorp.raft.logFuture.Response.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.API.Apply.spec (GF := GF) (hG := hG) := by
  intro a args reply γ rc i fc alb sl d n rep0
  wp_start as ⟨#Hapi, #Hargs, #Hd, Htok, Hrep⟩
  ihave #Hraft : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft) $$ []
  · iPkgInit
  unfold isAPI
  icases Hapi with ⟨%r, %fsm, %enq, %wt, #Hr, #Hfsm, #Henq, #Hwt, #Hisr, %Hresp, #Hst, #Hmu⟩
  iStructNamed Hargs
  wp_auto
  wp_apply wp_Apply $$ [$Hraft $Hisr $Hd $Htok] as %fi Hfut
  ihave ⟨Hfut, %hfi⟩ := futureOwn_ok γ rc fi d n $$ Hfut
  obtain ⟨x, rfl⟩ := hfi
  wp_apply (wp_waitFuture x _ (futDone γ rc (GoInterface.ok x) d n) wt
    (wp_future_Error wp_dErr.1 wp_eErr γ rc x d n)) $$ [$Hpkg $Hfut] as %err %ok Hw
  icases isRaftErr_of_init .notLeader $$ Hraft with ⟨%eNL, #HNL⟩
  icases isRaftErr_of_init .enqueueTimeout $$ Hraft with ⟨%eET, #HET⟩
  icases isRaftErr_of_init .leadershipTransferInProgress $$ Hraft with ⟨%eLT, #HLT⟩
  icases isRaftErr_of_init .leadershipLost $$ Hraft with ⟨%eLL, #HLL⟩
  have hgNL := isRaftErr_global (GF := GF) .notLeader eNL
  simp only [RaftErr.var] at hgNL
  ihave #HgNL := hgNL $$ HNL
  have hgET := isRaftErr_global (GF := GF) .enqueueTimeout eET
  simp only [RaftErr.var] at hgET
  ihave #HgET := hgET $$ HET
  have hgLT := isRaftErr_global (GF := GF) .leadershipTransferInProgress eLT
  simp only [RaftErr.var] at hgLT
  ihave #HgLT := hgLT $$ HLT
  ihave %hNL := isRaftErr_shape .notLeader eNL $$ [Hraft HNL]
  · iframe #
  ihave %hET := isRaftErr_shape .enqueueTimeout eET $$ [Hraft HET]
  · iframe #
  ihave %hLT := isRaftErr_shape .leadershipTransferInProgress eLT $$ [Hraft HLT]
  · iframe #
  ihave %hLL := isRaftErr_shape .leadershipLost eLL $$ [Hraft HLL]
  · iframe #
  ihave %n1 := isRaftErr_ne .notLeader .enqueueTimeout eNL eET (by decide) $$ [HNL HET]
  · iframe #
  ihave %n2 := isRaftErr_ne .notLeader .leadershipTransferInProgress eNL eLT (by decide) $$ [HNL HLT]
  · iframe #
  ihave %n3 := isRaftErr_ne .enqueueTimeout .leadershipTransferInProgress eET eLT (by decide)
    $$ [HET HLT]
  · iframe #
  ihave %n4 := isRaftErr_ne .leadershipLost .notLeader eLL eNL (by decide) $$ [HLL HNL]
  · iframe #
  ihave %n5 := isRaftErr_ne .leadershipLost .enqueueTimeout eLL eET (by decide) $$ [HLL HET]
  · iframe #
  ihave %n6 := isRaftErr_ne .leadershipLost .leadershipTransferInProgress eLL eLT (by decide)
    $$ [HLL HLT]
  · iframe #
  obtain ⟨lNL, rfl⟩ := hNL
  obtain ⟨lET, rfl⟩ := hET
  obtain ⟨lLT, rfl⟩ := hLT
  obtain ⟨lLL, rfl⟩ := hLL
  have m1 : lNL ≠ lET := fun h => n1 (by rw [h])
  have m2 : lNL ≠ lLT := fun h => n2 (by rw [h])
  have m3 : lET ≠ lLT := fun h => n3 (by rw [h])
  have m4 : lLL ≠ lNL := fun h => n4 (by rw [h])
  have m5 : lLL ≠ lET := fun h => n5 (by rw [h])
  have m6 : lLL ≠ lLT := fun h => n6 (by rw [h])
  have dne : ∀ a b : Loc, a ≠ b → decide (a = b) = false := fun a b h => decide_eq_false h
  have d1 := dne _ _ m1
  have d2 := dne _ _ m2
  have d3 := dne _ _ m3
  have d4 := dne _ _ m4
  have d5 := dne _ _ m5
  have d6 := dne _ _ m6
  have d1' := dne _ _ (Ne.symm m1)
  have d2' := dne _ _ (Ne.symm m2)
  have d3' := dne _ _ (Ne.symm m3)
  have d4' := dne _ _ (Ne.symm m4)
  have d5' := dne _ _ (Ne.symm m5)
  have d6' := dne _ _ (Ne.symm m6)
  clear dne
  icases Hw with (%hok | ⟨%hok, Hdone⟩)
  · subst hok
    wp_auto
    simp only [StatusUnknown]
    wp_auto
    iapply HΦ
    iexists _
    iframe
    unfold applyOut
    iright; ileft; ipureintro; rfl
  subst hok
  wp_auto
  unfold futDone
  icases Hdone with (⟨(#H1 | #H1 | #H1), Htok⟩ | ⟨%hnil, %f, %k, %e, %rr, %hfi, #Hc, %he, Hresp', Hf⟩ | #H1)
  · ihave %herr := isRaftErr_agree .notLeader err
      (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #lNL) $$ [H1 HNL]
    · iframe #
    cases herr
    wp_errs
    simp only [StatusNoEffect]
    wp_errs
    iapply HΦ; iexists _; iframe; unfold applyOut; ileft; iframe; ipureintro; rfl
  · ihave %herr := isRaftErr_agree .leadershipTransferInProgress err
      (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #lLT) $$ [H1 HLT]
    · iframe #
    cases herr
    wp_errs
    simp only [StatusNoEffect]
    wp_errs
    iapply HΦ; iexists _; iframe; unfold applyOut; ileft; iframe; ipureintro; rfl
  · ihave %herr := isRaftErr_agree .enqueueTimeout err
      (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #lET) $$ [H1 HET]
    · iframe #
    cases herr
    wp_errs
    simp only [StatusNoEffect]
    wp_errs
    iapply HΦ; iexists _; iframe; unfold applyOut; ileft; iframe; ipureintro; rfl
  · -- committed
    cases hnil
    wp_errs
    simp only [interface.mkOk] at hfi
    cases hfi
    wp_apply wp_future_Response wp_lResp f rr (DFrac.own 1) $$ [$Hraft $Hf] as Hf
    rw [Hresp]
    unfold respP
    icases Hresp' with ⟨%es, ⟨%hes, %hrr⟩, #Hes, #Hfl, -⟩
    subst hrr
    wp_auto
    simp only [StatusDone]
    wp_auto
    iapply HΦ; iexists _; iframe; unfold applyOut; iright; iright
    isplitr; · ipureintro; rfl
    iexists k, e, es
    iframe #
    ipureintro; exact ⟨he.1, he.2, hes, rfl⟩
  · ihave %herr := isRaftErr_agree .leadershipLost err
      (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #lLL) $$ [H1 HLL]
    · iframe #
    cases herr
    wp_errs
    simp only [StatusUnknown]
    wp_errs
    iapply HΦ; iexists _; iframe; unfold applyOut; iright; ileft; ipureintro; rfl

end proof

end Perennial
