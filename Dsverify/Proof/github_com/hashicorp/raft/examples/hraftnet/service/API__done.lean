/-
The proof of `service.API.done`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__done
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__Error
public import Dsverify.Spec.github_com.hashicorp.raft.errorFuture__Error

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

theorem github_com.hashicorp.raft.examples.hraftnet.service.futWait_ok (fi : GoInterface) (Q : GoInterface → IProp GF) :
    futWait fi Q ⊢ futWait fi Q ∗ ⌜∃ x, fi = GoInterface.ok x⌝ := by
  iintro H
  ihave %h : ⌜∃ x, fi = GoInterface.ok x⌝ $$ [H]
  · unfold futWait
    icases H with (⟨%e, %hfi, -⟩ | ⟨%f, %hfi, -⟩ | ⟨%f, %hfi, -⟩ | ⟨%f, %hfi, -⟩ | ⟨%f, %hfi, -⟩ |
      ⟨%f, %hfi, -⟩) <;> ipureintro <;> exact ⟨_, hfi⟩
  iframe; ipureintro; exact h

theorem github_com.hashicorp.raft.examples.hraftnet.service.API.done.wp_proof
    (wp_waitFuture : github_com.hashicorp.raft.examples.hraftnet.service.waitFuture.spec (GF := GF) (hG := hG))
    (wp_dErr : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (wp_eErr : github_com.hashicorp.raft.errorFuture.Error.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.API.done.spec (GF := GF) (hG := hG) := by
  intro a γ rc i fc alb fi Q
  wp_start as ⟨#Hapi, Hfut⟩
  unfold isAPI
  icases Hapi with ⟨%r, %fsm, %enq, %wt, #Hr, #Hfsm, #Henq, #Hwt, #Hisr, %Hresp, #Hst, #Hmu⟩
  ihave ⟨Hfut, %hfi⟩ := futWait_ok fi Q $$ Hfut
  obtain ⟨x, rfl⟩ := hfi
  wp_auto
  wp_apply (wp_waitFuture x _ Q wt (wp_futWait_Error wp_dErr.1 wp_dErr.2.1 wp_dErr.2.2.1
    wp_dErr.2.2.2.1 wp_dErr.2.2.2.2.1 wp_eErr x Q)) $$ [$Hpkg $Hfut] as %err %ok -
  rcases err with ei | _ <;> cases ok <;> wp_auto <;> iapply HΦ <;> itrivial

end proof

end Perennial
