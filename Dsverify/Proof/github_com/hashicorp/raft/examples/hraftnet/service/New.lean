/-
The proof of `service.New`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.New

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

theorem github_com.hashicorp.raft.examples.hraftnet.service.New.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.service.New.spec (GF := GF) (hG := hG) := by
  intro r fsm enq wt γ rc i fc alb
  wp_start as ⟨#Hr, %Hresp, #Hs⟩
  iapply wp_fupd
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  imod sync.init_Mutex (apiMuInv «$r0_ptr» γ i fc alb) ⊤ (structFieldRef API go!"mu" «$r0_ptr») $$ [mu] [barrierIn] with #Hmu
  · iexact mu
  · unfold apiMuInv; inext; iexists _; iframe barrierIn; ileft; ipureintro; rfl
  ipersist r
  ipersist fsm
  ipersist enqueue
  ipersist wait
  imodintro
  iapply HΦ
  isplitr
  · unfold isAPI
    iexists r, fsm, enq, wt
    iframe #
    ipureintro; exact Hresp
  · ipureintro; exact Hnn

end proof

end Perennial
