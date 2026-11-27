/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/deferError__init.lean (241f27e).
-/
/-
The proof of `raft.(*deferError).init`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.deferError__init

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

theorem github_com.hashicorp.raft.deferError.init.wp_proof :
    github_com.hashicorp.raft.deferError.init.spec (GF := GF) (hG := hG) := by
  intro f Q ch0
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

end proof

end Perennial
