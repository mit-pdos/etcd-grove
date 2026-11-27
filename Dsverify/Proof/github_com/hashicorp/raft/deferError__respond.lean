/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/deferError__respond.lean (241f27e).
-/
/-
The proof of `raft.(*deferError).respond`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond

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

theorem github_com.hashicorp.raft.deferError.respond.wp_proof :
    github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG) := by
  intro d Q err
  wp_start as Hpre
  unfold deferDone
  icases Hpre with (⟨Hresp, HQ⟩ | Hdone)
  · unfold deferResp
    icases Hresp with ⟨%ch, #Hch, (%Hnil | ⟨%γe, %Hne, #Hspsc, Hprod, Hr⟩)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
      wp_auto
      wp_apply (wp_spsc_send γe ch _ _ [] err) $$ [$Hspsc $Hprod HQ] as Hprod
      · iframe; ipureintro; rfl
      wp_apply (wp_spsc_close γe ch _ _ ([] ++ [err])) $$ [$Hspsc $Hprod]
      · ipureintro; simp
      iapply HΦ
      iexists ch; iframe #; iright; iframe
  · icases Hdone with ⟨%ch, #Hch, (%Hnil | Hr)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      wp_if_destruct
      · iapply HΦ
        iexists _; iframe #; ileft; ipureintro; rfl
      · iapply HΦ
        iexists ch; iframe #; iright; iframe

end proof

end Perennial
