/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Configuration__Clone.lean (241f27e).
-/
/-
The proof of `raft.(*Configuration).Clone`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Configuration__Clone

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

theorem github_com.hashicorp.raft.Configuration.Clone.wp_proof :
    github_com.hashicorp.raft.Configuration.Clone.spec (GF := GF) (hG := hG) := by
  intro p c ss dq dq'
  wp_start as ⟨Hp, Hs⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  wp_auto
  wp_apply (wp_slice_append slice.nil ([] : List Server) c.Servers' ss dq) $$ [Hs] as %s' ⟨Hs', -, Hs⟩
  · iframe Hs
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  iapply HΦ
  iframe Hs
  isplitl [Servers]
  · iapply typedPointsto_combine _ _ _ Hpn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · simp only [List.nil_append]; iexact Hs'

end proof

end Perennial
