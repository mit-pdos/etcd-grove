/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__setState.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).setState` (the embedded receiver): an atomic store to the
`state` cell, updating both halves of its ghost variable.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setState
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers

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

theorem github_com.hashicorp.raft.raftState.setState.wp_proof :
    github_com.hashicorp.raft.raftState.setState.spec (GF := GF) (hG := hG) := by
  intro r rc st0 st
  wp_start as ⟨#Hcell, Hg, %hst⟩
  wp_auto
  wp_apply_core sync.atomic.wp_StoreUint32 _ _ $$ [] [-]
  · iPkgInit
  unfold stateCell
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%y, Hpt, Hg', %hy⟩
  iexists y
  iframe Hpt
  iintro Hpt
  imod Hmask with -
  imod ghostVar_update_halves st _ _ _ $$ Hg Hg' with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hpt Hg'] with -
  · inext; iexists st; iframe; ipureintro; exact hst
  imodintro
  wp_auto
  iapply HΦ $$ Hg

end proof

end Perennial
