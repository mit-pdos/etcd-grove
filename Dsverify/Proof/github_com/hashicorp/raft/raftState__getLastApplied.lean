/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__getLastApplied.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).getLastApplied` (called through `*Raft`): an atomic load of
the `lastApplied` cell.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastApplied
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

theorem github_com.hashicorp.raft.raftState.getLastApplied.wp_proof :
    github_com.hashicorp.raft.raftState.getLastApplied.spec (GF := GF) (hG := hG) := by
  intro r rc a
  wp_start as ⟨#Hcell, Hg⟩
  wp_method_call; wp_call
  wp_auto
  wp_apply_core sync.atomic.wp_LoadUint64 _ (DFrac.own 1) $$ [] [-]
  · iPkgInit
  unfold appliedCell
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%x, Hpt, Hg'⟩
  iexists x
  iframe Hpt
  iintro Hpt
  imod Hmask with -
  ihave %he := monoNatAuthOwn_agree _ _ _ _ _ $$ Hg Hg'
  imod Hclose $$ [Hpt Hg'] with -
  · inext; iexists x; iframe
  imodintro
  wp_auto
  iapply HΦ
  iframe
  ipureintro; exact he.2.symm

end proof

end Perennial
