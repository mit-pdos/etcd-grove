/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__setLastApplied.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).setLastApplied` (called through `*Raft`): an atomic store
to the `lastApplied` cell, updating both halves of its ghost variable.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastApplied
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.LastLock
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers

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

theorem github_com.hashicorp.raft.raftState.setLastApplied.wp_proof :
    github_com.hashicorp.raft.raftState.setLastApplied.spec (GF := GF) (hG := hG) := by
  intro r rc x
  wp_start as #Hcell
  wp_method_call; wp_call
  wp_auto
  wp_apply_core sync.atomic.wp_StoreUint64_nc _ _ $$ [] [-]
  · iPkgInit
  iintro Hnc
  unfold appliedCell
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hi, Hclose⟩
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imodintro
  iframe Hnc
  inext
  icases Hi with ⟨%y, Hpt, Hg'⟩
  icases HAU with ⟨%a, Ha, %Hax, Hcl⟩
  iexists y
  iframe Hpt
  iintro Hpt
  imod applied_halves_update rc a (uint.nat y) (uint.nat x) Hax $$ [$Ha $Hg'] with ⟨-, Ha, Hg'⟩
  imod Hcl $$ Ha with HΦ
  imod Hclose $$ [Hpt Hg'] with -
  · inext; iexists x; iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
