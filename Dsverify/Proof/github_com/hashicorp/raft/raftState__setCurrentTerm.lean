/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__setCurrentTerm.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).setCurrentTerm` (the embedded receiver): an atomic store
to the term cell, with the caller's protocol step at the store.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setCurrentTerm
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers
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

theorem github_com.hashicorp.raft.raftState.setCurrentTerm.wp_proof :
    github_com.hashicorp.raft.raftState.setCurrentTerm.spec (GF := GF) (hG := hG) := by
  intro r γ rc i x Q
  wp_start as ⟨#Hcell, Hupd⟩
  wp_auto
  wp_apply_core sync.atomic.wp_StoreUint64_nc _ _ $$ [] [-]
  · iPkgInit
  iintro Hnc
  unfold termCell termV
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hi, Hclose⟩
  icases Hi with ⟨%t, >Hpt, >Hc⟩
  ihave Hu := Hupd $$ %(uint.nat t) Hc
  imod Hu $$ Hnc with ⟨Hnc, Hc, HQ⟩
  iframe Hnc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists t
  iframe Hpt
  iintro Hpt
  imod Hmask with -
  imod Hclose $$ [Hpt Hc] with -
  · inext; iexists x; iframe
  imodintro
  wp_auto
  iapply HΦ $$ HQ

end proof

end Perennial
