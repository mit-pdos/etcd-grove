/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setLatestConfiguration.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setLatestConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Configuration__Clone
public import Perennial.Spec.sync.atomic.Pointer__Store

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

theorem github_com.hashicorp.raft.Raft.setLatestConfiguration.wp_proof
    (wp_Clone : github_com.hashicorp.raft.Configuration.Clone.spec (GF := GF) (hG := hG))
    (wp_Store : sync.atomic.Pointer.Store.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG) := by
  intro b r γ c0 l i0 li c ci ss dq p0
  cases b
  · -- the invariant cell (installSnapshot, the main goroutine)
    wp_start as ⟨Hconf, Hs, Hif⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hif with ⟨%Hss, #Hinv⟩
    wp_auto
    wp_apply wp_Clone $$ [$c $Hs] as %c' ⟨c, Hs, Hs'⟩
    imod ownSlice_persist $$ Hs' with #Hs'
    ipersist cc
    wp_apply (wp_Store (T' := Configuration) Configuration.ty)
    imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    unfold latestCfgCell
    icases Hi with ⟨%p, Hv, -⟩
    iexists p
    iframe Hv
    iintro Hv
    imod Hmask with -
    imod Hclose $$ [Hv] with -
    · inext; iexists cc_ptr; iframe; iright; iexists c'; iframe #
      unfold cfgOpt; iexists ss; iframe #; ipureintro; exact Hss
    imodintro
    wp_auto
    iapply HΦ
    iframe
  · -- the caller's cell (NewRaft)
    wp_start as ⟨Hconf, Hs, Hv⟩
    simp only [↓reduceIte]
    wp_auto
    wp_apply wp_Clone $$ [$c $Hs] as %c' ⟨c, Hs, Hs'⟩
    ipersist cc
    wp_apply (wp_Store (T' := Configuration) Configuration.ty)
    iapply fupd_mask_intro (by simp)
    iintro Hclose
    inext
    iexists p0
    iframe Hv
    iintro Hv
    imod Hclose
    imodintro
    wp_auto
    iapply HΦ
    iframe
    iframe #
  /- stage-3 proof:
  := by
  intro b r γ c0 l i0 li c ci ss dq p0
  cases b
  · -- the invariant cell (installSnapshot)
    wp_start as ⟨Hconf, Hs, Hif⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hif with ⟨%Hss, #Hinv⟩
    wp_auto
    wp_apply wp_Clone $$ [$c $Hs] as %c' ⟨c, Hs, Hs'⟩
    imod ownSlice_persist $$ Hs' with #Hs'
    ipersist cc
    wp_apply (wp_Store (T' := Configuration) Configuration.ty)
    imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    unfold latestCfgCell
    icases Hi with ⟨%p, %cfg, Hv, -, -⟩
    iexists p
    iframe Hv
    iintro Hv
    imod Hmask with -
    imod Hclose $$ [Hv] with -
    · inext; iexists cc_ptr, c'; iframe; iframe #
      unfold cfgIs; iexists ss; iframe #; ipureintro; exact Hss
    imodintro
    wp_auto
    iapply HΦ
    iframe
  · -- the caller's cell (NewRaft)
    wp_start as ⟨Hconf, Hs, Hv⟩
    simp only [↓reduceIte]
    wp_auto
    wp_apply wp_Clone $$ [$c $Hs] as %c' ⟨c, Hs, Hs'⟩
    ipersist cc
    wp_apply (wp_Store (T' := Configuration) Configuration.ty)
    iapply fupd_mask_intro (by simp)
    iintro Hclose
    inext
    iexists p0
    iframe Hv
    iintro Hv
    imod Hclose
    imodintro
    wp_auto
    iapply HΦ
    iframe
    iframe #
  -/

end proof

end Perennial
