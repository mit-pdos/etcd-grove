/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__CurrentTerm.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).CurrentTerm`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__CurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap

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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

/-- The term cell gives the (trivial) lower bound `0` on the term. -/
theorem github_com.hashicorp.raft.termCell_lb0 (r : Loc) (γ : gprot.GNames) (rc : RCtx GF) (i : SID) :
    £ 1 ∗ termCell (GF := GF) r γ rc i ∗ srvDurInv γ rc i ⊢ |NC={⊤}=> gprot.termLb γ i 0 := by
  iintro ⟨-, #Hc, #Hdur⟩ Hnc
  ihave Hacc := durOpen γ rc i (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hdur
  imod Hacc $$ Hnc with ⟨Hnc, %X, HX, HXs, Hclose⟩
  unfold durCore
  icases HX with ⟨Ho, Hdv, Hlc, Htc, Hrest⟩
  ihave ⟨Htc, #Hlb⟩ := termCouple_get_lb γ i _ $$ Htc
  imod Hclose $$ %X [Ho Hdv Hlc Htc Hrest] HXs with -
  · iframe
  imodintro
  iframe Hnc
  iapply termLb_mono γ i _ 0 (Nat.zero_le _) $$ Hlb

theorem github_com.hashicorp.raft.Raft.CurrentTerm.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.CurrentTerm.spec (GF := GF) (hG := hG) := by
  constructor
  · intro r γ rc i s
    wp_start as ⟨#Hinv, #Hc, #Hdur, Hs⟩
    wp_auto
    wp_apply wp_getCurrentTerm.1 $$ [$Hinv $Hc $Hdur $Hs] as Hs
    iapply HΦ $$ Hs
  · intro r γ rc i s0
    wp_start as ⟨#HInv, #Hvi, #Hcell, #Hdur, #Hs0⟩
    wp_auto
    wp_method_call; wp_call
    try wp_auto
    wp_method_call; wp_call
    try wp_auto
    wp_apply_core sync.atomic.wp_LoadUint64_nc _ (DFrac.own 1) $$ [] [-]
    · iPkgInit
    iintro Hnc
    unfold termCell
    imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hi, Hclose⟩
    ihave Hacc := durOpen γ rc i durN_diff_termN $$ Hdur
    imod Hacc $$ Hnc with ⟨Hnc, %X, HX, HXs, Hclose2⟩
    iframe Hnc
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%t, Hpt, Hc⟩
    iexists t
    iframe Hpt
    iintro Hpt
    imod Hmask with -
    unfold durCore
    icases HX with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hrest⟩
    unfold termV
    icombine Htv Hc gives %ht
    imod termCouple_now γ _ gprotN_diff_termN_durN i _ s0 $$ [HInv Hvi Htc Hs0]
      with ⟨Htc, %s', #Hs', %Hle⟩
    · iframe; iframe #
    imod Hclose2 $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hrest] HXs with -
    · iframe
    imod Hclose $$ [Hpt Hc] with -
    · inext; iexists t; iframe
    imodintro
    wp_auto
    iapply HΦ
    iexists s'
    iframe #
    ipureintro; rw [← ht.2]; exact Hle

end proof

end Perennial
