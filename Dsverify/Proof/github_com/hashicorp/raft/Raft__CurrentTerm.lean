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
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers
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
theorem github_com.hashicorp.raft.termCell_lb0 (r : Loc) (γ : gprot.GNames) (i : SID) :
    £ 1 ∗ termCell (GF := GF) r γ i ⊢ |={⊤}=> gprot.termLb γ i 0 := by
  iintro ⟨Hlc, #Hc⟩
  unfold termCell
  iinv Hc with ⟨%t, >Hp, Hcpl⟩ Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑termN) $$ Hlc Hcpl with Hcpl
  unfold gprot.termCouple
  ihave #Hlb := monoNatLbOwn_get (γ.term i) _ _ $$ Hcpl
  imod Hclose $$ [Hp Hcpl] with _
  · inext; iexists t; iframe
  imodintro
  unfold gprot.termLb
  iapply monoNatLbOwn_le 0 (Nat.zero_le _) $$ Hlb

theorem github_com.hashicorp.raft.Raft.CurrentTerm.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.CurrentTerm.spec (GF := GF) (hG := hG) := by
  constructor
  · intro r γ i s
    wp_start as ⟨#Hinv, #Hc, Hs⟩
    wp_auto
    wp_apply wp_getCurrentTerm.1 $$ [$Hinv $Hc $Hs] as Hs
    iapply HΦ $$ Hs
  · -- witness form: the atomic load, with `termCouple_now` inside the cell's invariant
    intro r γ i s0
    wp_start as ⟨#HInv, #Hvi, #Hcell, #Hs0⟩
    wp_auto
    wp_method_call; wp_call
    try wp_auto
    wp_method_call; wp_call
    try wp_auto
    wp_apply_core sync.atomic.wp_LoadUint64 _ (DFrac.own 1) $$ [] [-]
    · iPkgInit
    unfold termCell
    imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hi, Hclose⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%t, Hpt, Hc⟩
    iexists t
    iframe Hpt
    iintro Hpt
    imod Hmask with -
    imod termCouple_now γ (⊤ \ ↑termN) gprotN_diff_termN i _ s0 $$ [HInv Hvi Hc Hs0]
      with ⟨Hc, %s', #Hs', %Hle⟩
    · iframe; iframe #
    imod Hclose $$ [Hpt Hc] with -
    · inext; iexists t; iframe
    imodintro
    wp_auto
    iapply HΦ
    iexists s'
    iframe #
    ipureintro; exact Hle

end proof

end Perennial
