/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__getCurrentTerm.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).getCurrentTerm` (called through `*Raft`): an atomic load of the
term cell.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.raftState.getCurrentTerm.wp_proof :
    github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG) := by
  constructor
  · intro r γ i s
    wp_start as ⟨#HInv, #Hcell, Hs⟩
    wp_method_call; wp_call
    wp_auto
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
    imod termCouple_agree γ (⊤ \ ↑termN) gprotN_diff_termN i s _ $$ [HInv Hs Hc] with ⟨Hs, Hc, %ht⟩
    · iframe; iframe #
    imod Hclose $$ [Hpt Hc] with -
    · inext; iexists t; iframe
    imodintro
    wp_auto
    have : t = W64 (s.term : Int) := by rw [← ht]; word
    subst this
    iapply HΦ $$ Hs
  · intro r γ i t0
    wp_start as ⟨#Hcell, #Hlb⟩
    wp_method_call; wp_call
    wp_auto
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
    ihave %hle := termCouple_lb γ i _ t0 $$ [Hc Hlb]
    · iframe; iframe #
    ihave ⟨Hc, #Hlb'⟩ := termCouple_get_lb γ i _ $$ Hc
    imod Hclose $$ [Hpt Hc] with -
    · inext; iexists t; iframe
    imodintro
    wp_auto
    iapply HΦ
    iframe #
    ipureintro; exact hle

end proof

end Perennial
