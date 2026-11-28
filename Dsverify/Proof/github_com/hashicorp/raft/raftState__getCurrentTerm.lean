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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.raftState.getCurrentTerm.wp_proof :
    github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG) := by
  constructor
  · intro r γ rc i s
    wp_start as ⟨#HInv, #Hcell, #Hdur, Hs⟩
    wp_method_call; wp_call
    wp_auto
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
    icases HX with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hrest⟩
    unfold srvV termV
    icombine Hsv Hs gives %hs
    icases Hrest with ⟨Hst, Htv, Hrest⟩
    icombine Htv Hc gives %ht
    imod Hclose2 $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hrest] HXs with -
    · iframe
    imod Hclose $$ [Hpt Hc] with -
    · inext; iexists t; iframe
    imodintro
    wp_auto
    have hs' : X.s = s := (Prod.mk.inj hs.2).1
    have : t = W64 (s.term : Int) := by rw [← hs', ht.2]; word
    subst this
    iapply HΦ $$ Hs
  · intro r γ rc i t0
    wp_start as ⟨#Hcell, #Hdur, #Hlb⟩
    wp_method_call; wp_call
    wp_auto
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
    ihave %hle := termCouple_lb γ i _ t0 $$ [Htc Hlb]
    · iframe; iframe #
    ihave ⟨Htc, #Hlb'⟩ := termCouple_get_lb γ i _ $$ Htc
    imod Hclose2 $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hrest] HXs with -
    · iframe
    imod Hclose $$ [Hpt Hc] with -
    · inext; iexists t; iframe
    imodintro
    wp_auto
    iapply HΦ
    rw [← ht.2]
    iframe #
    ipureintro; exact hle

end proof

end Perennial
