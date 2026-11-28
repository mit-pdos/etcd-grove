/-
(hraft_robust R5) The proof of `raft.(*Raft).tryRestoreSingleSnapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__tryRestoreSingleSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.fsmRestoreAndMeasure

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

theorem github_com.hashicorp.raft.Raft.tryRestoreSingleSnapshot.wp_proof
    (wp_fsmRestoreAndMeasure : github_com.hashicorp.raft.fsmRestoreAndMeasure.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.tryRestoreSingleSnapshot.spec (GF := GF) (hG := hG) := by
  intro r c x fx own eof Qc γ i fsmOwn respP snapP mp m b P k0 tid
  wp_start as ⟨#Hconf, %Hnsr, #Hsnaps, #Hsn, #Heof, #Hfsml, #Hfsm, Hmp, HP, Hacc, HsnapP, Hfo, %Hk0, Htok⟩
  wp_auto
  -- r.config(), inlined
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"config")]
  wp_call
  wp_auto
  wp_apply_core sync.atomic.Value.wp_Load _ DFrac.discard $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Hconf
  iintro _
  imod Hmask with -
  imodintro
  wp_auto
  rw [Hnsr]
  wp_auto
  unfold isSnapStore
  icases Hsn with ⟨-, -, #HOpen⟩
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HOpen $$ Htok
  ihave Hl := Hacc $$ HP
  iapply ncfupd_wand
  isplitl [Hl]
  · iexact Hl
  iintro Hl
  inext
  icases Hl with ⟨%old, Hown, %Hold, Hcl⟩
  subst Hold
  iexists _
  iframe Hown
  iintro Hown
  imod Hcl $$ Hown with HP
  imodintro
  iintro %v Hpost Htok
  simp only [openPost, ↓reduceIte]
  icases Hpost with ⟨%mp', %rd, %R, %Hv, Hmp', #Hrd, HR, %Hwt⟩
  subst Hv
  wp_auto
  wp_apply (wp_fsmRestoreAndMeasure fx γ i fsmOwn respP snapP k0 (uint.nat m.Index') rd R b eof m.Size')
    $$ [$Hfo $HR $HsnapP] as ⟨%k0', %res, Hfo, %Hk0', #Hnc, Hres⟩
  · iframe #; ipureintro; exact Hk0
  ihave #Hrd' := Hrd
  unfold readCloserOk
  icases Hrd' with ⟨-, #HClose⟩
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HClose
  wp_auto
  iapply HΦ
  iframe
  iframe #
  ipureintro; exact Hk0'

end proof

end Perennial
