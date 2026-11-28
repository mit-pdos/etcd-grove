/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__StoreLog.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).StoreLog`: `StoreLogs` of a one-element slice literal.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__StoreLog
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__StoreLogs

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

theorem github_com.hashicorp.raft.InmemStore.StoreLog.wp_proof
    (wp_StoreLogs : github_com.hashicorp.raft.InmemStore.StoreLogs.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.InmemStore.StoreLog.spec (GF := GF) (hG := hG) :=
  fun γs i p first e => by
  wp_start as ⟨#His, %Hfl, #Hp⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.PointerType Log.ty)))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType Log.ty) [p]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  have hf1 : first + 1 ≤ 2 ^ 64 := by omega
  wp_apply wp_StoreLogs γs i _ (DFrac.own 1) [p] first [e] $$ [Hsl] [HΦ «$res0»]
  · iframe His Hsl
    isplitr
    · ipureintro; exact ⟨rfl, by rw [List.length_singleton]; exact hf1⟩
    iapply BigSepL.bigSepL_singleton.2
    iexists e
    isplit
    · ipureintro; rfl
    · rw [Nat.add_zero]; iexact Hp
  · iintro Hnc
    imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
    imodintro
    iframe Hnc
    inext
    icases HAU with ⟨%L, HL, Hclose⟩
    iexists L
    iframe
    iintro HL
    imod Hclose $$ HL with HΦ
    imodintro
    iintro -
    wp_auto
    iexact HΦ

end proof

end Perennial
