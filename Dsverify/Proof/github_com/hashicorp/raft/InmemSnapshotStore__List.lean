/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemSnapshotStore__List.lean (241f27e).
-/
/-
The proof of `raft.(*InmemSnapshotStore).List`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemSnapshotStore__List

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

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.InmemSnapshotStore.List.wp_proof :
    github_com.hashicorp.raft.InmemSnapshotStore.List.spec (GF := GF) (hG := hG) :=
  fun m tid => by
  wp_start as ⟨#His, Htok⟩
  iNamed His
  icases Hpool with ⟨%γp, #Hpool⟩
  iapply wp_fupd
  wp_auto
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  imod qpool.borrow_lc snapPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  rw [method_unfold (t := go.GoType.PointerType InmemSnapshotStore.ty)]
  wp_auto
  wp_apply (sync.RWMutex.wp_RLock (m.[InmemSnapshotStore, go!"RWMutex"]) (snapInv m)) $$ [$Hown]
    with ⟨Hrlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc2 HP with HP
  icases (snapInv_unfold m _).mp $$ HP with HP
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType (go.GoType.PointerType SnapshotMeta.ty))))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType SnapshotMeta.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType InmemSnapshotStore.ty)]
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock (m.[InmemSnapshotStore, go!"RWMutex"]) (snapInv m))
    $$ [$Hrlocked HP] with Hown
  · inext; iapply (snapInv_unfold m _).mpr; iexact HP
  imod qpool.giveBack snapPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
    with Htok
  imodintro
  iapply HΦ $$ Hsl Htok

end proof

end Perennial
