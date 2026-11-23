/-
The slicing-by-8 table's cells (a defs module of `hash/crc32`'s proofs): a `[8][256]uint32` written
as a function of its indices (`tabOf`), its rows, and loads and stores of its entries.
-/
module

public import GeneratedProof.hash.crc32
public import Spec.hash.crc32.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace hash.crc32

/-- The `[8][256]uint32` whose entry `(j, k)` is `f j k`. -/
def tabOf (f : Nat → Nat → w32) : GoArray (GoArray w32 256) 8 :=
  array.mk 8 ((List.range 8).map fun j => array.mk 256 ((List.range 256).map (f j)))

theorem slicingTableArr_tabOf (poly : w32) :
    _root_.Perennial.hash.crc32.slicingTableArr poly = tabOf (_root_.Perennial.hash.crc32.slicingEntry poly) := rfl

theorem rangeMap_set {A : Type} (n : Nat) (g : Nat → A) (k : Nat) (v : A) :
    ((List.range n).map g).set k v = (List.range n).map (fun k' => if k' = k then v else g k') := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_set, List.getElem_map, List.getElem_range]
    by_cases h : k = i
    · subst h; simp
    · simp [h, Ne.symm h]

theorem tabOf_row (f : Nat → Nat → w32) (j : Nat) (hj : j < 8) :
    (tabOf f).arr[((j : Int)).toNat]? = some (array.mk 256 ((List.range 256).map (f j))) := by
  simp [tabOf, hj]

theorem row_entry (g : Nat → w32) (k : Nat) (hk : k < 256) :
    ((array.mk 256 ((List.range 256).map g) : GoArray w32 256)).arr[((k : Int)).toNat]? = some (g k) := by
  simp [hk]

theorem tabOf_setRow (f : Nat → Nat → w32) (j : Nat) (g : Nat → w32) :
    (array.mk 8 ((tabOf f).arr.set ((j : Int)).toNat (array.mk 256 ((List.range 256).map g))) :
      GoArray (GoArray w32 256) 8) = tabOf (fun j' => if j' = j then g else f j') := by
  simp only [tabOf, Int.toNat_natCast, rangeMap_set]
  congr 2
  funext j'
  split <;> rfl

theorem tabOf_zero : (zero_val (GoArray (GoArray w32 256) 8)) = tabOf (fun _ _ => 0#32) := by
  have h1 : ∀ {A : Type} (n : Nat) (c : A), (List.range n).map (fun _ => c) = List.replicate n c := by
    intro A n c; apply List.ext_getElem <;> simp
  show (⟨List.replicate (8 : Int).toNat ⟨List.replicate (256 : Int).toNat (0 : w32)⟩⟩ :
    GoArray (GoArray w32 256) 8) = _
  unfold tabOf
  simp only [h1]
  rfl

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.hash.crc32.Assumptions]

/-- Row `j` of a table: its own cells, and the table back from them (`array_acc`). -/
theorem tabOf_row_acc (l : Loc) (dq : DFrac) (f : Nat → Nat → w32) (j : Nat) (hj : j < 8) :
    (l ↦{dq} tabOf f : IProp GF) ⊢
      iprop(arrayIndexRef (GoArray w32 256) (j : Int) l ↦{dq}
          (array.mk 256 ((List.range 256).map (f j)) : GoArray w32 256) ∗
        (∀ g : Nat → w32, arrayIndexRef (GoArray w32 256) (j : Int) l ↦{dq}
            (array.mk 256 ((List.range 256).map g) : GoArray w32 256) -∗
          l ↦{dq} tabOf (fun j' => if j' = j then g else f j'))) := by
  iintro Ha
  icases array_acc l (j : Int) dq 8 (tabOf f) _ (by omega) (tabOf_row f j hj) $$ Ha with ⟨Hr, Hb⟩
  iframe Hr
  iintro %g Hg
  ihave Ha := Hb $$ Hg
  rw [tabOf_setRow]
  iexact Ha

/-- A read-only table's row `j`, read-only. -/
theorem tabOf_row_persist (l : Loc) (f : Nat → Nat → w32) (j : Nat) (hj : j < 8) :
    (l ↦□ tabOf f : IProp GF) ⊢
      arrayIndexRef (GoArray w32 256) (j : Int) l ↦□ (array.mk 256 ((List.range 256).map (f j)) : GoArray w32 256) := by
  iintro #Ha
  icases tabOf_row_acc l DFrac.discard f j hj $$ Ha with ⟨Hr, -⟩
  iexact Hr

/-- A load of entry `(j, k)`. -/
theorem wp_load_tabOf (l : Loc) (dq : DFrac) (f : Nat → Nat → w32) (j k : Nat) (hj : j < 8)
    (hk : k < 256) :
    {{ (l ↦{dq} tabOf f : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.uint32)))
        (Val #(arrayIndexRef w32 (k : Int) (arrayIndexRef (GoArray w32 256) (j : Int) l))))
    {{ RET #(f j k); l ↦{dq} tabOf f }} := by
  iintro %Φ Ha HΦ
  icases tabOf_row_acc l dq f j hj $$ Ha with ⟨Hr, Hb⟩
  icases array_acc _ (k : Int) dq 256 _ _ (by omega) (row_entry (f j) k hk) $$ Hr with ⟨Hv, Hb2⟩
  wp_apply (IntoValTyped.wp_load (t := go.uint32) _ _ _) $$ Hv as Hv
  ihave Hr := Hb2 $$ Hv
  rw [list_set_getElem?_self _ _ _ (row_entry (f j) k hk)]
  ihave Ha := Hb $$ %(f j) Hr
  have hf : (fun j' => if j' = j then f j else f j') = f := by
    funext j'; split <;> simp_all
  rw [hf]
  iapply HΦ
  iexact Ha

/-- A store to entry `(j, k)`. -/
theorem wp_store_tabOf (l : Loc) (f : Nat → Nat → w32) (j k : Nat) (hj : j < 8) (hk : k < 256)
    (v : w32) :
    {{ (l ↦ tabOf f : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.uint32)))
        (Val (PairV #(arrayIndexRef w32 (k : Int) (arrayIndexRef (GoArray w32 256) (j : Int) l)) #v)))
    {{ RET #(); l ↦ tabOf (fun j' k' => if j' = j ∧ k' = k then v else f j' k') }} := by
  iintro %Φ Ha HΦ
  icases tabOf_row_acc l (DFrac.own 1) f j hj $$ Ha with ⟨Hr, Hb⟩
  icases array_acc _ (k : Int) (DFrac.own 1) 256 _ _ (by omega) (row_entry (f j) k hk) $$ Hr with ⟨Hv, Hb2⟩
  wp_apply IntoValTyped.wp_store (t := go.uint32) _ _ _ $$ Hv as Hv
  ihave Hr := Hb2 $$ Hv
  simp only [Int.toNat_natCast, rangeMap_set]
  ihave Ha := Hb $$ %(fun k' => if k' = k then v else f j k') Hr
  have hf : (fun j' => if j' = j then (fun k' => if k' = k then v else f j k') else f j') =
      (fun j' k' => if j' = j ∧ k' = k then v else f j' k') := by
    funext j' k'
    by_cases h1 : j' = j <;> by_cases h2 : k' = k <;> simp_all
  rw [hf]
  iapply HΦ
  iexact Ha

end wps

end hash.crc32

end EtcdGrove
end Perennial
