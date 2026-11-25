/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Sort.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: `gryffcommon.ShortCircuit` sorts its `[]int32` with `slices.Sort` (dsv-fix4, 2026-11-25;
until then `sort.Slice` with a `<` closure, over the trust-boundary axiom `sort.Slice.wp_proofInt32Lt`,
retired: it had no length bound). The proof applies Perennial's `slices.wp_Sort` at `<` on the
signed values (its `lessImplements` is `cmp.Less` at `int32`, `Spec/cmp/Less.lean`; its length
premise is `ShortCircuit`'s guard `len(keys) <= maxShortReads`); this module has the pure facts:
`<` is a strict weak order, and a sorted permutation is `mergeSort` by `sle` (the model's
`shortCircuitReads`).
-/
module

public import Dsverify.Proof.gryff.H1.Defs
public import Dsverify.Proof.gryff.H1.SortPure
public import Perennial.Proof.slices.SortBasics

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

theorem if_pos' {c : Prop} [Decidable c] (h : c) {α : Sort _} {t e : α} : (if c then t else e) = t := by
  simp [h]

open Perennial.gryff.model (sle slt)

/-- `<` on the signed values of `int32`s is a strict weak order (Perennial's
`slices.StrictWeakOrder_signed_lt`, at `w32`). -/
theorem strictWeakOrder_slt32 :
    _root_.Perennial.slices.StrictWeakOrder (fun (a b : w32) => sint.Z a < sint.Z b) where
  strict_weak_order_irrefl _ := by omega
  strict_weak_order_trans _ _ _ h1 h2 := by omega
  strict_weak_order_equiv :=
    ⟨fun _ => by omega, fun h => by omega, fun h1 h2 => by omega⟩

/-- What `slices.wp_Sort` gives at `<` (a permutation, no later element below an earlier one) is
`mergeSort` by `sle`. -/
theorem sorted_slt_eq_mergeSort (xs ys : List w32) (hp : xs.Perm ys)
    (hs : ∀ (i j : Nat) (xi xj : w32), ys[i]? = some xi → ys[j]? = some xj → i < j →
      ¬ sint.Z xj < sint.Z xi) :
    ys = xs.mergeSort (fun a b => sle a b) := by
  apply sortp.srt_perm_eq xs ys _ hp.symm
  unfold sortp.Srt
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  simp only [sle, decide_eq_true_eq]; omega

end Perennial.gryff.replica2
