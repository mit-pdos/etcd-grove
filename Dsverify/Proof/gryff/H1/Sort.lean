/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Sort.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: a spec of `sort.Slice` on a `[]int32` with a `less` that compares two elements with
`<`: the slice ends sorted (`mergeSort` by `sle`, the model's `shortCircuit`). Port: the lab proved
it over its trusted insertion-sort model of `sort.Slice` (`Harness/Code/sort_extra.lean`); here it
is the hypothesis `SortSliceHyp` (`Lib/SortHyps.lean`, where `lessOk` now lives).
-/
module

public import Dsverify.Proof.gryff.H1.Defs
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

theorem if_pos' {c : Prop} [Decidable c] (h : c) {α : Sort _} {t e : α} : (if c then t else e) = t := by
  simp [h]

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (sle slt)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [sortA : SortSliceHyp GF]

theorem wp_sort_Slice (sl : GoSlice) (xs : List w32) (less : GoFunc) (F : IProp GF) :
    {{ sl ↦* xs ∗ F ∗ lessOk sl F less }}
      (App (App (Val (@! sort.Slice')) (Val #(interface.mkOk (go.SliceType go.int32) #sl)))
        (Val #less))
    {{ RET #(); sl ↦* xs.mergeSort (fun a b => sle a b) ∗ F }} :=
  SortSliceHyp.slice sl xs less F

end

end Perennial.gryff.replica2
