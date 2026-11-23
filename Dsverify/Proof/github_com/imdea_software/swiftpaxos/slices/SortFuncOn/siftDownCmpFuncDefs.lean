/-
The definitions, specs and lemmas of `siftDownCmpFunc.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Perennial.Proof.slices.HeapSortBasics
public import Perennial.Spec.slices.siftDownCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.Basics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `siftDownCmpFunc(data, lo, hi, first)` sifts the element at `first + lo` down the heap
`[first + lo, first + hi)` (first conjunct; `lo < hi`), and returns at once for `lo = hi = 0`
(second conjunct, `wp_siftDownCmpFunc_Trivial` in `Results.lean`). The two triples (`wp_siftDownCmpFunc` and
`wp_siftDownCmpFunc_Trivial` before) are separate proofs, neither implying the other. -/
abbrev slices.siftDownCmpFunc.specOn : Prop :=
  (∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
      [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (φ : E → Prop) (data : GoSlice)
      (lo hi a b : w64) (cmp_code : GoFunc) (xs : List E) (Hφ : AllOn φ xs),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmpOn R φ cmp_code ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z a + sint.Z lo ∧
                        sint.Z a + sint.Z lo < sint.Z a + sint.Z hi ∧
                        sint.Z a + sint.Z hi ≤ sint.Z b ∧
                        sint.Z b ≤ xs.length ∧
                        xs.length ≤ 2 ^ 62⌝ ∗
        "%HSegSorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                    (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                    (sint.nat a ≤ i ∧ i < sint.nat b) →
                    xs[i]? = some xi →
                    xs[j]? = some xj → ¬ R xj xi⌝ ∗
        "%Heap" ∷ ⌜IsHeapSeg R xs (sint.nat a) (sint.nat b) (sint.nat lo + 1) (sint.nat hi)⌝ }}
      (App (App (App (App (App (Val #(functions siftDownCmpFunc [Et])) (Val #data)) (Val #lo))
        (Val #hi)) (Val #a)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%HPermPost" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%HSegSortedPost" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                    (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                    (sint.nat a ≤ i ∧ i < sint.nat b) →
                    xs'[i]? = some xi →
                    xs'[j]? = some xj → ¬ R xj xi⌝ ∗
        "%Heap" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }}) ∧
  (∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
      [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (φ : E → Prop) (data : GoSlice)
      (a b : w64) (cmp_code : GoFunc) (xs : List E) (Hφ : AllOn φ xs),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmpOn R φ cmp_code ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (App (Val #(functions siftDownCmpFunc [Et])) (Val #data))
        (Val #(W64 0))) (Val #(W64 0))) (Val #a)) (Val #cmp_code))
    {{ RET #(); "Hxs" ∷ data ↦* xs }})

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

end proof

end Perennial
