/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/slices/SortFuncOn/Basics.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`slices.SortFunc` with the comparator needed only on a predicate `φ` that every element of the
slice satisfies (`cmpOn`): the definitions and the comparison-call lemma shared by the copies of
Perennial's `pdqsort` proofs in this directory (each copy is Perennial's proof
(Perennial/Proof/slices/<F>CmpFunc.lean) with `cmpImplements R cmp` replaced by `cmpOn R φ cmp`
and the premise `∀ x ∈ xs, φ x` on the slice's elements; every comparison is between two of the
slice's elements, a permutation of the input).
-/
module

public import Perennial.Proof.slices.SortBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section pure
variable {E : Type} (φ : E → Prop)

/-- `φ` on every element of `xs`. -/
abbrev AllOn (xs : List E) : Prop := ∀ x ∈ xs, φ x

theorem allOn_perm {xs xs' : List E} (H : AllOn φ xs) (Hp : xs ≡ₚ xs') : AllOn φ xs' :=
  fun x hx => H x (Hp.symm.subset hx)

theorem allOn_lookup {xs : List E} {i : Nat} {x : E} (H : AllOn φ xs) (Hx : xs[i]? = some x) :
    φ x :=
  H x (List.mem_of_getElem? Hx)

theorem allOn_perm_lookup {xs xs' : List E} {i : Nat} {x : E} (H : AllOn φ xs)
    (Hp : xs ≡ₚ xs') (Hx : xs'[i]? = some x) : φ x :=
  allOn_lookup φ (allOn_perm φ H Hp) Hx

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) (φ : E → Prop)

/-- The comparison function implements `R` on the values satisfying `φ`. -/
def cmpOn (cmp_code : GoFunc) : IProp GF :=
  iprop(∀ (x y : E),
    {{ ⌜φ x ∧ φ y⌝ }}
      (App (App (Val #cmp_code) (Val #x)) (Val #y))
    {{ (r : w64), RET #r; ⌜sint.Z r < 0 ↔ R x y⌝ }})

instance cmpOn_persistent (cmp_code : GoFunc) :
    Persistent (cmpOn (GF := GF) R φ cmp_code) := by
  unfold cmpOn; infer_instance

/-- `cmpImplements` gives `cmpOn` for every `φ`. -/
theorem cmpImplements_on (cmp_code : GoFunc) :
    cmpImplements (GF := GF) R cmp_code ⊢ cmpOn R φ cmp_code := by
  unfold cmpImplements cmpOn
  iintro #H %x %y %Φ !> - HΦ
  iapply H $$ [] HΦ
  itrivial

omit [ZeroVal E] [TypedPointsto (GF := GF) E] [IntoValTyped (GF := GF) E Et] sem in
/-- A call of the comparison function on two values satisfying `φ`, with `cmpOn` kept folded. -/
theorem cmpOn_wp (cmp_code : GoFunc) (x y : E) (hx : φ x) (hy : φ y) :
    {{ cmpOn (GF := GF) R φ cmp_code }}
      (App (App (Val #cmp_code) (Val #x)) (Val #y))
    {{ (r : w64), RET #r; ⌜sint.Z r < 0 ↔ R x y⌝ }} := by
  iintro %Φ #Hc HΦ
  unfold cmpOn
  iapply Hc $$ [] HΦ
  ipureintro
  exact ⟨hx, hy⟩

end proof

end slices

end Perennial
