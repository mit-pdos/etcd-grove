/-
`sort.Sort` over a `sort.Interface`, proved by Perennial's `sort.wp_Sort` (Perennial translates
`sort.Sort`, `Reverse` and the pdqsort of `zsortinterface.go`, and proves them over its sorter
predicate `sort.isSorter`, which `sorterSpec` gives: `sorterSpec_isSorter`). Lean-first; see
`notes/decisions.md`, "The server's txn".

**The sorter** (`sorterSpec x R lt`): the interface value `x` is a sorter over a list of
elements of any type `E`, its state the resource `R l` for the list `l` it holds: `Len()`
returns `l`'s length, `Less(i, j)` (indices of `l`) returns `lt l[i] l[j]`, `Swap(i, j)`
exchanges the two elements. **`sort.Sort(x)`**, for a strict weak order `lt` (Perennial's
`slices.StrictWeakOrder`, as its `slices.SortFunc`) and a list of at most `2^62` elements (as
Perennial's `slices.Sort`: past that, the heapsort fallback's index arithmetic overflows),
leaves the sorter holding a permutation of `l` sorted by `lt` (no later element less than an
earlier one); the sort is not stable. The pure statement is Perennial's `slices.wp_SortFunc`'s (and `sort.wp_Sort`'s).
-/
module

public import Perennial.Proof.sort
public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

/-- **The `sort.Interface` `x` sorts a list** held by `R` (persistent): `Len`, `Less` and
`Swap` on the list `l` with `R l`. -/
def sorterSpec {E : Type} (x : GoInterfaceOk) (R : List E → IProp GF) (lt : E → E → Bool) :
    IProp GF :=
  iprop(
    □ (∀ l : List E,
      {{ R l }} (App (Val #(methods x.ty go!"Len" x.v)) (Val #()))
      {{ RET #(W64 l.length); R l }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ R l }} (App (App (Val #(methods x.ty go!"Less" x.v)) (Val #i)) (Val #j))
      {{ RET #(lt a b); R l }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ R l }} (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
      {{ RET #(); R ((l.set (sint.nat i) b).set (sint.nat j) a) }}))

instance sorterSpec_persistent {E : Type} (x : GoInterfaceOk) (R : List E → IProp GF)
    (lt : E → E → Bool) : Persistent (sorterSpec x R lt) := by
  unfold sorterSpec; infer_instance

omit package_sem in
/-- A sorter is one of Perennial's (`sort.isSorter`), for the order `lt a b = true`. -/
theorem sorterSpec_isSorter {E : Type} (x : GoInterfaceOk) (R : List E → IProp GF)
    (lt : E → E → Bool) :
    sorterSpec x R lt ⊢ _root_.Perennial.sort.isSorter x R (fun a b => lt a b = true) := by
  unfold sorterSpec _root_.Perennial.sort.isSorter
  iintro #⟨#HLen, #HLess, #HSwap⟩
  isplitr
  · iexact HLen
  isplitr
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hl HΦ
    iapply HLess $$ %l %i %j %a %b %Hij Hl
    inext
    iintro Hl
    iapply HΦ
    iframe Hl
    ipureintro; exact Iff.rfl
  · iexact HSwap

omit package_sem in
/-- One of Perennial's sorters (`sort.isSorter`) for an order `lt a b = true` is a sorter. -/
theorem isSorter_sorterSpec {E : Type} (x : GoInterfaceOk) (R : List E → IProp GF)
    (lt : E → E → Bool) :
    _root_.Perennial.sort.isSorter x R (fun a b => lt a b = true) ⊢ sorterSpec x R lt := by
  iintro #Hs
  unfold _root_.Perennial.sort.isSorter
  icases Hs with ⟨#HLen, #HLess, #HSwap⟩
  unfold sorterSpec
  isplitr
  · iexact HLen
  isplitr
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hl HΦ
    iapply HLess $$ %l %i %j %a %b %Hij Hl
    inext
    iintro %r ⟨Hl, %Hr⟩
    have : r = lt a b := by cases r <;> cases h : lt a b <;> simp_all
    subst this
    iapply HΦ $$ Hl
  · iexact HSwap

/-- `sort.Sort(x)`: the sorter's list permuted into an order sorted by the strict weak order
`lt`. -/
abbrev sort.«Sort».spec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (lt : E → E → Bool) (l : List E),
  slices.StrictWeakOrder (fun a b => lt a b = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterSpec x R lt ∗ R l ∗ ⌜l.length ≤ 2 ^ 62⌝ }}
    (App (Val (@! sort.«Sort»)) (Val #(GoInterface.ok x)))
  {{ (l' : List E), RET #(); R l' ∗
      ⌜l.Perm l' ∧ ∀ (i j : Nat) (a b : E), l'[i]? = some a → l'[j]? = some b → i < j →
        lt b a = false⌝ }}

end spec

end EtcdGrove
end Perennial
