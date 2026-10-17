/-
`sort.Slice(x, less)` of Go's `sort` package. The trust boundary: Perennial names `sort.Slice`
but does not translate it (it swaps through `internal/reflectlite.Swapper` and runs
`pdqsort_func`, neither translated). Lean-first (no Rocq counterpart); first used by
etcd-io/etcd#22304's `cohortsByRevision` (`notes/pr-verify/etcd-22304.md`).

**The spec.** `x` is a slice `s` (as an `any`) of elements of any type `E`, holding `xs`. The
caller's `less(i, j)` reads the slice (as `cohortsByRevision`'s closure does, through the
variable that holds it) and, for its elements `a = l[i]` and `b = l[j]` of the slice's current
list `l` (a permutation of `xs`), returns `key a < key b` for a key `key : E → Int`, keeping the
caller's resource `I` (here: the variable and the elements' fields the key is read from). That
is a strict weak order, as `sort.Slice` requires. `sort.Slice` leaves the slice holding a
permutation of `xs` sorted by `key` (no later element with a smaller key); the sort is not
stable. As Perennial's `slices.SortFunc` and this repository's `sort.Sort`, at most `2 ^ 62`
elements (past that, the heapsort fallback's index arithmetic overflows).

What `sort.Slice` does in Go: `reflectlite.Swapper(x)` swaps the slice's elements in place,
`pdqsort_func` (the same pdqsort as `sort.Sort`'s, over `less` and the swapper) calls `less`
only with indices in `[0, len)`. So the slice holds a permutation of `xs` at every call of
`less`, and nothing else is touched.
-/
module

public import Perennial.Proof.sort

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

/-- `less` compares the elements `i` and `j` of the slice `s` by `key`, for every list `l` of the
slice that is a permutation of `xs`, keeping `I` (persistent). -/
def sort.lessByKey {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (s : GoSlice) (less : GoFunc) (xs : List E) (key : E → Int)
    (I : IProp GF) : IProp GF :=
  iprop(□ ∀ (l : List E) (i j : w64) (a b : E),
    ⌜l.Perm xs ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
    {{ s ↦* l ∗ I }} (App (App (Val #less) (Val #i)) (Val #j))
    {{ RET #(decide (key a < key b)); s ↦* l ∗ I }})

instance sort.lessByKey_persistent {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E]
    {Et : go.GoType} [IntoValTyped (GF := GF) E Et] (s : GoSlice) (less : GoFunc) (xs : List E)
    (key : E → Int) (I : IProp GF) :
    Persistent (sort.lessByKey (Et := Et) s less xs key I) := by
  unfold sort.lessByKey; infer_instance

/-- `sort.Slice(s, less)`: the slice permuted into an order sorted by `key`. -/
abbrev sort.Slice.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (s : GoSlice) (less : GoFunc) (xs : List E) (key : E → Int)
    (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ s ↦* xs ∗ I ∗ ⌜xs.length ≤ 2 ^ 62⌝ ∗
      sort.lessByKey (Et := Et) s less xs key I }}
    (App (App (Val (@! sort.Slice')) (Val #(interface.mkOk (go.GoType.SliceType Et) #s)))
      (Val #less))
  {{ (xs' : List E), RET #(); s ↦* xs' ∗ I ∗
      ⌜xs.Perm xs' ∧ ∀ (i j : Nat) (a b : E), xs'[i]? = some a → xs'[j]? = some b → i < j →
        key a ≤ key b⌝ }}

end spec

end EtcdGrove
end Perennial
