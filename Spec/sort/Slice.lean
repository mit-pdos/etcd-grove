/-
`sort.Slice` (the trust boundary: Perennial does not translate it; it swaps through
`reflectlite.Swapper`). Lean-first (no Rocq counterpart); used by mvcc's index-driven compaction
(etcd-io/etcd#21951, `store.scheduleCompactionIndexDriven`), which sorts the revisions it deletes.

`sort.Slice(x, less)` of a slice `s` (passed as `any`) holding `xs`, with a `less` closure that,
on any permutation of `xs` the slice holds and indices in range, runs with a frame `P` and the
slice and returns a boolean: the slice then holds a permutation of `xs` (its order is not stated:
no caller here needs it), `P` back.
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

/-- `sort.Slice(s, less)`: the slice holds a permutation of its elements after it. -/
abbrev sort.Slice.spec : Prop :=
  ∀ (V : Type) (t : go.GoType) [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] (s : GoSlice) (xs : List V)
    (less : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ s ↦* xs ∗ P ∗
      □ (∀ (ys : List V) (i j : w64),
        ⌜ys.Perm xs ∧ 0 ≤ sint.Z i ∧ sint.Z i < xs.length ∧ 0 ≤ sint.Z j ∧
          sint.Z j < xs.length⌝ -∗
        {{ P ∗ s ↦* ys }} (App (App (Val #less) (Val #i)) (Val #j))
        {{ (b : Bool), RET #b; P ∗ s ↦* ys }}) }}
    (App (App (Val (@! _root_.Perennial.sort.Slice'))
      (Val #(interface.mkOk (go.GoType.SliceType t) #s))) (Val #less))
  {{ RET #(); P ∗ ∃ ys : List V, s ↦* ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end EtcdGrove
end Perennial
