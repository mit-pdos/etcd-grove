/-
`slices.Insert(s, i, v...)` (names-only in Perennial: its `slices.toml` translates the sorts only),
on a slice `s` holding `xs` with its capacity owned, at an index `i` in `[0, len(xs)]`, inserting
the values `ys` of a slice `v` read with any fraction: it returns a slice `s'` holding `xs[:i] ++ ys
++ xs[i:]`, with its capacity owned (`s` itself may not be used after: its backing array may be
`s'`'s). The trust boundary: an axiom, `Proof/slices/Insert.lean`.

Its callers: structured-merge-diff's sorted sets and maps of path elements (`fieldpath`:
`PathElementSet.Insert`, `PathElementValueMap.Insert`, `SetNodeMap.Descend`), inserting one element
(a slice literal of one) at the index `slices.BinarySearchFunc` returned. Lean-first (2026-11-19,
notes/smd-robustness.md).

True of Go (`slices/slices.go`, go1.27): `Insert` bounds-checks `s[i:]` (no panic: `0 ≤ i ≤
len(s)`); returns `s` if `v` is empty; `append(s, v...)` if `i == len(s)`; if `len(s)+len(v) >
cap(s)`, `append(s[:i], make(S, n+m-i)...)` (a new array, `cap(s[:i]) = cap(s) < n+m`) filled by
two `copy`s; otherwise `s[:n+m]`, written only within `s`'s capacity, with the overlap of `v` and
`s[i+m:]` handled (here none: `v`'s elements, read with a fraction, cannot be in `s`'s capacity,
owned in full). In every case the result holds `s[:i] ++ v ++ s[i:]`, and its elements past its
length are either `s`'s capacity or a new array's. The length bound `len(xs) + len(ys) < 2^63` keeps
`n+m` an `int`; the allocation of a new array is assumed to succeed (as every Go allocation in
Perennial's model).
-/
module

public import Perennial.Proof.slices.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev slices.Insert.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (s : GoSlice) (xs : List E) (i : w64) (v : GoSlice) (ys : List E) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗ s ↦* xs ∗ ownSliceCap E s (DFrac.own 1) ∗
        v ↦*{dq} ys ∗
        ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ xs.length ∧ xs.length + ys.length < 2 ^ 63⌝ }}
      (App (App (App (Val #(functions _root_.Perennial.slices.Insert [S, Et]))
        (Val #s)) (Val #i)) (Val #v))
    {{ (s' : GoSlice), RET #s';
        s' ↦* (xs.take (sint.Z i).toNat ++ ys ++ xs.drop (sint.Z i).toNat) ∗
        ownSliceCap E s' (DFrac.own 1) ∗ v ↦*{dq} ys }}

end spec

end EtcdGrove
end Perennial
