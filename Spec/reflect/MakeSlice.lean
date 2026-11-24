/-
`reflect.MakeSlice(rt, n, m)` of the `reflect.Type` of `[]Obj` (the k8s etcd3 driver's object,
`examples/k8s/etcd3`): a fresh zeroed slice of length `n` and capacity `m`, as its `Value`.
The allocation limit: `m ≤ 2^41` (revised after the attack, T8: `m·sizeof(Obj) ≤ maxAlloc` = 2^48
with `sizeof(Obj) = 112`; above it the runtime panics, `TestMakeSliceHugeCapPanics`).

Faithful: `MakeSlice` allocates zeroed memory for `m` elements (`reflect/value.go`,
`unsafe_NewArray`).

Never nil (`s ≠ slice.nil`, added 2026-11-19, stage 7g, `notes/k8s-7g-trust.md`): `MakeSlice` builds the
slice header with `Data: unsafe_NewArray(...)`, and `unsafe_NewArray` (`mallocgc`) returns a non-nil
pointer even for zero bytes (`&zerobase`), so `MakeSlice(rt, 0, m)` is a non-nil empty slice for every `m`,
`m = 0` included. Go: `examples/k8s/etcd3/trustspecs_test.go` `TestMakeSliceZeroNonNil` (`IsNil` false,
`!= nil`, not `DeepEqual` to a nil `[]Obj`, for capacities 0, 1, 5).
What the conjunct adds: for `m > 0` it already follows from `s.cap = m`; for `m = 0` it says only
`s.ptr ≠ null` (equivalently, given the post's `ownSlice`). Only `[]Obj` (112 bytes) is in scope, so a
zero-byte allocation, and the zero-size-element case, arise only at `m = 0`. It claims nothing about the
address: cap-0 results all share `&zerobase` (attack 2026-11-19, `TestZeroCapSharesAddress`), so never add
freshness or distinctness of the location for capacity 0.

The trust boundary: an axiom, `Proof/reflect/MakeSlice.lean` (`reflect` is names-only; the reasoning principles of `Proof/reflect/Values.lean`; stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked in `notes/k8s-7e-2-attack.md`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI reflectM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev reflect.MakeSlice.spec : Prop :=
  ∀ (rt : _root_.Perennial.reflect.«Type») (n m : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      ⌜reflType rt (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) ∧
        0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z m ∧ sint.Z m ≤ 2 ^ 41⌝ }}
    (App (App (App (Val (@! _root_.Perennial.reflect.MakeSlice)) (Val #rt)) (Val #n)) (Val #m))
  {{ (w : _root_.Perennial.reflect.Value), RET #w; ∃ s, ⌜reflSliceV w github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty s ∧
        s.len = n ∧ s.cap = m ∧ s ≠ slice.nil⌝ ∗
      s ↦* List.replicate (sint.nat n) (zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) ∗
      ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj s (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
