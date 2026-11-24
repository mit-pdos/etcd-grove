/-
Lean-first (no Rocq counterpart).

# `reflect.Value`: the trust boundary of its uses (2026-10-22, `notes/k8s-etcd3-plan.md`)

Perennial translates `reflect.Value` as the struct it is (`typ_ *abi.Type`, `ptr`, `flag`;
Perennial `3eae9cd1f`, PR #672), with the generated instances that let a program keep a
`reflect.Value` in a variable (`GeneratedProof/reflect.lean`: `typed_pointsto'Value`,
`into_val_typed'Value`); `reflect.Type`, an interface type, is translated too (its values are
`GoInterface`s; Perennial `090fdac23`). `reflect`'s functions are not: Go's implementation works on
the runtime's representation (`Interface()` builds an `any` from two words with `unsafe`), outside
Perennial's semantics. Until a trusted model of the subset used is in Perennial (stage R1 of
etcd-grove #40), this repository states the reasoning principles as axioms, here and in the specs
of `Spec/reflect/{New,Value__Addr,Value__Type,Value__Interface}.lean` and
`Spec/k8s_io/apimachinery/pkg/conversion/EnforcePtr.lean`:

- `reflElem v T p`: `v` is the addressable `reflect.Value` of the `T` at `p` (what
  `conversion.EnforcePtr` of a `*T` gives); `reflPtr w T p`: `w` is the `Value` of the pointer
  `p : *T`; `reflType rt T`: `rt` is the `reflect.Type` of `T`. Opaque: the specs say what they
  give, nothing else;
- `reflSliceV w T s`: `w` is the (non-addressable) `Value` of the slice `s : []T`;
- `reflNew T p` (an opaque resource): the zeroed `T` that `reflect.New` allocated at `p`;
  `reflNew_pointsto` turns it into `p ↦ zero_val V` for a Lean type `V` that represents `T`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.reflect

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace reflectM

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `v` is the addressable `reflect.Value` of the `T` at `p`. -/
opaque reflElem (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop

/-- `w` is the `reflect.Value` of the pointer `p : *T`. -/
opaque reflPtr (w : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop

/-- `rt` is the `reflect.Type` of `T`. -/
opaque reflType (rt : _root_.Perennial.reflect.Type'') (T : go.GoType) : Prop

/-- `z` is the (non-addressable) zero `reflect.Value` of `T` (what `reflect.Zero` gives). -/
opaque reflZero (z : _root_.Perennial.reflect.Value) (T : go.GoType) : Prop

/-- `w` is the non-addressable `reflect.Value` of the slice `s : []T` (what `reflect.MakeSlice` and
`reflect.Append` return; stage 7e-2). -/
opaque reflSliceV (w : _root_.Perennial.reflect.Value) (T : go.GoType) (s : GoSlice) : Prop

/-- The zeroed `T` that `reflect.New` allocated at `p` (opaque). -/
opaque reflNew (T : go.GoType) (p : Loc) : IProp GF

/-- **`reflect.New`'s allocation is a zero value** of any Lean type representing `T` (the trust
boundary). -/
axiom reflNew_pointsto (T : go.GoType) (p : Loc) {V : Type} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] :
    reflNew (GF := GF) T p ⊢ p ↦ (zero_val V)

end defs

end reflectM
end EtcdGrove
end Perennial
