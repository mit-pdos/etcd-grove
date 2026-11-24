/-
Lean-first (no Rocq counterpart).

# `reflect.Value`: the predicates of its specs (2026-10-22, `notes/k8s-etcd3-plan.md`; reflect S0
2026-11-24)

Perennial models `reflect` (`goose/model/overlay/reflect`, reflect S0): `TypeOf`, `ValueOf` and
`Value.{Kind, Type, IsNil, Elem, Interface}`, `Type.{Kind, Elem}` are translated with their bodies; the
rest of the package is names only. Its `Value` is `{typ_ any; ptr any; flag}`, `typ_` the token of the
value's type. The predicates the specs here are stated in:

- `reflElem v T p`, `reflPtr w T p`, `reflType rt T`, `reflNew T p` (definitions, those of the
  reflect S0 plan, over the model's `Value`): `v` is the addressable `reflect.Value` of the `T` at `p`
  (what `Elem()` of a non-nil `*T` gives), `w` the `Value` of the pointer `p : *T`, `rt` the
  `reflect.Type` of `T`, and `reflNew T p` the zeroed `T` at `p` (`reflNew_pointsto` turns it into
  `p ↦ zero_val V` for a Lean type `V` that represents `T`);
- `reflZero z T`, `reflSliceV w T s` (opaque, for the names-only `Zero`, `MakeSlice` and `Append`):
  `z` is the zero `Value` of `T`, `w` the (non-addressable) `Value` of the slice `s : []T`. The
  specs say what they give, nothing else.

The specs of the translated functions (`Spec/reflect/{ValueOf,Value__Kind,Value__IsNil,Value__Type,
Value__Interface,Type__Elem}.lean`) are proved; those of the names-only ones (`New`, `Zero`,
`Value.{Set, Addr, Len, Cap}`, `MakeSlice`, `Append`, `Copy`, `DeepEqual`, and `TypeOf`'s `String`) are
trust-boundary axioms.
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

/-- `v` is the addressable `reflect.Value` of the `T` at `p` (`Elem()` of the `Value` of a non-nil
`*T`): it holds `any(p)` (a `*T`), and its flag is `T`'s kind with `flagIndir` (128) and `flagAddr`
(256). -/
def reflElem (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop :=
  ∃ k : Nat, go.kindOf (underlying T) = some k ∧
    v = _root_.Perennial.reflect.Value.mk (go.tok T) (interface.mkOk (go.GoType.PointerType T) #p)
      (W64 k ||| W64 128 ||| W64 256)

/-- `w` is the `reflect.Value` of the pointer `p : *T` (`reflect.ValueOf(any(p))`): direct, of kind
`Pointer` (22). -/
def reflPtr (w : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop :=
  w = _root_.Perennial.reflect.Value.mk (go.tok (go.GoType.PointerType T))
    (interface.mkOk (go.GoType.PointerType T) #p) (W64 22)

/-- `rt` is the `reflect.Type` of `T`: the interface holding the model's `rtype` of `T`'s token. -/
def reflType (rt : _root_.Perennial.reflect.Type') (T : go.GoType) : Prop :=
  rt = interface.mkOk _root_.Perennial.reflect.rtype.ty #(_root_.Perennial.reflect.rtype.mk (go.tok T))

/-- `z` is the (non-addressable) zero `reflect.Value` of `T` (what `reflect.Zero` gives). -/
opaque reflZero (z : _root_.Perennial.reflect.Value) (T : go.GoType) : Prop

/-- `w` is the non-addressable `reflect.Value` of the slice `s : []T` (what `reflect.MakeSlice` and
`reflect.Append` return; stage 7e-2). -/
opaque reflSliceV (w : _root_.Perennial.reflect.Value) (T : go.GoType) (s : GoSlice) : Prop

/-- The zeroed `T` that `reflect.New` allocated at `p`: its typed points-to at each Lean type `V`
that represents `T`. -/
def reflNew (T : go.GoType) (p : Loc) : IProp GF :=
  iprop(∀ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
    (_ : IntoValTyped (GF := GF) V T), p ↦ (zero_val V))

/-- **`reflect.New`'s allocation is a zero value** of any Lean type representing `T`. -/
theorem reflNew_pointsto (T : go.GoType) (p : Loc) {V : Type} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] :
    reflNew (GF := GF) T p ⊢ p ↦ (zero_val V) := by
  unfold reflNew
  iintro H
  ispecialize H $$ %V %inferInstance %inferInstance %inferInstance
  iexact H

end defs

end reflectM
end EtcdGrove
end Perennial
