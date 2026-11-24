/-
Lean-first (no Rocq counterpart).

# `reflect.Value`: the predicates of its specs (2026-10-22, `notes/k8s-etcd3-plan.md`; reflect S0
2026-11-24)

Perennial models `reflect` (`goose/model/overlay/reflect`, reflect S0): `TypeOf`, `ValueOf` and
`Value.{Kind, Type, IsNil, Elem, Interface}`, `Type.{Kind, Elem}` are translated with their bodies; the
rest of the package is names only. Its `Value` is `{typ_ any; ptr any; flag}`, `typ_` the token of the
value's type. The predicates the specs here are stated in:

- `reflElem v T p`, `reflPtr w T p`, `reflType rt T`, `reflNew T p` (abbreviations of Perennial's
  `Perennial/Proof/reflect/Values.lean`, over the model's `Value`): `v` is the addressable `reflect.Value` of the `T` at `p`
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

public import Perennial.Proof.reflect.Values

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace reflectM

open Iris Iris.BI

section vocab
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- `v` is the addressable `reflect.Value` of the `T` at `p` (`Elem()` of the `Value` of a non-nil
`*T`): Perennial's `reflect.reflElem`. -/
abbrev reflElem (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop :=
  _root_.Perennial.reflect.reflElem v T p

/-- `w` is the `reflect.Value` of the pointer `p : *T` (`reflect.ValueOf(any(p))`): Perennial's
`reflect.reflPtr`. -/
abbrev reflPtr (w : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop :=
  _root_.Perennial.reflect.reflPtr w T p

/-- `rt` is the `reflect.Type` of `T`: Perennial's `reflect.reflType`. -/
abbrev reflType (rt : _root_.Perennial.reflect.Type') (T : go.GoType) : Prop :=
  _root_.Perennial.reflect.reflType rt T

/-- `x` is a non-nil interface whose dynamic type is not the model's `reflect.rtype`: the values
`reflect.TypeOf` of the model is defined at (it is stuck on the values of reflect's own `Type`). -/
def notRType (x : GoInterface) : Prop :=
  ∃ (t : go.GoType) (v : val), x = interface.mkOk t v ∧ t ≠ _root_.Perennial.reflect.rtype.ty

/-- A pointer is not an `rtype`. -/
theorem notRType_ptr (T : go.GoType) (v : val) : notRType (interface.mkOk (go.PointerType T) v) :=
  ⟨_, v, rfl, by simp [_root_.Perennial.reflect.rtype.ty]⟩

/-- A kind is below 27. -/
theorem kindOf_lt {u : go.GoType} {k : Nat} (h : go.kindOf u = some k) : k < 27 := by
  unfold go.kindOf at h
  split at h <;> try (cases h; omega)
  simp only [List.find?] at h
  repeat (first | (split at h <;> try (cases h; omega)) | (simp at h; omega))
  all_goals simp_all

/-- The flag bits of a `reflElem` of kind `k`: its kind bits, non-zero, not a method value; and
`Elem()` of a `reflPtr` builds it. -/
theorem elemFlag_bits (k : Nat) (hk : k < 27) :
    (W64 k ||| W64 128 ||| W64 256) &&& W64 31 = W64 k ∧
    (W64 k ||| W64 128 ||| W64 256) ≠ W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 512 = W64 0 ∧
    W64 22 &&& W64 96 ||| W64 128 ||| W64 256 ||| W64 k = W64 k ||| W64 128 ||| W64 256 := by
  revert k
  decide

end vocab

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `z` is the (non-addressable) zero `reflect.Value` of `T` (what `reflect.Zero` gives). -/
opaque reflZero (z : _root_.Perennial.reflect.Value) (T : go.GoType) : Prop

/-- `w` is the non-addressable `reflect.Value` of the slice `s : []T` (what `reflect.MakeSlice` and
`reflect.Append` return; stage 7e-2). -/
opaque reflSliceV (w : _root_.Perennial.reflect.Value) (T : go.GoType) (s : GoSlice) : Prop

/-- The zeroed `T` that `reflect.New` allocated at `p`: Perennial's `reflect.reflNew`, its typed
points-to at each Lean type `V` that represents `T`. -/
abbrev reflNew (T : go.GoType) (p : Loc) : IProp GF :=
  _root_.Perennial.reflect.reflNew (GF := GF) T p

/-- **`reflect.New`'s allocation is a zero value** of any Lean type representing `T`. -/
theorem reflNew_pointsto (T : go.GoType) (p : Loc) {V : Type} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] :
    reflNew (GF := GF) T p ⊢ p ↦ (zero_val V) :=
  _root_.Perennial.reflect.reflNew_pointsto T p

end defs

end reflectM
end EtcdGrove
end Perennial
