/-
Lean-first (no Rocq counterpart).

# `reflect.Value`: the trust boundary of its uses (2026-10-22, `notes/k8s-etcd3-plan.md`)

Perennial translates `reflect` names-only: `reflect.Value` and `reflect.Type` are axiomatized
Lean types, and the generated instances that let a program keep a `reflect.Value` in a variable
(`GeneratedProof/reflect.lean`: `Value_typed_pointsto`, `Value_into_val_typed`) are
`sorry -- axiomatized type`. Go's implementation of `reflect` works on the runtime's
representation (a `Value` is a type descriptor, an `unsafe.Pointer` and flags; `Interface()`
builds an `any` from two words with `unsafe`), outside Perennial's semantics, so it cannot be
translated and proved. Until a trusted model of the subset used is in Perennial (with proved
reasoning principles: `notes/perennial-changes.md`, "`reflect.Value` held in a variable"), this
repository states the reasoning principles as axioms, here and in the specs of
`Spec/reflect/{New,Value__Addr,Value__Type,Value__Interface}.lean` and
`Spec/k8s_io/apimachinery/pkg/conversion/EnforcePtr.lean`:

- the two instances, as axioms of higher priority than the generated `sorry`s (a `reflect.Value`
  is a value like any other: allocated, loaded, stored); they hold of the real `Value`, a struct;
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

/-- **A `reflect.Value` is a value** (the trust boundary; see the file header). -/
@[instance high]
axiom value_typed_pointsto : TypedPointsto (GF := GF) _root_.Perennial.reflect.Value

/-- **A `reflect.Value` is allocated, loaded and stored as a value** (the trust boundary). -/
@[instance high]
axiom value_into_val_typed [reflect.Assumptions] :
    IntoValTypedUnderlying (GF := GF) _root_.Perennial.reflect.Value
      _root_.Perennial.reflect.Value.underlying

/-- **`reflect.Type`'s values are distinct as values** (the trust boundary, stage 7e-2): Go's
`reflect.Type` is an interface type, whose values Perennial's `GoInterface` represents injectively;
an axiom because Perennial axiomatizes `Type` (`notes/perennial-changes.md`, "`reflect.Type` in a
struct field"). -/
axiom type_intoVal_inj : go.IntoValInj _root_.Perennial.reflect.Type'

/-- **A `reflect.Type` is held in memory as a value** (stage 7e-2, after etcd-grove-81's review of
2026-11-10): the heap points-to of its value (`heapTypedPointsto`), so it names the heap instance
`hG` and `intoVal`, as every real instance does (not an axiom: an axiom of type
`TypedPointsto reflect.Type'` would depend on `GF` alone and claim one points-to for every heap,
the defect the review found in `value_typed_pointsto`). Of higher priority than Goose's generated
`Type'_typed_pointsto`, a `sorry` (the two coexist, and a struct elaborated against the generated one,
client-go's `Reflector.expectedType`, keeps it: `notes/perennial-changes.md`). -/
instance (priority := high) type_typed_pointsto : TypedPointsto (GF := GF) _root_.Perennial.reflect.Type' :=
  heapTypedPointsto _root_.Perennial.reflect.Type' type_intoVal_inj.intoVal_inj

/-- **A `reflect.Type` is allocated, loaded and stored as a value** (the trust boundary): Perennial's
alloc/load/store triples of the heap points-to at `Type`'s underlying type, which Perennial
axiomatizes (in Go an interface type, for which Perennial proves them). Replaces the generated
`Type'_into_val_typed`, a `sorry`. -/
@[instance high]
axiom type_into_val_typed [reflect.Assumptions] :
    IntoValTypedUnderlying (GF := GF) _root_.Perennial.reflect.Type'
      _root_.Perennial.reflect.Type'.underlying

/-- `v` is the addressable `reflect.Value` of the `T` at `p`. -/
opaque reflElem (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop

/-- `w` is the `reflect.Value` of the pointer `p : *T`. -/
opaque reflPtr (w : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop

/-- `rt` is the `reflect.Type` of `T`. -/
opaque reflType (rt : _root_.Perennial.reflect.Type') (T : go.GoType) : Prop

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
