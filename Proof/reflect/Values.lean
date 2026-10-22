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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- `v` is the addressable `reflect.Value` of the `T` at `p`. -/
opaque reflElem (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop

/-- `w` is the `reflect.Value` of the pointer `p : *T`. -/
opaque reflPtr (w : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) : Prop

/-- `rt` is the `reflect.Type` of `T`. -/
opaque reflType (rt : _root_.Perennial.reflect.Type') (T : go.GoType) : Prop

/-- `z` is the (non-addressable) zero `reflect.Value` of `T` (what `reflect.Zero` gives). -/
opaque reflZero (z : _root_.Perennial.reflect.Value) (T : go.GoType) : Prop

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
