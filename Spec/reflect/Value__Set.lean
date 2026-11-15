/-
`v.Set(z)` of the addressable `Value` of the `T` at `p` (on the variable `vp` holding `v`) and
either the zero `Value` of `T` (`p` then holds the zero value of any Lean type representing `T`)
or, for a slice type `[]E`, the `Value` of a slice `s` (`reflect.MakeSlice`'s, `reflect.Append`'s:
`p` then holds `s`; restated in stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked T11).

Faithful: `Set` stores the value's contents into the addressable location (`reflect/value.go`:
`typedmemmove`; for a slice, its header).

The trust boundary: an axiom, `Proof/reflect/Value__Set.lean` (`reflect` is names-only; the reasoning principles of `Proof/reflect/Values.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

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

/-- See the file header. -/
abbrev reflect.Value.Set.spec : Prop :=
  ∀ (vp : Loc) (dq : DFrac) (v z : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc)
    (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] (x y : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗ ⌜reflElem v T p⌝ ∗
      ⌜reflZero z T ∧ y = zero_val V ∨ ∃ E s, T = go.GoType.SliceType E ∧ reflSliceV z E s ∧
        HEq y s⌝ ∗ p ↦ x }}
    (App (Val #(methods (go.GoType.PointerType _root_.Perennial.reflect.Value.ty) go!"Set" #vp))
      (Val #z))
  {{ RET #(); vp ↦{dq} v ∗ p ↦ y }}

end spec

end EtcdGrove
end Perennial
