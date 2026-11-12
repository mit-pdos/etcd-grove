/-
`v.Set(z)` of the addressable `Value` of the `T` at `p` (on the variable `vp` holding `v`) and
the zero `Value` of `T`: `p` holds the zero value of any Lean type representing `T`.

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
    (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] (x : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗ ⌜reflElem v T p⌝ ∗
      ⌜reflZero z T⌝ ∗ p ↦ x }}
    (App (Val #(methods (go.GoType.PointerType _root_.Perennial.reflect.Value.ty) go!"Set" #vp))
      (Val #z))
  {{ RET #(); vp ↦{dq} v ∗ p ↦ (zero_val V) }}

end spec

end EtcdGrove
end Perennial
