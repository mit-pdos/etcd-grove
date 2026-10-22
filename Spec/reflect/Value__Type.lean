/-
`v.Type()` of the `Value` of a `T` (on the variable `vp` holding `v`): the `reflect.Type` of `T`.

The trust boundary: an axiom, `Proof/reflect/Value__Type.lean` (`reflect` is names-only; the reasoning
principles of `Proof/reflect/Values.lean`). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]

/-- See the file header. -/
abbrev reflect.Value.Type.spec : Prop :=
  ∀ (vp : Loc) (dq : DFrac) (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗ ⌜reflElem v T p⌝ }}
    (App (Val #(methods (go.GoType.PointerType _root_.Perennial.reflect.Value.ty) go!"Type" #vp))
      (Val #()))
  {{ (rt : _root_.Perennial.reflect.Type'), RET #rt; vp ↦{dq} v ∗ ⌜reflType rt T⌝ }}

end spec

end EtcdGrove
end Perennial
