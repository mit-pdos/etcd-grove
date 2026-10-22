/-
`v.Addr()` of the addressable `Value` of the `T` at `p` (the call as Goose translates it: on the
variable `vp` holding `v`): the `Value` of the pointer `p`.

The trust boundary: an axiom, `Proof/reflect/Value__Addr.lean` (`reflect` is names-only; the reasoning
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
abbrev reflect.Value.Addr.spec : Prop :=
  ∀ (vp : Loc) (dq : DFrac) (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗ ⌜reflElem v T p⌝ }}
    (App (App (Val (GoInstruction (MethodResolve
      (go.GoType.PointerType _root_.Perennial.reflect.Value.ty) go!"Addr"))) (Val #vp)) (Val #()))
  {{ (w : _root_.Perennial.reflect.Value), RET #w; vp ↦{dq} v ∗ ⌜reflPtr w T p⌝ }}

end spec

end EtcdGrove
end Perennial
