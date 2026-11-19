/-
`(*valueUnstructured).IsBool()`, the method a `value.Value` dispatches to: whether the value is a `bool`. Reads the
wrapper at any share, given back (the `Value` bundle's triple, `valueIfaceM`).

Lean-first (2026-11-19, notes/smd-plan.md): Draft, the stage's per-package specs of `value`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

/-- See the file header. -/
abbrev value.valueUnstructured.IsBool_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isValF (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p) dq x }}
    (App (Val (p @!! (go.GoType.PointerType value.valueUnstructured.ty) @!! go!"IsBool")) (Val #()))
  {{ (r : Bool), RET #r; isValF (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p) dq x ∗ ⌜r = x.isBoolB⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
