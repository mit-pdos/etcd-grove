/-
`(*valueUnstructured).reuse(v)`: sets the wrapper's interface and returns it as a `Value`
(internal: the allocators' wrappers, `NewValueInterface`, the iterations).

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
abbrev value.valueUnstructured.reuse.spec : Prop :=
  ∀ (p : Loc) (i : GoInterface) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ wrapperOwn p ∗ isIface i x }}
    (App (Val (p @!! (go.GoType.PointerType value.valueUnstructured.ty) @!! go!"reuse")) (Val #i))
  {{ (v : value.Value), RET #v; ⌜v = (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p)⌝ ∗ isValF v (DFrac.own 1) x }}

end spec

end smd
end EtcdGrove
end Perennial
