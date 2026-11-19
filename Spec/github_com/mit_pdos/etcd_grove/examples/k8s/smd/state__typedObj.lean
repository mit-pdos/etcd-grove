/-
`(*state).typedObj(obj)`: `obj` typed as a root (it conforms: else the driver panics).

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI
open smd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- See the file header. -/
abbrev state.typedObj.spec : Prop :=
  ∀ (s sc u lv : Loc) (mfm : GoMap) (m : GoMap) (kvs : List (GoString × UVal)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗ s ↦ (_root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.mk sc u lv mfm) ∗ isSchema sc sc0 ∗ isUMap m kvs ∗
      ⌜conforms sc0 rootRef (.map kvs)⌝ }}
    (App (Val (s @!! go.GoType.PointerType _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.ty @!! go!"typedObj")) (Val #m))
  {{ (p : Loc), RET #p; s ↦ (_root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.mk sc u lv mfm) ∗ isTV p sc sc0 rootRef (.map kvs) }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
