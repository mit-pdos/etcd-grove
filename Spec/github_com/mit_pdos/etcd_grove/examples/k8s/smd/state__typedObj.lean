/-
`(*state).typedObj(obj)`: the object, valid as a `root` of the scenario's schema, typed (a new
`*TypedValue` of the state's schema); the state's schema indexes are threaded through.

Lean-first (2026-11-19, notes/smd-robustness.md).
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
  ∀ (s sc : Loc) (st : St) (m : GoMap) (kvs : List (GoString × UVal)),
  validate k8s_smd.sc rootRef (.map kvs) = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗ ownState s sc st ∗ ownUMap m kvs }}
    (App (Val (s @!! go.GoType.PointerType _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.ty @!! go!"typedObj")) (Val #m))
  {{ (p : Loc), RET #p; ownState s sc st ∗ ownTV p sc ⟨some (.map kvs), rootRef⟩ }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
