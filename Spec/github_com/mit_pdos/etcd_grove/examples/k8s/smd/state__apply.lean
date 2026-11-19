/-
`(*state).apply(config, manager, msg)`: when SSA of `config` by `manager`, not forced, succeeds
(`applyResult` is `ok obj mf'`), the state becomes the new object (the old one if `obj` is `none`)
and `mf'`, and the call returns whether the object changed.

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
abbrev state.apply.spec : Prop :=
  ∀ (s sc : Loc) (st : St) (m : GoMap) (kvs : List (GoString × UVal)) (mgr msg : GoString)
    (obj : Option UVal) (mf' : MF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗ ownState s sc st ∗ isUMap m kvs ∗ ⌜conforms sc0 rootRef (.map kvs)⌝ ∗
      ⌜∀ m e, st.mf m = some e → e.version = version ∧ keysWithItems sc0 rootRef e.set⌝ ∗
      ⌜applyResult sc0 rootRef false st.live (.map kvs) version st.mf mgr false = .ok obj mf'⌝ }}
    (App (App (App (Val (s @!! go.GoType.PointerType _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.ty @!! go!"apply")) (Val #m)) (Val #mgr))
      (Val #msg))
  {{ RET #obj.isSome; ownState s sc ⟨obj.getD st.live, mf'⟩ }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
