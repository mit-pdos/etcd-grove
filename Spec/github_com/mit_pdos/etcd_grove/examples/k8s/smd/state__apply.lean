/-
`(*state).apply(config, manager, msg)`: when the model's `stApply` returns (no error, no panic),
the state becomes its new state and the call returns whether the object changed.

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
abbrev state.apply.spec : Prop :=
  ∀ (s sc : Loc) (st st' : St) (m : GoMap) (kvs : List (GoString × UVal)) (mgr msg : GoString)
    (ch : Bool),
  stOk st = true → stApply st (.map kvs) mgr = some (st', ch) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗ ownState s sc st ∗ ownUMap m kvs }}
    (App (App (App (Val (s @!! go.GoType.PointerType _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.ty @!! go!"apply")) (Val #m)) (Val #mgr))
      (Val #msg))
  {{ RET #ch; ownState s sc st' }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
