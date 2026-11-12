/-
## `IsLocalMsgTarget(id)`

**Users.** `node.Step`, `node.run`, `RawNode.Step`, `Config.validate`. **Changes.** Unchanged.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- `isLocalTarget`. -/
def IsLocalMsgTarget.spec : Prop :=

  ∀ (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (@! go_etcd_io.raft.v3.IsLocalMsgTarget)) (Val #id))
  {{ (b : Bool), RET #b; ⌜b = isLocalTarget id⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
