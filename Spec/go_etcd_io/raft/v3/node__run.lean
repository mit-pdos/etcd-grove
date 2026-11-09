/-
## `node.run()` (internal)

**Users.** `StartNode`, `RestartNode` (`go n.run()`). **Proof sketch.** The loop holds `nodeLoop n`
(the `RawNode` and its token, the pending `Ready`, the armed channels); each `select` case is the
matching `RawNode` method's spec under the node's invariant; the `readyc` case hands the `Ready` with
`readyGot` (built from `RawNode.readyWithoutAccept`'s, the enter update relayed through the node's
`nodeRunning`) and then `acceptReady`; `stop` closes `done`, depositing the loop's state.
**Changes.** Mirrors the code.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

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

/-- (internal) The node's goroutine. -/
def node.run.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ nodeLoop n }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec
end Raft
end EtcdGrove
end Perennial
