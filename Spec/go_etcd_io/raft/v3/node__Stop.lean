/-
## `node.Stop()`

**Users.** etcd's `raftNode.onStop` (`server/etcdserver/raft.go:420`); the examples' `Replica.stop`
/ crash (`examples/raft/kvdurable/kv.go:379`). Snippet: `restart.go` (`ReqStopRestart`).

**Proof sketch.** Send on `stop` (the run goroutine closes `done` and returns, depositing its
`nodeLoop` and the vacancy in the node's invariant as `nodeStopped`), or find `done` closed; wait for
`done`. With `nodeRunning n 1` the node's invariant gives the vacancy back (no `Ready` update can fire
any more: each takes a `nodeRunning` fraction).

**Changes.** Unchanged (over opaque predicates). The storage stays attached (a storage is attached
once: a restart uses a new one).

**Margin.** A second `Stop` returns at once; the spec takes the whole running token, which only the
first caller has.
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

/-- **Stops node `n`**: afterwards it has stopped and its id is vacant. -/
def node.Stop.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ nodeRunning n 1 }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); nodeStopped n ∗ nodeVacant γ id }}

end spec
end Raft
end EtcdGrove
end Perennial
