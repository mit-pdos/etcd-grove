/-
## `node.Stop()`

**Users.** etcd's `raftNode.onStop` (`server/etcdserver/raft.go:420`); the examples' `Replica.stop`
/ crash (`examples/raft/kvdurable/kv.go:379`). Snippet: `restart.go` (`ReqStopRestart`).

**Proof sketch.** Send on `stop` (the run goroutine closes `done` and returns, depositing its
`nodeLoop` and the vacancy in the node's invariant as `nodeStopped`), or find `done` closed; wait for
`done`. With `nodeRunning n 1` the node's invariant gives the vacancy back (no `Ready` update can fire
any more: each takes a `nodeRunning` fraction).

**Changes.** Over opaque predicates; (round 1) a call on a stopped node is covered (it finds `done`
closed and returns), the vacancy given back only by the call that stopped it. The storage stays
attached (a storage is attached once: a restart uses a new one).

**Margin.** Concurrent first calls are not covered (each needs the whole running token).
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

/-- **Stops node `n`** (running, or already stopped): afterwards it has stopped; its id is vacant
again if this call stopped it. -/
def node.Stop.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (running : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ (if running then nodeRunning n 1 else nodeStopped n) }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); nodeStopped n ∗ (if running then nodeVacant γ id else iprop(True)) }}

end spec
end Raft
end EtcdGrove
end Perennial
