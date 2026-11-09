/-
## `node.ReportUnreachable`

**Users.** etcd's `EtcdServer.ReportUnreachable` (`server.go:726`) from rafthttp's peers on a failed send, and `snapshotSender` (`rafthttp/snapshot_sender.go:118`); the examples' lossy networks (`kvdurable/cluster.go:394`). Snippet: `transport.go` (`ReqDeliver`, `ReqSendSnapshot`).

**Proof sketch.** A local `MsgUnreachable` from `to` (any id: one that is no peer is
ignored by the leader) sent on `recvc` (`stepOk` of a local report), or `done`.

**Changes.** Unchanged. **Margin.** No effect is stated (progress tracking only: liveness).
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

/-- **Reports to node `n`** a failed send (or a snapshot's fate). Any id, any status. -/
def node.ReportUnreachable.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"ReportUnreachable")) (Val #to))
  {{ RET #(); True }}

end spec
end Raft
end EtcdGrove
end Perennial
