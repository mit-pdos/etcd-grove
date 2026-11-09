/-
## `(*pipeline).handle()`

**Users.** `pipeline.start` (forked four times).

**Proof sketch.** Loop: a `select` on `msgc` (a message with `outMsg`) and `stopc`; `pbutil.MustMarshalMessage` (an encoding `e`, `RaftPb.msgEncodes e m`; no panic for a message raft sent), `post` with the facts; the status, follower stats (2e: no-ops), `Raft.ReportUnreachable`/`ReportSnapshot`, metrics. On `stopc`: `wg.Done()` with the worker's share.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (A8 F8): the sketch over raftpb's `msgEncodes`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal; a worker goroutine) **Posts each queued message** until stopped; reports unreachable on a failure, `ReportSnapshot` for a `MsgSnap` (none: `sendable`). -/
def pipeline.handle.spec : Prop :=
  ∀ (pl : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ pipeAt pl ν lid pid ∗ pipeWorker pl }}
    (App (Val (pl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline.ty @!! go!"handle")) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
