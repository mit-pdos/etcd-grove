/-
## `(*snapshotSender).send(merged)`

**Users.** `peer.sendSnap` (forked).

**Proof sketch.** `createSnapBody` (`snapBodyAt`, snap's close right kept), `picker.pick`, `createPostRequest` (`POST /raft/snapshot`), a ticket and the deposit of the credit (`snapReq`), `post`; `defer merged.CloseWithError(err)` (snap's right, once); on an error `reportCriticalError` for `errMemberRemoved`, `unreachable`, `deactivate`, `Raft.ReportUnreachable`, `ReportSnapshot(SnapshotFailure)`; else `activate`, `ReportSnapshot(SnapshotFinish)`; metrics.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

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

/-- (internal; a goroutine) **Posts a merged snapshot** and closes the message once with the outcome; reports the snapshot's fate. -/
def snapshotSender.send.spec : Prop :=
  ∀ (s : Loc) (ν : Net) (lid pid : w64) (mp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ ssAt s ν lid pid ∗ outSnap ν mp }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender.ty @!! go!"send")) (Val #mp))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
