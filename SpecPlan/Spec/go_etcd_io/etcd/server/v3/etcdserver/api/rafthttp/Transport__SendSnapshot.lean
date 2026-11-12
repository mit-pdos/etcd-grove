/-
## `(*Transport).SendSnapshot(m)`

**Users.** etcd's `sendMergedSnap` (`server.go:1886`), on `createMergedSnapshotMessage`'s message (`snapshot_merge.go:32-53`), then waits on `merged.CloseNotify()`. Snippet: `snapshot.go` (`ReqSendMergedSnapshot`).

**Proof sketch.** `Lock`; the peer of `To`: `peer.sendSnap` (a goroutine runs `snapshotSender.send`, which closes the message once); none: `m.CloseWithError(errMemberNotFound)` (snap's close right). `Unlock`.

**Changes.** Restated: was `netSnapBundle` with the image certificate `N.img`; now `outSnap`: 2e's `isMessage`/`msgClose`/`dbReader` with the client's `snapImg` (`ν.img`).

**Margin.** The outcome (`ReportSnapshot`, the close notification's boolean) is not stated (liveness).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- **Sends a merged snapshot message** (`outSnap`): delivered at most once, its database saved at the receiver first (the client's `saveOk` update fired: `recvd`'s `dbIn`), or failed; the message is closed exactly once (its `CloseNotify` then yields the outcome). -/
def Transport.SendSnapshot.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64) (mp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ outSnap ν mp }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"SendSnapshot")) (Val #mp))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
