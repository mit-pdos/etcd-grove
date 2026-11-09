/-
## `(*peer).sendSnap(m)`

**Users.** `Transport.SendSnapshot`.

**Proof sketch.** Fork `snapshotSender.send` (`ssAt` from `peerAt`) with `outSnap`.

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

/-- (internal) **Sends a merged snapshot** on a new goroutine (`snapshotSender.send`). -/
def peer.sendSnap.spec : Prop :=
  ∀ (p : Loc) (ν : Net GF) (lid pid : w64) (mp : Loc) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ peerAt p ν lid pid ∗ outSnap ν mp }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer.ty @!! go!"sendSnap")) (Val #mp))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
