/-
## `(*peer).stop()`

**Users.** `Transport.removePeer`, `Transport.Stop`.

**Proof sketch.** The stop right: `close(stopc)`, `cancel()`, `streamWriter.stop` ×2, `pipeline.stop`, `snapshotSender.stop`, `streamReader.stop` ×2.

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

/-- (internal) **Stops the peer**: the loops' stop channel closed, its context cancelled, the writers, pipeline, sender and readers stopped (each joined but the sender's goroutines and the two loops). -/
def peer.stop.spec : Prop :=
  ∀ (p : Loc) (ν : Net) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ peerAt p ν lid pid ∗ peerStopRight p }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer.ty @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
