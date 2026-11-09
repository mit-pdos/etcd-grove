/-
## `(*closeNotifier).Close()`

**Users.** the stream writer (`closeUnlocked`), `peer.attachOutgoingConn`.

**Proof sketch.** `close(done)` with the right (the channel's close payload: the handler's response writer).

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

/-- (internal) Closes the notifier (once). -/
def closeNotifier.Close.spec : Prop :=
  ∀ (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ cnAt n ∗ cnCloseRight n }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.closeNotifier.ty @!! go!"Close")) (Val #()))
  {{ RET #interface.nil; True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
