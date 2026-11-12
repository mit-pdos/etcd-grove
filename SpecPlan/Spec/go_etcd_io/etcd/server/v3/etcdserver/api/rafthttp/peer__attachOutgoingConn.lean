/-
## `(*peer).attachOutgoingConn(conn)`

**Users.** `streamHandler.ServeHTTP`.

**Proof sketch.** `conn.t` is one of the two types (`outConn`): the matching writer's `attach`; `false`: `conn.Close()` (the close right: the close notifier, which gives the response writer back to the handler).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
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

/-- (internal) **Hands an outgoing stream connection** to the writer of its type, or closes it (the writer stopped). -/
def peer.attachOutgoingConn.spec : Prop :=
  ∀ (p : Loc) (ν : Net GF) (lid pid : w64) (c : Loc) (t : StreamTy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ peerAt p ν lid pid ∗ outConn c ν lid pid t }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer.ty @!! go!"attachOutgoingConn")) (Val #c))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
