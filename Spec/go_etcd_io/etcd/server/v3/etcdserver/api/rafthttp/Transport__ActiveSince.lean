/-
`(*Transport).ActiveSince(id)` (`transport.go`; rafthttp stage 6d, 2026-10-24). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`t.ActiveSince(id)`** on a started transport (`trState`; D43 M5c, until then a frozen one:
the peer is read under the lock, which `AddPeer`/`RemovePeer` write under), from any goroutine: some time (the zero time
if no peer of `id` is added or it is not connected). It looks `id` up in `t.peers` under the read
lock and asks the peer's status (`peerStatus.activeSince`, under the status's lock). The read lock
is taken without one of the lock's reader tokens (`trTok`): the server's request path calls it
(`isConnectedSince`), from any number of goroutines, at most `2^30 - 1` of them at once,
physically (as `netProcSlots`). -/
abbrev rafthttp.Transport.ActiveSince.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trState γn t c }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"ActiveSince")) (Val #id))
  {{ (tm : _root_.Perennial.time.Time), RET #tm; True }}

end spec

end EtcdGrove
end Perennial
