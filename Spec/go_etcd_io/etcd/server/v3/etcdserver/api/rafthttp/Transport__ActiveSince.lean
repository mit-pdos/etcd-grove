/-
`(*Transport).ActiveSince(id)` (`transport.go`; rafthttp stage 6d, 2026-10-24; proved by rdslot,
2026-11-22). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`t.ActiveSince(id)`** with one of the transport's reader tokens (`transportTok`, given back):
some time (the zero time if no peer of `id` is added or it is not connected). It looks `id` up in
`t.peers` under the read lock and asks the peer's status (`peer.activeSince`, under the status's
lock). (rdslot, 2026-11-22: proved over the real code; until then a trust-boundary axiom over
`trState` alone, which read-locked without a reader token, "at most `2^30 - 1` callers at once,
physically". The request path's callers now hold a token: `srvTrReader`, in `srvLeadTimeReader`.) -/
abbrev rafthttp.Transport.ActiveSince.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      transportTok γn t c }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"ActiveSince")) (Val #id))
  {{ (tm : _root_.Perennial.time.Time), RET #tm; transportTok γn t c }}

end spec

end EtcdGrove
end Perennial
