/-
`(*Transport).ActivePeers()` (`transport.go`; rdslot, 2026-11-22). Lean-first.
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

/-- **`t.ActivePeers()`** with one of the transport's reader tokens (`transportTok`, given back):
some count (of the peers whose status is active). It ranges over `t.peers` under the read lock
and asks each peer's status (`peer.activeSince`, under the status's lock). -/
abbrev rafthttp.Transport.ActivePeers.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      transportTok γn t c }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"ActivePeers")) (Val #()))
  {{ (n : w64), RET #n; transportTok γn t c }}

end spec

end EtcdGrove
end Perennial
