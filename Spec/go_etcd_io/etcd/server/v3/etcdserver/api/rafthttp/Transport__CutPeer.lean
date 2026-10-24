/-
`(*rafthttp.Transport).CutPeer(id)` (`transport.go`). Lean-first; the partition plan's S2
(2026-10-20), an axiom to rafthttp stage 6d (2026-10-24), which restated it over the transport's
state and proved it over its callees' specs (`rafthttp.Transport.CutPeer_ok`, `TransportSpecs.lean`;
linked in stage 6f).
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

/-- **`t.CutPeer(id)`** on a frozen transport with one of its lock's reader tokens, `id` no
remote: it returns the token. It pauses the peer of `id` (`peer.Pause`, if one is added): the transport
drops every message to and from member `id` (etcd's partition injection, its integration tests' `InjectPartition`), until `MendPeer`; a dropped message is one the network may lose. `id` is no remote: a remote's `Pause` stops
its pipeline, a second one panics (`issues/nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md`). The
method set's premise `PeerPausable` (`*peer` implements `Pausable`). -/
abbrev rafthttp.Transport.CutPeer.spec : Prop :=
  PeerPausable → ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (id : w64),
  id ∉ rs.1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trFrozen γn t c rs ∗ trTok γn t c }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"CutPeer")) (Val #id))
  {{ RET #(); trTok γn t c }}

end spec

end EtcdGrove
end Perennial
