/-
`(*rafthttp.Transport).AddPeer(id, urls)` (`transport.go`). Lean-first; for `NewServer` since stage
N0 (2026-10-16, D13), an axiom from unit N4 (2026-10-17, D14e) to rafthttp stage 6d (2026-10-24),
which restated it over the transport's state and proved it over its callees' specs
(`rafthttp.Transport.AddPeer_ok`, `TransportSpecs.lean`; linked in stage 6f).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs

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

/-- **`t.AddPeer(id, us)`** on a live transport, of `id`'s URL strings (non-empty, plain
`http://` URLs, `types.plainPeerURL`, of hosts the directory gives `id`), a member other than the
transport's own, with eight `R`s (the peer's goroutines' calls into `Raft`): `id` among the peers'
ids. -/
abbrev rafthttp.Transport.AddPeer.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (id : w64) (us : GoSlice) (dq : DFrac)
    (ss : List GoString),
  ss ≠ [] → (∀ s ∈ ss, types.plainPeerURL s) →
  (∀ h, go!"http://" ++ h ∈ ss → (netRh γn).owner h = id) → c.lid ≠ id → (netRh γn).member id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trLive γn t c rs ∗ us ↦*{dq} ss ∗ [∗list] _x ∈ List.replicate 8 (), c.R }}
    (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddPeer")) (Val #id))
      (Val #us))
  {{ RET #(); trLive γn t c (rs.1, rs.2 ++ [id]) ∗ us ↦*{dq} ss }}

end spec

end EtcdGrove
end Perennial
