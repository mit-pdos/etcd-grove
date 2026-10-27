/-
`(*rafthttp.Transport).AddRemote(id, urls)` (`transport.go`). Lean-first; for `NewServer` since
stage N0 (2026-10-16, D13), an axiom from unit N4 (2026-10-17, D14e) to rafthttp stage 6d
(2026-10-24), which restated it over the transport's state and proved it over its callees' specs
(`rafthttp.Transport.AddRemote_ok`, `TransportSpecs.lean`; linked in stage 6f).
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

/-- **`t.AddRemote(id, us)`** on a started transport, by any caller (D43 M5c: no owner's right;
the handlers call it on every request, for a sender that is no peer), as `AddPeer`, of an id the
transport's pool has four `R`s for (`id ∈ c.L`, which `Start` was given them for; the remote's
pipeline's goroutines borrow them for good): it returns. It starts a remote for `id` unless the
transport is stopped or `id` is a peer or has a remote already. -/
abbrev rafthttp.Transport.AddRemote.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (id : w64) (us : GoSlice) (dq : DFrac)
    (ss : List GoString),
  ss ≠ [] → (∀ s ∈ ss, types.plainPeerURL s) →
  (∀ h, go!"http://" ++ h ∈ ss → (netRh γn).owner h = id) → c.lid ≠ id → (netRh γn).member id →
  id ∈ c.L →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trState γn t c ∗ us ↦*{dq} ss }}
    (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
      (Val #id)) (Val #us))
  {{ RET #(); us ↦*{dq} ss }}

end spec

end EtcdGrove
end Perennial
