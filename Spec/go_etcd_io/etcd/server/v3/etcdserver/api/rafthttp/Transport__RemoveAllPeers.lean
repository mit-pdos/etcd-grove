/-
`(*rafthttp.Transport).RemoveAllPeers()` (`transport.go`). Lean-first; D22 receiver epochs, S8d
(2026-10-25), for `applySnapshot`'s transport reset, stated over the transport's live state
(`trLive`, the peers right: the user's decision on W3, D43); its proof is left to the membership
track's M5 (`notes/membership-plan.md`), which proves it rather than restating it (the user's
decision, 2026-10-25): proved in M5a (2026-10-26, `TransportRemove.lean`).
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

/-- **`t.RemoveAllPeers()`** on a live transport whose ids are `rs`: it returns, every peer
removed (`transport.go:333-339`: under the write lock, `removePeer` of each key of `t.peers`: the
peer's `stop`, its map entry deleted, its `LeaderStats.Followers` entry and its probers' entries
removed, a log line), the remotes kept: the live transport with no peer id. -/
abbrev rafthttp.Transport.RemoveAllPeers.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trLive γn t c rs }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"RemoveAllPeers"))
      (Val #()))
  {{ RET #(); trLive γn t c [] }}

end spec

end EtcdGrove
end Perennial
