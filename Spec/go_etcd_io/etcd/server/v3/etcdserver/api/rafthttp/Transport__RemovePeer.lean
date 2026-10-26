/-
`(*rafthttp.Transport).RemovePeer(id)` (`transport.go`). Lean-first; D43 M5a (2026-10-26), for
`applyConfChange`'s `RemoveNode`, stated over the transport's live state (`trLive`, the peers
right: the user's decision on W3, D43); proved in `TransportRemove.lean`.
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

/-- **`t.RemovePeer(id)`** on a live transport whose ids are `rs`: it returns, the peer of `id`
removed if there was one (`transport.go`: under the write lock, `removePeer`: the peer's `stop`, its
map entry deleted, its `LeaderStats.Followers` entry and its probers' entries removed, a log line),
or a log line if there was none: the live transport with `id` no longer among the peers' ids. -/
abbrev rafthttp.Transport.RemovePeer.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trLive γn t c rs }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"RemovePeer")) (Val #id))
  {{ RET #(); trLive γn t c (rs.1, rs.2.filter (· != id)) }}

end spec

end EtcdGrove
end Perennial
