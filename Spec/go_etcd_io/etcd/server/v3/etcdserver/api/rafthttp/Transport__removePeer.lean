/-
## `(*Transport).removePeer(id)`

**Users.** `RemovePeer`, `RemoveAllPeers`.

**Proof sketch.** The map entry's `peerStopRight`: `peer.stop`; delete; `delete(LeaderStats.Followers, ...)` (`leaderStatsOwn`, kept in the lock's invariant); the probes removed (trust). `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** New (no old spec). verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

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

/-- (internal) Under the lock: stops and removes peer `id` if present. -/
def Transport.removePeer.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ trMaps t ν lid }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"removePeer")) (Val #pid))
  {{ RET #(); trMaps t ν lid }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
