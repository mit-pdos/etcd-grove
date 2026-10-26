/-
The trust boundary: `(*v2stats.LeaderStats).Follower(name)` (names-only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.LeaderStats__Follower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 6b): `LeaderStats.Follower` (`leader.go`) takes the stats'
lock, returns the follower's `*FollowerStats`, made and stored if absent. -/
axiom v2stats.LeaderStats.Follower.wp_proof : v2stats.LeaderStats.Follower.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
