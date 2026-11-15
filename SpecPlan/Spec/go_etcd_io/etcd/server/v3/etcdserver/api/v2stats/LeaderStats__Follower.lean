/-
## `(*LeaderStats).Follower(name)` (`leader.go`): translated

**Users.** 2f's `Transport.AddPeer`. **Proof sketch.** Under the lock, the map's entry or a new one.
**Changes**: from `specs-ref`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V2stats

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Assumptions]

/-- **The follower's statistics** (made on first use). -/
def LeaderStats.Follower.spec : Prop :=
  ∀ (p : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ isLeaderStats p }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.LeaderStats.ty @!! go!"Follower")) (Val #name))
  {{ (f : Loc), RET #f; isFollowerStats f }}

end spec

end V2stats
end EtcdGrove
end Perennial
