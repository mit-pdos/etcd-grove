/-
## `NewLeaderStats(lg, id)` (`leader.go`): translated

**Users.** `NewServer`. **Proof sketch.** A struct literal (an empty followers map, its mutex).
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

/-- **The leader's statistics.** -/
def NewLeaderStats.spec : Prop :=
  ∀ (lg : Loc) (id : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ Zap.isLogger lg }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewLeaderStats)) (Val #lg)) (Val #id))
  {{ (p : Loc), RET #p; leaderStatsOwn p }}

end spec

end V2stats
end EtcdGrove
end Perennial
