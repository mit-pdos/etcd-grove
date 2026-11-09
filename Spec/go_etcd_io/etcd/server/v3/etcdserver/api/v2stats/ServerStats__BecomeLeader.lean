/-
## `(*ServerStats).BecomeLeader(…)` (v2stats): names only

**Users.** 2d's ready handler. **Why it is true.** Counters under the statistics' lock. **Changes**: from
`specs-ref` where it existed. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Api
public import Spec.go_uber_org.zap.Api

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

/-- **`BecomeLeader`**: statistics only. -/
def ServerStats.BecomeLeader.spec : Prop :=
  ∀ (p : Loc) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ isServerStats p }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats.ty @!! go!"BecomeLeader")) (Val #()))
  {{ RET #(); True }}

end spec

end V2stats
end EtcdGrove
end Perennial
