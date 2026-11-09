/-
## `NewServerStats(name, id)` (`server.go` of v2stats): names only

**Users.** `NewServer`. **Why it is true.** A struct literal with its mutex. **Changes**: from
`specs-ref`. **Margin.** None.
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

/-- **The server's statistics.** -/
def NewServerStats.spec : Prop :=
  ∀ (name id : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewServerStats)) (Val #name)) (Val #id))
  {{ (p : Loc), RET #p; isServerStats p }}

end spec

end V2stats
end EtcdGrove
end Perennial
