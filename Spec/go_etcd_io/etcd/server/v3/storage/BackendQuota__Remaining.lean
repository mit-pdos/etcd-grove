/-
## `(*BackendQuota).Remaining()` (`quota.go:177`): trusted (names only)

**Users.** v3rpc's maintenance status. **Why it is true.** The limit minus the backend's size (an
atomic read). **Changes**: new. **Margin.** Some value.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **`Remaining()`**: some value. -/
def BackendQuota.Remaining.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isQuota (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendQuota.ty) #p) }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendQuota.ty @!! go!"Remaining")) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
