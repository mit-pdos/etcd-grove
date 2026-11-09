/-
## `(*storage).MinimalEtcdVersion()` (`storage.go:89-107`): trusted (names only)

**Users.** The storage-version monitor's downgrade check (`monitorStorageVersion`, through the
version manager).
**Why it is true.** Under the write lock: the latest snapshot record, the WAL reopened there and
read whole (panics on any error: `diskOk`), the minimal version of its entries; the reopened WAL
replaces the old one (same directory, same records).
**Changes**: new. **Margin.** The version is not stated (a `*semver.Version`, read-only).
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

/-- **The minimal etcd version the WAL's entries need** (some read-only version). -/
def storage.MinimalEtcdVersion.spec : Prop :=
  ∀ (s : Loc) (wd sd : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isStorage s wd sd ∗ storageOpen s q ∗ ⌜diskOk⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"MinimalEtcdVersion")) (Val #()))
  {{ (v : Loc), RET #v; storageOpen s q }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
