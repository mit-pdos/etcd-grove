/-
## `snap.New(lg, dir)` (`snapshotter.go:34-43`): trusted (names only)

**Users.** `bootstrapSnapshot` (`bootstrap`), `RecoverSnapshotBackend`. **Why it is true.** A struct
literal (a nil logger replaced by `zap.NewNop()`). **Changes**: new. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Snap

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

/-- **A snapshotter of directory `sd`.** -/
def New.spec : Prop :=
  ∀ (lg : Loc) (sd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.snap.New)) (Val #lg)) (Val #sd))
  {{ (ss : Loc), RET #ss; isSnapshotter ss sd }}

end spec

end Snap
end EtcdGrove
end Perennial
