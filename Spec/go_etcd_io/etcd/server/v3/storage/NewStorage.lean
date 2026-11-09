/-
## `NewStorage(lg, w, s)` (`storage.go:50-52`): trusted (names only)

**Users.** `bootstrappedRaft.newRaftNode` (`bootstrap.go:589`), once per start.
**Why it is true.** A struct literal; the WAL's open handle moves into the `RWMutex`'s invariant.
**Changes**: new (the old `NodeStartSpec` premise `rnNewStorageOk`). **Margin.** None.
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

/-- **The raft loop's storage** over the opened WAL `w` and the snapshotter `ss`. -/
def NewStorage.spec : Prop :=
  ∀ (lg w ss : Loc) (wd sd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger lg ∗ Wal.walOpen w wd ∗ Snap.isSnapshotter ss sd }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewStorage)) (Val #lg)) (Val #w)) (Val #ss))
  {{ (st : GoInterface), RET #st; ∃ s : Loc, ⌜st = storageIface s⌝ ∗ isStorage s wd sd ∗
      storageOpen s 1 }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
