/-
## `(*Snapshotter).DBFilePath(id)` (`db.go:98-115`): trusted (names only)

**Users.** `OpenSnapshotBackend` (2d's `applySnapshot`). **Why it is true.** The directory read
(`diskOk`), then whether `<id:016x>.snap.db` exists: a read of `snapDbs` (the update fired with the
state unchanged); its path, or `ErrNoDBSnapshot`. **Changes** (from `specs-ref`'s
`Snapshotter__DBFilePath.lean`): over the db files' model. **Margin.** The path is not named.
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

/-- **Finds the database snapshot of index `id`** (its path) or fails. -/
def Snapshotter.DBFilePath.spec : Prop :=
  ∀ (ss : Loc) (sd : GoString) (id : w64) (Q : Option BeImage → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ isSnapshotter ss sd ∗ ⌜ServerStorage.diskOk⌝ ∗
      (AU <{ ∃∃ (F : Nat → Option BeImage), snapDbs sd F }> @ ⊤, ∅
        <{ snapDbs sd F, COMM Q (F (uint.nat id)) }>) }}
    (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!! go!"DBFilePath")) (Val #id))
  {{ (path : GoString) (err : GoInterface), RET (PairV #path #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ img, Q (some img)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Q none) }}

end spec

end Snap
end EtcdGrove
end Perennial
