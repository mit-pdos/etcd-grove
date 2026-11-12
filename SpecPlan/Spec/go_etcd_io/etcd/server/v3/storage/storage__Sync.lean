/-
## `(*storage).Sync()` (`storage.go:83-87`): trusted (names only)

**Users.** The raft loop (2d: after a leader's `Save` of a commit-only state, on a heartbeat).
**Why it is true.** `WAL.Sync`: an fsync; no change to the records' replay view. **Changes**: new.
**Margin.** The synced commit is not raised (`Wal.Recs.syncedCommit` keeps the last write's): a
crash after a `Sync` is described as if the commit-only state were still unsynced (weaker than the
code). Verify-round (A8 provability F1.2): the "no crash in scope" note dropped.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api
public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

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

/-- **Fsyncs the WAL.** -/
def storage.Sync.spec : Prop :=
  ∀ (s : Loc) (wd sd : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isStorage s wd sd ∗ storageOpen s q ∗ ⌜diskOk⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Sync")) (Val #()))
  {{ RET #GoInterface.nil; storageOpen s q }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
