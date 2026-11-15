/-
## `(*storage).Close()` (`storage.go:76-80`, `wal.go:985-1009`): trusted (names only)

**Users.** The raft node's stop (2d's `raftNode.onStop`), once, after the loop ended.

**Why it is true.** Under the write lock, `WAL.Close`: fsync the tail, release every lock. The
records stay what they are only if no purge runs (`Close` releases the locks the purge respects):
the purge's right is the premise, given back (`walPurgeRight`, the WAL API's critique 2). An fsync
error is returned (`diskOk`).

**Changes** (from `walClose_spec`): the records stay in their owner's hands (`walRecs` is not
taken: the closed directory's content is the same records). **Margin.** None.
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

/-- **Closes the WAL** (the whole `storageOpen` and the purge's right, which it gives back). -/
def storage.Close.spec : Prop :=
  ∀ (s : Loc) (wd sd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isStorage s wd sd ∗ storageOpen s 1 ∗ Wal.walPurgeRight wd ∗ ⌜diskOk⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Close")) (Val #()))
  {{ RET #GoInterface.nil; Wal.walPurgeRight wd }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
