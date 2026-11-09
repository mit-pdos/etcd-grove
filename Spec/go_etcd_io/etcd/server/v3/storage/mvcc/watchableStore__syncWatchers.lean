/-
`(*watchableStore).syncWatchers()` (internal): under `s.mu` and `revMu`, chooses up to
`maxWatchersPerSync` unsynced watchers (`choose`: the compacted ones sent their compaction response),
reads the events of revisions `[minRev, curRev]` from the storage (`rangeEvents`), batches them per
watcher (`newWatcherBatch`), sends each watcher its batch (a full channel makes it a victim), moves the
caught-up ones to the synced group. Returns the unsynced count.

**Proof sketch.** `s.mu.Lock` (`wsMu`); `revMu.RLock` (the loop's reader, `wsLoopS`: one of the
store's own slots of its current storage borrowed for the pass, 3e's internal hand-off; `wsReadAt`
with the notified history `h`, nothing pending, the storage's image of it, `compactMainRev` its
compaction revision or `-1`); `choose` (its spec, with each member's compaction response sendable:
`cr ≤ h.compacted`, below its `minRev`; the least `minRev` it returns is at least `compactionRev`,
`minRevOf`, so `h.compacted ≤` it: `rangeEvents`' premise); `rangeEvents` (the events of `h` from
the least `minRev`, exact under the compaction condition: what the facts of the responses built
here need); `newWatcherBatch`; for each chosen watcher not behind the compaction:
`minRev` past `curRev`, or the batch's `moreRev`; `w.send` with the batch at `Revision: curRev`
(`wsSendable`: the events of its range from its position, whole revisions up to the batch's last);
`addVictim`; the gauges.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watchableStore.syncWatchers.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsLoopS s γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"syncWatchers")) (Val #()))
  {{ (n : w64), RET #n; wsLoopS s γ ∗ ⌜0 ≤ sint.Z n⌝ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
