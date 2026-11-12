/-
`(*watchableStore).Restore(b)`: the store over a new storage (a snapshot's image), every synced
watcher made unsynced: the `KV` interface's `Restore` contract (3e's) at the watchable store.

**Users.** `EtcdServer.applySnapshot` (`etcdserver/server.go:1094`, 2d: `s.kv.Restore(newbe)`).
Snippet: `mvccwatch/store.go` `ReqRestore`.

**Proof sketch.** Under `s.mu` (no write is between its two steps: `End` holds `s.mu`, so nothing is
pending and `σ.notified = σ.kv`; no loop pass is running, so both loop shares are parked, and `wsMu`
gives them, `storeLoops st γ mvccLoopN`): 3e's `store.Restore(b)` (its watched instance,
`store.Restore.watched.spec`, `InternalWatched.lean`: `mvccRestoreGate γ 1` passed through, the
loop shares swapped to the new storage and parked again, the old storage's `storageRest B
mvccReaderN` back, the loops' slots among them; the
client's update fires at a state whose history the new one extends: `histLe σ.notified σ'.kv`, so
`mvccLb`'s authority, part of `mvccState`'s realization, grows and every fact sent before stays a
fact of the new history; the loops' next passes borrow slots of `B'`); each synced watcher marked `restore` and moved to the
unsynced group (its position stays; the resync reads the new storage from it; `restore` exempts a
`minRev` above the new revision from `chooseAll`'s check).

**Changes** from `specs-ref`'s file: the canonical instance of 3e's restated contract (whose update
carries the extension the watchers need).

**Margin.** As the contract's.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalWatched
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Restore` meets `KV.Restore`'s contract. -/
def watchableStore.Restore.spec : Prop := ∀ s : Loc, KV.Restore.contract (GF := GF) (go.GoType.PointerType watchableStore.ty) #s

end spec

end Mvcc
end EtcdGrove
end Perennial
