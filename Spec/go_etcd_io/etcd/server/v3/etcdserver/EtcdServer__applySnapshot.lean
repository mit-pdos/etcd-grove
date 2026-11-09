/-
`(*EtcdServer).applySnapshot(ep, toApply)` (`server.go:1021-1179`): install a received snapshot:
open its `.snap.db` as the new backend, recover the consistent index, the lessor, mvcc, the alarm
and auth stores and the membership from it, release the WAL below it, close the old backend,
re-add the peers, and move the progress to the snapshot.

**Users**: `applyAll` (`server.go:980`). Snippet `snapshot.go` (`ReqInstallSnapshot`).

**Proof sketch**. No snapshot: return. Else (`applyBatch`'s facts, R1's `readyGot`): the snapshot
`sn` is valid (`snapValid γ.raft sn`), past the delivered log (`B.prev < sn.index`, so the
"outdated index" panic is unreachable), and its database image is kept (`snapImage γ sn`: the member's
invariant over its snapshot directory, 2e's `snapDbs`, recorded when `Process` received the
`MsgSnap` with 2f's `ν.dbIn sn.index`, `srvNet`; `snapImage_point` gives its point `a`, the same the
`Ready` loop named for the node's configuration at `Advance` (round 1, F3), under the scope of
`nonissues/etcd-merged-snapshot-same-index-image.md`). `<-notifyc`: the
loop's `SaveSnap`, `Save` and `Sync` of this batch are done (the WAL holds the snapshot record, so
`Release` below it is safe). Under `bemu`: `OpenSnapshotBackend` (2e's
`ServerStorage.OpenSnapshotBackend.spec`: the `.snap.db` of `sn.index` opens to a backend whose
image is `imgAt γ sn.index`, the state machine at `histAt γ a` with stored index `a`, the
snapshot's point; `Cindex.beStoredCI newbe a`); `consistIndex.SetBackend(newbe)`
(`Cindex.consistentIndex.SetBackend.spec`); `lessor.Recover` (3c), `kv.Restore` (3e: no error on an
image of the history), the post-lock hook set (4a); swap `s.be`; `storage.Release(sn)` (2e: no
error, the snapshot is in the WAL); `alarmStore.Recover`, `authStore.Recover`,
`cluster.SetBackend`/`Recover` (2e, 3d: from the image's records); `go oldbe.Close()` (a raw goroutine, not
attached: `run`'s `s.wg.Wait()` does not wait for it; its thread token and the old backend's closer
go with it, 4a's: the close returns); the transport's `RemoveAllPeers`/`AddPeer` of the
image's members (2f); the progress to `(sn.index, sn.term)`, `ep.confState := sn`'s (the
configuration at the snapshot's point `a`, `confAt γ.raft a m`; the node's view is the loop's, which
named the same `a` at `Advance`: round 1, F3); `NewUberApplier()` (3a's contract, established by its constructor, as the old
`apply-uber-contract` example: whoever constructs it). The state machine is at `histAt γ a`,
`a ≥ sn.index`: the entries in `(sn.index, a]` are replayed for the membership only (`apply`'s
`applyV3`), and raft's view is already at `a`, so none of them is applied to raft.

**Changes** from `specs-ref`'s `applySnapshot.specSnapM` (the mode-indexed image, the receipt, the
compaction permits, `srvSnapOwn`, the restart window `srvRestR`): one statement over `applyThread`;
compaction mode, auth mode and leases are inside the state machine (3a, 3e, 3c, 3d); the image may be
ahead of the snapshot's index (`nonissues/etcd-replay-snapshot-confstate-ahead.md`'s case).

**Margin**: none beyond the applied index.

**Integration (I4).** The install holds the store's whole `Mvcc.mvccRestoreGate γm 1` for
`s.kv.Restore` (3e: no `Hash`/`HashByRev` runs concurrently, `issues/etcd-mvcc-hash-currentrev-race.md`):
the server's invariant lends the hash checkers (`monitorKVHash`, `monitorCompactHash`, the
maintenance handlers through `isServer`) shares of it, and the apply thread takes it whole for the
install (a fractional census like `srvGate`'s). `s.lessor.Recover(newbe, rd)` takes 3c's `beOk newbe`
(4a's open share of the new backend) and installs the server's deleter closure, whose `rdOk` the
apply thread re-establishes from 3e's `mvccDeleter_rdOk` (3c, "from 3c (round 1)", item 1). The
auth store's `Recover` takes 3d's `authReached γ a'`, `recordsFit a'` of the image's auth state.

Changes: verify-round: takes and gives back the thread's `threadTok` (A7-provability F2: `s.Logger()`, `createMergedSnapshotMessage`, `newSnapshotReaderCloser` take one). `run`'s is the fresh token of `start`'s `go s.run()` (Perennial's `wp_fork_tok_body`); the apply jobs' is the scheduler worker's, lent to each job (`Schedule.funcOk`). The `srvMember` that `Logger` takes comes from `srvNode_member`.

Changes: verify-round (lease-auth's request): `authStore.Recover` takes `authBeCur γa be0` (the apply thread's, in `srvStores`) and gives back `authBeCur γa be` with `authBackendAt be0 _`. Scope (A10-completeness O1, open decision A8): `kv.Restore` takes mvcc's whole `mvccRestoreGate`, and the server's hashers (`maintenanceServer.Hash`, `HashKV`, the corruption checker's `HashByRev`, `monitorKVHash`, `monitorCompactHash`) are not synchronized with the apply thread: a run is in scope only if no hash runs during a snapshot install, a scope restriction on the server's run (the repair report's New decisions) until the user decides A8.

Changes: verify-round (server-boot's request): `OpenSnapshotBackend` returns 4a's `isBackend` through the client's allocation step (premises `Backend.envOk`, `safeRegOk`, the thread's `threadTok`, `MemoryMlock = false`: from `NewServer`'s `backendBootRes`, kept in `srvNode`); the old backend is closed through `beClosable`; no `ServerStorage.beOpen`.

Changes: verify-round (apply-txn's request): the new `NewUberApplier` (`EtcdServer.NewUberApplier.spec` over `srvStores`) gets `lessorSt`'s `ls.be = newbe` and the deleter from `lessor.Recover(newbe, rd)`, `kvDelOk` by `srvStores_kv`, `authBeCur` from `authStore.Recover`.

Changes: verify-round, last relay (server-boot's request): `OpenSnapshotBackend` takes the backend file's `Backend.beNoRevert` and returns `Backend.beRevert path o` (the renamed-over file may come back at a crash); the apply thread keeps it in the disk's state (`diskState`'s realization, reached through `diskAcc`) until the next `SaveDBFrom`'s directory fsync gives `beNoRevert` back.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Install the batch's snapshot** (if any): the applied index moves to its index. -/
def EtcdServer.applySnapshot.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ep ap : Loc)
    (apv : go_etcd_io.etcd.server.v3.etcdserver.toApply) (p : Progress) (B : ApplyBatch),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ applyThread s γ ep p ∗ ap ↦□ apv ∗
      applyBatch (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ apv B
        false ∗
      ⌜uint.nat p.appliedi = B.prev⌝ ∗ threadTok }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"applySnapshot")) (Val #ep)) (Val #ap))
  {{ RET #(); threadTok ∗ ∃ p', applyThread s γ ep p' ∗
      applyBatch (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ apv B
        true ∗
      ⌜uint.nat p'.appliedi = B.base⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
