/-
`(*EtcdServer).applySnapshot(ep, toApply)` (`server.go:1021-1179`): install a received snapshot:
open its `.snap.db` as the new backend, recover the consistent index, the lessor, mvcc, the alarm
and auth stores and the membership from it, release the WAL below it, close the old backend,
re-add the peers, and move the progress to the snapshot.

**Users**: `applyAll` (`server.go:980`). Snippet `snapshot.go` (`ReqInstallSnapshot`).

**Proof sketch**. No snapshot: return. Else (`applyBatch`'s facts, R1's `readyGot`): the snapshot
`sn` is valid (`snapValid γ.raft sn`), past the delivered log (`B.prev < sn.index`, so the
"outdated index" panic is unreachable), and carries a database image (`snapImage γ sn`: the merged
snapshot's sender made it, 2f delivered the db to the snapshotter, `req/` 2e/2f). `<-notifyc`: the
loop's `SaveSnap`, `Save` and `Sync` of this batch are done (the WAL holds the snapshot record, so
`Release` below it is safe). Under `bemu`: `OpenSnapshotBackend` (2e/4a: the `.snap.db` of
`sn.index` opens to a backend whose state machine is at `histAt γ k` for its consistent index
`k ≥ sn.index`; `Cindex.beStoredCI newbe k`); `consistIndex.SetBackend(newbe)`
(`Cindex.consistentIndex.SetBackend.spec`); `lessor.Recover` (3c), `kv.Restore` (3e: no error on an
image of the history), the post-lock hook set (4a); swap `s.be`; `storage.Release(sn)` (2e: no
error, the snapshot is in the WAL); `alarmStore.Recover`, `authStore.Recover`,
`cluster.SetBackend`/`Recover` (2e, 3d: from the image's records); `go oldbe.Close()` (an attached
goroutine: the old backend's close returns, 4a's); the transport's `RemoveAllPeers`/`AddPeer` of the
image's members (2f); the progress to `(sn.index, sn.term)`, `ep.confState := sn`'s (R1: the node
takes the snapshot's configuration at `Advance`, at the point `a ≥ sn.index` the snapshot names:
the thread's configuration view `confAt γ.raft a m` with `a = k` once the image's records are
read); `NewUberApplier()` (3a's contract, established by its constructor, as the old
`apply-uber-contract` example: whoever constructs it). The state machine is at `histAt γ k`,
`k ≥ sn.index`: the entries in `(sn.index, k]` are replayed for the membership only (`apply`'s
`applyV3`).

**Changes** from `specs-ref`'s `applySnapshot.specSnapM` (the mode-indexed image, the receipt, the
compaction permits, `srvSnapOwn`, the restart window `srvRestR`): one statement over `applyThread`;
compaction mode, auth mode and leases are inside the state machine (3a, 3e, 3c, 3d); the image may be
ahead of the snapshot's index (`nonissues/etcd-replay-snapshot-confstate-ahead.md`'s case).

**Margin**: none beyond the applied index.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false

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
  ∀ (s : Loc) (γ : Names) (id : w64) (ep ap : Loc)
    (apv : go_etcd_io.etcd.server.v3.etcdserver.toApply) (p : Progress) (B : ApplyBatch),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ applyThread s γ ep p ∗ ap ↦□ apv ∗
      applyBatch (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ apv B
        false ∗
      ⌜uint.nat p.appliedi = B.prev⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"applySnapshot")) (Val #ep)) (Val #ap))
  {{ RET #(); ∃ p', applyThread s γ ep p' ∗
      applyBatch (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ apv B
        true ∗
      ⌜uint.nat p'.appliedi = B.base⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
