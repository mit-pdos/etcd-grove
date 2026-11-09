/-
`(*EtcdServer).snapshot(ep, toDisk)` (`server.go:2108-2160`): make a raft snapshot at the applied index
in the `MemoryStorage` (with the thread's `ConfState`, no data); to disk, first commit the KV (the
backend's consistent index at least the snapshot's), then save it (`SaveSnap`: the snapshot file and
its WAL record) and release the WAL below it.

**Users**: `snapshotIfNeededAndCompactRaftLog` (`server.go:1247`). Snippet `snapshot.go`
(`ReqSnapshotCompact`).

**Proof sketch**. To disk: clear `forceDiskSnapshot` (`forceSnapW`); `s.KV().Commit()` (3e's: the
backend commits, its pre-commit hook saving the consistent index `c ≥ appliedi`). The snapshot `sn =
(appliedi, appliedt, ep.confState, nil)` is valid: R1's `snap_make` with the delivered prefix of
length `appliedi` (`committedLb`, its term `appliedt`, the thread's) and the configuration at the
thread's point `max appliedi c ≥ appliedi` (`confAt`, `ep.confState` listing it: the replay's
configuration ahead of the index, `nonissues/etcd-replay-snapshot-confstate-ahead.md`), recorded in
the cluster's `snapsMade` with its point (`snapPoint γ sn c`, `c` the consistent index: the backend's
image at `c`).
`raftStorage.CreateSnapshot(appliedi, cs, nil)` (R1's `MemoryStorage.CreateSnapshot.spec` through
`stor_createSnapshot`, with `nodeAdvanced` for `appliedLb` and R1's `appliedLb_storedLb` for the `storedLb` it now takes; `ep.confState` a `confStateFull`): `ErrSnapOutOfDate` returns (a newer
snapshot is already stored; R1's raft never stores one past its applied index, so this is a stored
snapshot at `appliedi`: `nodeSnapLb` holds either way); any other error is excluded by the update's
precondition. `verifyConsistentIndexIsLatest.spec` (`c ≥ appliedi`, the thread's invariant). To
disk: `storage.SaveSnap(sn)`, `storage.Release(sn)` (2e's WAL and snapshotter: no error under 2e's
disk premise; `Release` keeps the records at and above `sn`, which hold the durable state).

**Changes** from `specs-ref`'s `snapshot.spec` (the memory storage's frozen ranges, `srvSnapDisk`,
the WAL's token): over `applyThread`, `nodeAdvanced`, `nodeSnapLb`; any applied index (no
`σ.b = 0` scope). **Margin**: the snapshot indices move (`memSnap := appliedi`, and `diskSnap` when
to disk); the post states only `nodeSnapLb`.

Changes: verify-round: takes and gives back the thread's `threadTok` (A7-provability F2: `s.Logger()`, `createMergedSnapshotMessage`, `newSnapshotReaderCloser` take one). `run`'s is the fresh token of `start`'s `go s.run()` (Perennial's `wp_fork_tok_body`); the apply jobs' is the scheduler worker's, lent to each job (`Schedule.funcOk`). (Superseded by re-review RR1, below.)

Changes: re-review (RR1): takes `srvStarted s γ id` (persistent; its callers `applyAll`, `apply`, `snapshotIfNeededAndCompactRaftLog` hold it): `s.Cfg.SnapshotCount` (`server.go:2116`), which `start` defaults, is read-only from then on (`srvStarted`'s), `Logger` over `srvFields` (`srvNode_fields`).
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

/-- **Snapshot at the applied index**: the node's storage then holds a snapshot at or past it. -/
def EtcdServer.snapshot.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ep : Loc) (p : Progress) (toDisk : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ applyThread s γ ep p ∗
      nodeAdvanced (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s)
        (uint.nat p.appliedi) ∗
      ⌜0 < uint.nat p.appliedi⌝ ∗ threadTok }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"snapshot")) (Val #ep)) (Val #toDisk))
  {{ RET #(); threadTok ∗ ∃ p', applyThread s γ ep p' ∗
      nodeSnapLb (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s)
        (uint.nat p.appliedi) ∗
      ⌜p'.appliedi = p.appliedi ∧ p'.appliedt = p.appliedt⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
