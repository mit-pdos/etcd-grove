/-
`(*EtcdServer).applyAll(ep, apply)` (`server.go:979-1019`): one batch: install its snapshot, apply
its entries, trigger the applied index's waiters, wait for the loop's disk writes and for raft's
`Advance`, snapshot and compact the raft log if due, and merge a queued `MsgSnap`.

**Users**: `run`'s scheduled job (`server.go:841`). Snippets `apply.go` (`ReqWriteAnswered`,
`ReqAppliedRead`), `snapshot.go` (`ReqSnapshotCompact`, `ReqMergedSnapshot`, `ReqInstallSnapshot`).

**Proof sketch**. `applySnapshot.spec` (the applied index at `B.base`), `applyEntries.spec` (at
`B.last`); `backend.VerifyBackendConsistency(s.Backend(), ...)` (4a's: no panic on a consistent
backend; `s.Backend()` under `bemu`'s read lock); `applyWait.Trigger(appliedi)` (2c's
`timeList.Trigger`, the list's predicate `srvApplied s γ`, from `applyThread_applied`);
`<-apply.notifyc` (the loop's `Save` of this batch done: the WAL holds it); then `raftAdvancedC`'s
close (`nodeAdvanced r B.last`) or `s.stopping` (return, the thread's state given back);
`snapshotIfNeededAndCompactRaftLog.spec` with `nodeAdvanced`; finally a non-blocking receive on
`msgSnapC` (`msgSnapC_recv`: a `MsgSnap` pointer `m` the node sent, `msgPts`, `msgSent`, `m.term ≠
0`): if `m.term = B.term` (so `B.term ≠ 0`: after a restart `raftTerm` is `0` until the first
non-empty hard state, and then the guard fails) and its snapshot's index is at most `appliedi`,
`createMergedSnapshotMessage.spec` with `appliedt ≤ B.term` (`applyBatch_terms`: R1's term bound on
a batch, requested in `req/go_etcd_io_raft_v3.md`, "from 2d (round 1)"; the applied term is the
batch's last entry's, or the snapshot's, or an earlier batch's, each at most `B.term`) and the
thread's configuration (`ep.confState` at its point `c ≥ appliedi`), then `sendMergedSnap.spec`
(with `srvStarted`).

**Changes** from `specs-ref`'s `applyAll.specBatch` (about 60 conjuncts over the restart point, the
window, the receipts' bound, the auth component, `kvAppliedM`, `srvRestR`, the WAL token, ...): over
`applyThread` and `applyBatch`; any batch (with or without a snapshot, any restart point); the
merged snapshot's guard is the code's (`m.term = raftTerm`, `index ≤ appliedi`), with no window
premise (`winNoMergedSendR`, false at a restart, is gone: the history is the cluster's, so a merged
snapshot at any applied index is valid).

**Margin**: the batch's snapshot and entries are applied (the post says only where the applied index
is; the history it reflects is `applyThread`'s).

Changes: verify-round: takes and gives back the thread's `threadTok` (A7-provability F2: `s.Logger()`, `createMergedSnapshotMessage`, `newSnapshotReaderCloser` take one). `run`'s is the fresh token of `start`'s `go s.run()` (Perennial's `wp_fork_tok_body`); the apply jobs' is the scheduler worker's, lent to each job (`Schedule.funcOk`). The `srvMember` that `Logger` takes comes from `srvNode_member`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

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

/-- **Apply one batch**: the applied index moves to the batch's end. -/
def EtcdServer.applyAll.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ep ap : Loc)
    (apv : go_etcd_io.etcd.server.v3.etcdserver.toApply) (p : Progress) (B : ApplyBatch),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ applyThread s γ ep p ∗ ap ↦□ apv ∗
      applyBatch (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ apv B
        false ∗
      ⌜uint.nat p.appliedi = B.prev⌝ ∗ threadTok }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"applyAll")) (Val #ep)) (Val #ap))
  {{ RET #(); threadTok ∗ ∃ p', applyThread s γ ep p' ∗ ⌜uint.nat p'.appliedi = B.last⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
