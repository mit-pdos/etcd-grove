/-
`(*EtcdServer).run()` (`server.go:752-853`): the apply loop, a goroutine (`start`'s `go s.run()`).

**Users**: `EtcdServer.start` (`server.go:604`, batch 2e). Snippets
`examples/specreq/etcdserverapply/apply.go` (`ReqWriteAnswered`, `ReqAppliedRead`),
`restart.go` (`ReqRestartContinues`, `ReqCrashKeepsAnswered`).

**Proof sketch**. `srvRunTok s γ id` holds what `start` built (2e): the apply thread's state at its
start (`applyThread s γ ep₀ p₀`, `p₀` all at the storage snapshot's index, the backend's state
machine at `histAt γ ci₀` for its consistent index `ci₀ ≥ p₀.appliedi`), the driver's `rnLoop` and
`rnStopper` (R1's `nodeDriver` from `StartNode`/`RestartNode`, delivered log of length
`p₀.appliedi`), the ready handler's writers, the lessor's expiry channel's receive right, the stop
channel's receive right and the escrow of `done`'s close.
1. `s.r.raftStorage.Snapshot()`: R1's `MemoryStorage.Snapshot.spec` through `stor_read` (the stored
   snapshot empty or valid, `storSnapLb`); `ErrSnapshotTemporarilyUnavailable` is never returned by
   a `MemoryStorage` (no panic). `ep`'s fields from it; its `ConfState` non-nil (`MemoryStorage`
   stores the configuration it was given: the `panic("empty confstate")` is unreachable).
2. `schedule.NewFIFOScheduler(lg)` (`Schedule.NewFIFOScheduler.spec`, `Pay := True`).
3. The ready handler `rh`: four closures over `s`'s atomics (`readyHandlerOk rh s γ`, the writers
   `readyHandlerTok rh`); `updateLeadership` calls the lessor's `Demote`/`Promote`-free paths and the
   compactor's `Pause`/`Resume` (3c's, 2e's), `leaderChanged.Notify()` (2c's notifier).
4. `s.r.start(rh)` (`raftNode.start.spec`, with `rnLoop`).
5. The loop: on `applyc` (`applyc_recv`) a batch `applyBatch r γ apv B false`, whose `B.prev` is the
   delivered log's length before it, which is the applied index the last scheduled job leaves (the
   chain's invariant: `schedTail γs (∃ p, applyThread s γ ep p ∗ ⌜p.appliedi = delivered⌝)`); schedule
   `applyAll(&ep, &ap)` (`Schedule.NewJob.spec`, `funcOk` from `EtcdServer.applyAll.spec`; the chain
   moves to the batch's end, `B.last`). On `expiredLeaseC` (3c's channel: a slice of expired leases,
   `expiredLeases`, only when `γ.cfg.leaseExpiry`): `revokeExpiredLeases.spec`. `errorc` is never
   sent on (2e's invariant: nothing writes it in the runs covered). On `s.stop` (2e's stop request):
   return.
6. The deferred shutdown: close `stopping`; `cancel()`; `sched.Stop()` (`□ True`) gives back the
   chain's end, the apply thread's last state; `s.wg.Wait()` (the attached goroutines' resources
   back); `s.r.stop()` (`raftNode.stop.spec`: `rnStopped`); `Cleanup()` (2e's: the lessor, mvcc, auth
   and backend closed, the backend's durable image); `close(done)` deposits `srvStopped s γ id`
   (the WAL's and the backend's durable halves, the node's vacancy) in the escrow 2e's stop right
   claims.

**K4-K6 through this loop**: every entry is applied in log order, after raft committed it, by the
FIFO chain; the history is the cluster's (`histAt`), so a member's restart (from `srvStopped`'s
halves) or a snapshot install continues it.

**Changes** from `specs-ref`'s `EtcdServer.run.spec`: one opaque `srvRunTok` in place of
`isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq ...) (srvDoneInv ...)`
(19 parameters); no auth-mode component, no receipt bound (`etcdState_revFits` is the cluster's,
W0's K7), **no restart premises** (the eight R2d'a premises, two of them found false: a restart is
a start whose `srvRunTok` 2e builds from the member's durable state, with the backend ahead of the
WAL allowed, `ci₀ ≥ p₀.appliedi`, and no window token); no `σ.b = 0` scope (any snapshot); the
thread token is `srvRunTok`'s.

**Margin**: `errorc`'s exit (the data directory removal) is outside: nothing sends on it.
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

/-- **The apply loop**: runs until stopped; its shutdown deposits what the stopped member leaves
(`srvStopped`) where the stop right (2e's) claims it. -/
def EtcdServer.run.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvRunTok s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"run")) (Val #()))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
