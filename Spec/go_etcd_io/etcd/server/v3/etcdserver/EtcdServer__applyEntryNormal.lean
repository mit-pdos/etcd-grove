/-
`(*EtcdServer).applyEntryNormal(e, shouldApplyV3)` (`server.go:1970-2030`): apply a normal entry:
an empty one (a new leader's) notifies the first commit in the term and, at the leader, promotes the
lessor; else the uber-applier applies its request (`apply.Apply`) and, when it went to the backend,
its waiter is answered (`w.Trigger(id, ar)`), or, for a request refused for lack of space while no
`NOSPACE` alarm is raised, an alarm is proposed first and the waiter answered after it. The
consistent index moves to the entry when no write transaction moved it.

**Users**: `apply` (`server.go:1945`). Snippets `apply.go` (`ReqWriteAnswered`,
`ReqReplayBelowCI`), `apply.go`'s `ReqNoSpaceAlarm`.

**Proof sketch**. The thread's state machine is at `histAt γ (k - 1) σ` (or at `c ≥ k`, the replay,
`v3 = false`). Empty data: `firstCommitInTerm.Notify()` (2c's notifier); `isLeader()` then
`lessor.Promote` (3c's: no effect on the model; `Promote` extends the leases' expiry). Else
`apply.Apply(lg, e, uberApply, w, v3)` (3a's `apply.Apply.spec`, over the uber-applier's contract
the thread holds: with `v3`, its state machine moves to `histAt γ k σ'` with the answer `res` the
commit fixed, `answered γ k id res`, and the result `ar` holding `res`; its transactions' post-lock
hook sets the consistent index to the applying index `k`; with `v3 = false`, nothing moves and no
waiter is answered). `ar ≠ nil` and not `ErrNoSpace`: `w.Trigger(id, ar)` (2c's registry predicate,
satisfied by `answered γ k id res` and `ar`'s ownership, `req/` 2c). `ErrNoSpace` with no alarm
(`alarmStore.Get`, 2e's `v3alarm`): `GoAttach` a goroutine that proposes the `NOSPACE` alarm through
`raftRequest` (2c's, with the update `envUpd γ.etcd γ.cfg` gives: `EnvStep.alarm` at its commit) and
then answers the waiter with `ar` (the refusal `.err .noSpace` is a `Step` with no change, fixed at
the entry's commit). The deferred `ConsistentIndex()`/`SetConsistentIndex(k)` moves the index when
the applier wrote nothing (`Cindex`'s specs).

**Changes** from `specs-ref`'s `applyEntryNormal.spec` (two auth modes merged through `srvApplyKVC`,
`kvAppliedM`, the write-token pool, the window's `kvBatchR`): over `applyAt`; any request kind (the
applier's contract covers KV, leases, auth, alarms, membership attributes, compaction).

**Margin**: the waiter's answer and the alarm's proposal are effects on 2c's registry and the cluster
(the post states only the thread's position).
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

/-- **Apply the normal entry at index `k`**: the thread is applied through `k`; the consistent index
moves to `k` if the entry went to the backend. -/
def EtcdServer.applyEntryNormal.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ep : Loc) (p : Progress) (c ai k : Nat) (ptr : Loc)
    (e : Raft.LogEntry) (l : List Raft.LogEntry) (v3 : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ applyAt s γ ep p (k - 1) c ai ∗ entryAt ptr k e ∗ Raft.committedLb γ.raft l ∗
      ⌜0 < k ∧ l[k - 1]? = some e ∧ e.type = Raft.EntryNormal ∧ v3 = applyV3 c k ∧
        (v3 = true → ai = k)⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"applyEntryNormal")) (Val #ptr)) (Val #v3))
  {{ RET #(); applyAt s γ ep p k (if v3 then k else c) ai }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
