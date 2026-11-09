/-
`(*EtcdServer).applyConfChange(cc, ep, shouldApplyV3)` (`server.go:2032-2106`): validate a committed
legacy conf change against the membership; refused: apply a no-op to raft (`NodeId := None`) and move
the consistent index; accepted: (when `shouldApplyV3`) apply it to raft and record the new
`ConfState`, save it with the next backend commit, and change the membership and the transport's
peers. Reports whether this member was removed.

**Users**: `apply` (`server.go:1952`). Snippets `apply.go` (`ReqConfChangeAnswered`,
`ReqReplayBelowCI`).

**Proof sketch**. The entry at `k` is committed with configuration `confAt γ.raft (k - 1) m`. R1's
`nodeConf` is the `Ready` loop's (round 1, F3): for a batch with conf changes the loop lends it to the
apply thread through the batch (`applyBatch`) and waits on `notifyc`'s second send until the apply
thread has applied them, which returns it (`raft.go:317-324, 337-343`); `applyAt` holds it while
lent (at `k - 1`, or past it at `c ≥ k` in the replay). The decision is the
cluster's (R1's `confDecide`, once, by the first member to apply the entry; every later member finds
`confDecided` and agrees because `ValidateConfigurationChange` is a function of the history's
membership at `k - 1`, `histAt γ (k - 1) σ`, and the member-local `maxLearners`, equal on every member: 2e's
configuration premise; 2e's `Membership` spec). An accepted change applies in raft (`confDecide`
needs `d.step m = some m'`): validation does not check for the last voter, so this rests on the
proposer's `mayRemoveMember`, which concurrent removals can race (round 1, S6:
`nonissues/etcd-concurrent-remove-last-voter.md`; a scope restriction of the workload: no two
`RemoveMember` calls in flight at once). Refused: `cc.NodeId := 0`,
`s.r.ApplyConfChange(cc)` (`raftNode.ApplyConfChange.spec`: R1's legacy change at node `0` changes
nothing, `Membership.applyChange_v1`); with `v3`, `ConsistentApplyingIndex()` then
`SetConsistentIndex` (`Cindex`). Accepted with `v3`: `s.r.ApplyConfChange(cc)` gives the new
`ConfState` (the view at `k`); `beHooks.SetConfState` (2e's hooks: saved with the next commit, with
the consistent index `k`); the membership change (`AddMember`/`PromoteMember`/`RemoveMember`/
`UpdateRaftAttributes`, 2e's `Membership`: their backend writes run the post-lock hook, which sets
the consistent index to `k`); the context's JSON decodes and names the change's node (the
proposer built it, `configure`: the cluster's invariant on conf-change proposals, so the two
`lg.Panic`s are unreachable); the transport's `AddPeer`/`RemovePeer`/`UpdatePeer` (2f). Without
`v3` (replayed below the consistent index): raft is not called (its configuration is already past
`k`: R1's restart at the backend's configuration), the membership's in-memory view is updated
(`shouldApplyV3 = false`: no backend write).

**Changes** from `specs-ref`'s `applyConfChange.spec` (`kvAppliedM`, the restart point, `epCsAt` at
the ghost log): over `applyAt`; the decision is R1's `confDecide` (was etcd's own conf ghost).

**Margin**: `removed` is `true` iff an accepted `RemoveNode` names this member; the post does not say
so. A refusal's error is the membership's (2e's `ErrIDRemoved`, `ErrIDExists`, ...): the post says
only that it is not `nil`.

Changes: verify-round: takes and gives back the thread's `threadTok` (A7-provability F2: `s.Logger()`, `createMergedSnapshotMessage`, `newSnapshotReaderCloser` take one). `run`'s is the fresh token of `start`'s `go s.run()` (Perennial's `wp_fork_tok_body`); the apply jobs' is the scheduler worker's, lent to each job (`Schedule.funcOk`). (Superseded by re-review RR1, below.)

Changes: re-review (RR1): takes `srvStarted s γ id` (persistent; its callers `applyAll`, `apply`, `snapshotIfNeededAndCompactRaftLog` hold it): `s.r.transport` (`server.go:2075,2085,2101`) is `srvMember`'s (`srvNode_member`), `Logger` over `srvFields` (`srvNode_fields`).
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

/-- **Apply the conf change at index `k`** (decoded into `cc`): the thread is applied through `k`. -/
def EtcdServer.applyConfChange.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ccp ep : Loc) (cc : Raft.ConfChangeV1) (p : Progress)
    (c ai k : Nat) (e : Raft.LogEntry) (l : List Raft.LogEntry) (v3 : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ applyAt s γ ep p (k - 1) c ai ∗
      Raft.confChangePts (interface.mkOk
        (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChange.ty) #ccp) (DFrac.own 1) (.v1 cc) ∗
      Raft.committedLb γ.raft l ∗
      ⌜0 < k ∧ l[k - 1]? = some e ∧ e.type = Raft.EntryConfChange ∧
        Raft.decodeConfChange e.type e.data = some (.v1 cc) ∧ v3 = applyV3 c k ∧
        (v3 = true → ai = k)⌝ ∗ threadTok }}
    (App (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"applyConfChange")) (Val #ccp)) (Val #ep)) (Val #v3))
  {{ (removed : Bool) (err : GoInterface), RET (PairV #removed #err); threadTok ∗
      applyAt s γ ep p k (if v3 then k else c) ai ∗
      ⌜err = interface.nil ∨ removed = false⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
