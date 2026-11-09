/-
`(*concurrency.Election).Proclaim(ctx, val)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippets: `concurrency/election.go` (`ReqCampaignProclaim`, `ReqResumedProclaim`).

Proof sketch: no leader session: `ErrElectionNotLeader` (`init.spec`), nothing sent. Else
(`electionSt_session`: it is `s`) the KV contract's `Txn` with `If(CreateRevision(key) = rev)`,
`Then(OpPut(key, val, WithLease(lease)))` (update from the lent permission: a put of the leader
key with `val` and the session's lease); its reply at `σ`: succeeded, the comparison held at `σ`
(as W0's `Compare.holds` decides it: at `rev = 0` an absent key passes, and the put creates it),
the put's step (`putKey`, the lease live: a put with a dead lease is an error) and the header
(persisted) of `σ`'s next revision; failed, the comparison false at `σ`, the leader key cleared,
`ErrElectionNotLeader`; an error, unchanged. The lent permission (`etcdLent γ T P`, token `P`): each write's update is built
from it, each read's from its `etcdPeek`; `etcdLb_reach` in the first firing gives `Reach σ0`. `P` is
returned on every outcome whose writes have all been answered.

Changes: from `specs-ref`'s `Election__Proclaim.lean`: over the cluster's states (`etcdLb` of the
states before and after) instead of `proclaimedAt`/`notLeaderAt`. Round 1: the fence stated as the
comparison (the round-0 post claimed the key present, false at `leaderRev = 0`:
`nonissues/etcd-v3election-proclaim-rev-zero.md`); the effect a put of the leader key only; the lent
permission; `σ0`; the principal per call.

Margin: after a failed `Proclaim` the leader key is `""` while the leader session stays (a second
`Proclaim` or `Resign` then sends a transaction on the empty key, which etcd refuses: an error).
With `leaderRev > 0` (after `Campaign`), the comparison's holding means the key is present with that
create revision (`etcdLb_init`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `e.Proclaim(ctx, val)`: `nil`, the fence `CreateRevision(leaderKey) = leaderRev` held at a
state `σ` after `σ0` and the leader key was put to `val` with the session's lease (`σ` to `putKey σ
...` a step the cluster took); or `ErrElectionNotLeader`: no leader session, or the fence failed at
a state after `σ0` (the leader key cleared); or another error, unchanged. -/
def Election.Proclaim.spec : Prop :=
  ∀ (e s c : Loc) (pfx : GoString) (st : ElectionSt) (γ : Cluster) (dflt who : Principal) (id : w64)
    (ctx : GoInterface) (val : GoString) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ electionSt e st ∗ isSession s c γ id ∗ isClient c γ dflt ∗
      Context.ctxOk ctx ∗ ctxPrin dflt ctx who ∗
      etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (putEff (fun k => k = st.leaderKey) (fun v => v = val) (sint.Z id)) T⌝ }}
    (App (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"Proclaim")) (Val #ctx)) (Val #val))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil ∧ st.leaderSession = s⌝ ∗ P ∗ ∃ (hd : Loc) (hm : HeaderM) (σ : State),
          electionSt e { st with hdr := hd } ∗ etcdLb γ σ ∗
          etcdLb γ (putKey σ st.leaderKey val (sint.Z id)) ∗ respHeaderOwn hd DFrac.discard hm ∗
          ⌜Reach σ0 σ ∧ (ownerCmp st.leaderKey st.leaderRev).holds σ.kv.store ∧
            hm.revision = W64 (σ.kv.rev + 1)⌝) ∨
      (⌜err = concErrVal .electionNotLeader⌝ ∗ P ∗
          ((⌜st.leaderSession = null⌝ ∗ electionSt e st) ∨
           (∃ σ : State, electionSt e { st with leaderKey := [] } ∗ etcdLb γ σ ∗
              ⌜Reach σ0 σ ∧ ¬ (ownerCmp st.leaderKey st.leaderRev).holds σ.kv.store⌝))) ∨
      (⌜err ≠ GoInterface.nil ∧ ∀ e, err ≠ concErrVal e⌝ ∗ electionSt e st) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
