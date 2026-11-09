/-
`(*concurrency.Election).Proclaim(ctx, val)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippets: `concurrency/election.go` (`ReqCampaignProclaim`, `ReqResumedProclaim`).

Proof sketch: no leader session: `ErrElectionNotLeader` (`init.spec`). Else (`electionSt_session`:
it is `s`) the KV contract's `Txn` with `If(CreateRevision(key) = rev)`, `Then(OpPut(key, val,
WithLease(lease)))` (update from `etcdPerm`: `keysEff`'s put of the leader key); its reply at `σ`:
succeeded, the put's step (`putKey`, the lease live: a put with a dead lease is an error) and the
header (persisted) of `σ`'s next revision; failed, the comparison false at `σ`, the leader key
cleared, `ErrElectionNotLeader`; an error, unchanged.

Changes: from `specs-ref`'s `Election__Proclaim.lean`: over the cluster's states (`etcdLb` of the
states before and after) instead of `proclaimedAt`/`notLeaderAt`.

Margin: after a failed `Proclaim` the leader key is `""` while the leader session stays (a second
`Proclaim` or `Resign` then sends a transaction on the empty key, which etcd refuses: an error).
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

/-- `e.Proclaim(ctx, val)`: `nil`, the leader key (with its create revision `leaderRev` at
`σ`) put to `val` with the session's lease, `σ` to `putKey σ ...` a step the cluster took; or
`ErrElectionNotLeader`: no leader session, or the fence failed at a state the cluster reached (the
leader key cleared); or another error, unchanged. -/
def Election.Proclaim.spec : Prop :=
  ∀ (e s : Loc) (pfx : GoString) (st : ElectionSt) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (val : GoString) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ electionSt e st ∗ isSession s γ who id ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ etcdPerm γ T ∗ ⌜effIn (keysEff (fun k => k = st.leaderKey) (sint.Z id)) T⌝ }}
    (App (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"Proclaim")) (Val #ctx)) (Val #val))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil ∧ st.leaderSession = s⌝ ∗ ∃ (hd : Loc) (hm : HeaderM) (σ : State),
          electionSt e { st with hdr := hd } ∗ etcdLb γ σ ∗
          etcdLb γ (putKey σ st.leaderKey val (sint.Z id)) ∗ respHeaderOwn hd DFrac.discard hm ∗
          ⌜(∃ r, σ.kv.store st.leaderKey = some r ∧ (r.createRev : Int) = sint.Z st.leaderRev) ∧ hm.revision = W64 (σ.kv.rev + 1)⌝) ∨
      (⌜err = concErrVal .electionNotLeader⌝ ∗
          ((⌜st.leaderSession = null⌝ ∗ electionSt e st) ∨
           (∃ σ : State, electionSt e { st with leaderKey := [] } ∗ etcdLb γ σ ∗
              ⌜¬ (∃ r, σ.kv.store st.leaderKey = some r ∧ (r.createRev : Int) = sint.Z st.leaderRev)⌝))) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ electionSt e st) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
