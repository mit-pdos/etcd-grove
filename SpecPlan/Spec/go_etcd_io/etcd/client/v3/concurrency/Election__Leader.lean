/-
`(*concurrency.Election).Leader(ctx)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippet: `concurrency/election.go` (`ReqLeader`).

Proof sketch: `isSession_client`; `WithFirstCreate.spec`; the KV contract's `Get(ctx, pfx,
WithFirstCreate()...)` (a linearizable read, update from `etcdPeek`; `Reach σ0`): its reply at
`σ` (`RangeReq.answers`: sorted by create revision ascending, limit 1: `firstCreate`); none:
`ErrElectionNoLeader`; an error returned.

Changes: from `specs-ref`'s `Election__Leader.lean`: over the cluster's states (`holdsAt` at a
reached state) instead of `leaderKvAt`. Round 1: `σ0`; the principal per call.

Changes: verify-round: `ErrElectionNoLeader` the value its variable holds (A3 F4).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.concurrency.Api

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

/-- `e.Leader(ctx)`: the reply listing the leader's key-value (the oldest key under the prefix,
`holdsAt`) at a state the cluster reached, its header that state's; or `ErrElectionNoLeader`, the
prefix empty at a state the cluster reached; or another error. -/
def Election.Leader.spec : Prop :=
  ∀ (e s c : Loc) (pfx : GoString) (γ : Cluster) (dflt who : Principal) (id : w64)
    (ctx : GoInterface) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ isSession s c γ id ∗ isClient c γ dflt ∗ Context.ctxOk ctx ∗
      ctxPrin dflt ctx who ∗ etcdPeek γ ∗ etcdLb γ σ0 }}
    (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"Leader")) (Val #ctx))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (hm : HeaderM) (v : KV) (σ : State),
          rangeRespOwn resp (DFrac.own 1) m ∗ etcdLb γ σ ∗
          ⌜Reach σ0 σ ∧ m.hdr = some hm ∧ hm.revision = W64 σ.kv.rev ∧ m.kvs = [KeyValueM.ofKV v] ∧
            σ.kv.store v.key = some (recOf v) ∧ holdsAt pfx v.key v.createRev σ.kv.store⌝) ∨
      (⌜resp = null⌝ ∗ globalAddr go_etcd_io.etcd.client.v3.concurrency.ErrElectionNoLeader ↦□ err ∗ ∃ σ : State, etcdLb γ σ ∗
          ⌜Reach σ0 σ ∧ ∀ k, pfx <+: k → σ.kv.store k = none⌝) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end Concurrency
end EtcdGrove
end Perennial
