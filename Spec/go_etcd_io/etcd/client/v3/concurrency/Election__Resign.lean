/-
`(*concurrency.Election).Resign(ctx)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippets: `concurrency/election.go` (`ReqCampaignProclaim`, `ReqResumedProclaim`).

Proof sketch: no leader session: `nil`, unchanged. Else the KV contract's `Txn` with
`If(CreateRevision(key) = rev)`, `Then(OpDelete(key))` (update from `etcdPerm`: `keysEff`'s
delete of the leader key); its reply at `σ'` (the key deleted if the fence held, else unchanged:
either way it has no create revision `rev` there), the header kept (persisted); the leader key
and session cleared whatever the outcome.

Changes: from `specs-ref`'s `Election__Resign.lean`: over the cluster's states.

Margin: none.
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

/-- `e.Resign(ctx)`: without a leader session `nil`, unchanged; else the leader key and session
cleared, and `nil` with the key not at its create revision at a state the cluster reached (the
header kept is that state's), or an error. -/
def Election.Resign.spec : Prop :=
  ∀ (e s : Loc) (pfx : GoString) (st : ElectionSt) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ electionSt e st ∗ isSession s γ who id ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ etcdPerm γ T ∗ ⌜effIn (keysEff (fun k => k = st.leaderKey) 0) T⌝ }}
    (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"Resign")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜st.leaderSession = null ∧ err = GoInterface.nil⌝ ∗ electionSt e st) ∨
      (⌜st.leaderSession ≠ null⌝ ∗ ∃ hd : Loc,
          electionSt e { st with leaderKey := [], leaderSession := null, hdr := hd } ∗
          ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : HeaderM) (σ : State), etcdLb γ σ ∗
              respHeaderOwn hd DFrac.discard hm ∗
              ⌜hm.revision = W64 σ.kv.rev ∧ ¬ (∃ r, σ.kv.store st.leaderKey = some r ∧ (r.createRev : Int) = sint.Z st.leaderRev)⌝) ∨
           ⌜err ≠ GoInterface.nil ∧ hd = st.hdr⌝)) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
