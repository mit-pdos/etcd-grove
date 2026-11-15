/-
`(*concurrency.Election).Campaign(ctx, val)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippets: `concurrency/election.go` (`ReqCampaignProclaim`, `ReqLeaderFenced`).

Proof sketch: `isSession_client`; `fmt.Sprintf` (the key `k` under the prefix); the KV contract's
`Txn` with `If(CreateRevision(k) = 0)`, `Then(OpPut(k, val, WithLease(lease)))`,
`Else(OpGet(k))` (update from the lent permission: `campaignEff`'s put); its reply at `σt`: created, `c` is
the header's revision and `k` holds `val` there; else `c` is `k`'s create revision and its value
the get's; if that value is not `val`, `Election.Proclaim.spec` (`k`, `c`, the session: its
success puts `val` keeping `c`; its failure: `Election.Resign.spec` and the error; after `ErrElectionNotLeader` the leader key
is `""`, and `Resign`'s premise over `k = "" ∧ k ≠ ""` is the identity, within any `T`; after another
error it is `k`, whose delete is `campaignEff`'s).
`waitDeletes.spec` with `c - 1` (`etcdLb_init`: `c ≥ 2`): at `σ` nothing under the prefix is
older than `c`. On its error, `ctx.Done()` in a `select` with a default (`Context.Done.spec`,
`doneRecv`): `Resign(client.Ctx())` (1c's `Client.Ctx.spec`) or the leader session cleared.
The header kept is the transaction's (persisted), whose revision is between `c` and `σ`'s.
The lent permission (`etcdLent γ T P`, token `P`): each write's update is built
from it, each read's from its `etcdPeek`; `etcdLb_reach` in the first firing gives `Reach σ0`. `P` is
returned on every outcome whose writes have all been answered.

Changes: from `specs-ref`'s `Election__Campaign.lean`: over the cluster's states; the old
`leaderAt ∨ campaignLost` is the one fact `waitedFor` (no claim that the key is present:
`nonissues/election-campaign-key-check.md`), whose use is the fence of `Proclaim`/`Resign` and
user transactions (`fence`). Any context. Round 1: the lent permission, `σ0`, the principal
per call; the cleanup `Resign` (as the client's own principal on a done context) has
`campaignEff`'s delete.

Changes: verify-round: the key is the session's (`sessKey`; `campaignEff` touches only it, A3 completeness F2); the cleanup `Resign` after a failed fence closes through `Resign`'s sharpened premise (A3 F2).

Margin: errors unclassified, the state after one any.
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

/-- `e.Campaign(ctx, val)`: `nil` with the election leading with the session's key `k` under
the prefix, created at `c`: `k` held `val` with that create revision at a state the cluster
reached, and at a later one nothing under the prefix was older than `c` (`waitedFor`; with
`fence`, wherever `k` still has create revision `c`, it is the leader); or an error. -/
def Election.Campaign.spec : Prop :=
  ∀ (e s c : Loc) (pfx : GoString) (st : ElectionSt) (γ : Cluster) (dflt who : Principal) (id : w64)
    (ctx : GoInterface) (val : GoString) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ electionSt e st ∗ isSession s c γ id ∗ isClient c γ dflt ∗
      Context.ctxOk ctx ∗ ctxPrin dflt ctx who ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (campaignEff pfx val (sint.Z id)) T⌝ }}
    (App (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"Campaign")) (Val #ctx)) (Val #val))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ P ∗ ∃ (k : GoString) (cr : Nat) (hd : Loc) (hm : HeaderM) (σ σv : State),
          electionSt e { leaderKey := k, leaderRev := W64 cr, leaderSession := s, hdr := hd } ∗
          etcdLb γ σ ∗ etcdLb γ σv ∗ respHeaderOwn hd DFrac.discard hm ∗
          ⌜Reach σ0 σv ∧ Reach σ0 σ ∧ k = sessKey pfx (sint.Z id) ∧ waitedFor pfx k cr σ ∧ (cr : Int) ≤ sint.Z hm.revision ∧
            sint.Z hm.revision ≤ σ.kv.rev ∧
            ∃ r, σv.kv.store k = some r ∧ r.createRev = cr ∧ r.value = val⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ st' : ElectionSt, electionSt e st') }}

end spec

end Concurrency
end EtcdGrove
end Perennial
