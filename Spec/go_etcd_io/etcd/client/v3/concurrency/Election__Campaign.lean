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
`Else(OpGet(k))` (update from `etcdPerm`: `keysEff`'s put); its reply at `σt`: created, `c` is
the header's revision and `k` holds `val` there; else `c` is `k`'s create revision and its value
the get's; if that value is not `val`, `Election.Proclaim.spec` (`k`, `c`, the session: its
success puts `val` keeping `c`; its failure: `Election.Resign.spec` and the error).
`waitDeletes.spec` with `c - 1` (`etcdLb_init`: `c ≥ 2`): at `σ` nothing under the prefix is
older than `c`. On its error, `ctx.Done()` in a `select` with a default (`Context.Done.spec`,
`doneRecv`): `Resign(client.Ctx())` (1c's `Client.Ctx.spec`) or the leader session cleared.
The header kept is the transaction's (persisted), whose revision is between `c` and `σ`'s.

Changes: from `specs-ref`'s `Election__Campaign.lean`: over the cluster's states; the old
`leaderAt ∨ campaignLost` is the one fact `waitedFor` (no claim that the key is present:
`nonissues/election-campaign-key-check.md`), whose use is the fence of `Proclaim`/`Resign` and
user transactions (`fence`). Any context.

Margin: errors unclassified, the state after one any.
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

/-- `e.Campaign(ctx, val)`: `nil` with the election leading with the session's key `k` under
the prefix, created at `c`: `k` held `val` with that create revision at a state the cluster
reached, and at a later one nothing under the prefix was older than `c` (`waitedFor`; with
`fence`, wherever `k` still has create revision `c`, it is the leader); or an error. -/
def Election.Campaign.spec : Prop :=
  ∀ (e s : Loc) (pfx : GoString) (st : ElectionSt) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (val : GoString) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ electionSt e st ∗ isSession s γ who id ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ etcdPerm γ T ∗ ⌜effIn (keysEff (fun k => pfx <+: k) (sint.Z id)) T⌝ }}
    (App (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"Campaign")) (Val #ctx)) (Val #val))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (k : GoString) (c : Nat) (hd : Loc) (hm : HeaderM) (σ σv : State),
          electionSt e { leaderKey := k, leaderRev := W64 c, leaderSession := s, hdr := hd } ∗
          etcdLb γ σ ∗ etcdLb γ σv ∗ respHeaderOwn hd DFrac.discard hm ∗
          ⌜waitedFor pfx k c σ ∧ (c : Int) ≤ sint.Z hm.revision ∧ sint.Z hm.revision ≤ σ.kv.rev ∧
            ∃ r, σv.kv.store k = some r ∧ r.createRev = c ∧ r.value = val⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ st' : ElectionSt, electionSt e st') }}

end spec

end Concurrency
end EtcdGrove
end Perennial
