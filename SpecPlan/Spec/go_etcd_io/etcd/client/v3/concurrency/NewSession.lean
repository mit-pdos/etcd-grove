/-
`concurrency.NewSession(client, opts...)` (`client/v3/concurrency/session.go`).

Users: `server/etcdserver/api/v3lock/lock.go:36` and `v3election/election.go:126` (`WithLease(req.Lease)`,
`WithContext(ctx)`, then `Orphan()`: a session over a lease the remote client holds, never
refreshed by the server; `Leader`/`Observe` pass lease `-1`; a session per RPC), `client/leasing/kv.go:147` (a
session per monitor round, in a loop, its `Done()` awaited), `server/proxy/grpcproxy/register.go:65`
(`WithTTL`, its lease on an endpoint key, `Close()` on error or shutdown, a new session per expiry), recipes
(`key.go:142`, `rwmutex.go:69`, `double_barrier.go:47`: `Client()` and `Lease()`), etcd's tests
(`tests/integration/clientv3/concurrency/session_test.go`). Snippets: `concurrency/session.go` (`ReqSessionLease`, `ReqSessionResumeLease`,
`ReqSessionDone`, `ReqSessionTTL`, `ReqSessionLoop`).

Proof sketch: `Client.GetLogger.spec`, `Client.Ctx.spec` (1c, over `clientBase c dflt`, from
`clientRest` by `clientRest_core`, `clientCore_pre`, `clientPre_base`: `isLogger`; the client's
context, `ctxOk` and `ctxPrin dflt ctx dflt`); `sessOptAt_call` per option (the options' struct, a fresh allocation); if the options
name no lease, the `Lease` field's `Grant(ctx, ttl)` (`clientRest_fields`' `leaseAt`, 1c's
`Lease.methods`: a repeatable call, so a persistent update, built from `etcdPerm γ T`: a grant's
step is `grantEff`, a refusal or an error no change; `etcdLb_reach` inside it orders the state after
`σ0`): the reply's `ID` with `etcdLb` of the state after (the lease live there), or its error
returned. `Context.WithCancel.spec` and `ctxPrin_child` over the options' context; `KeepAlive(ctx,
id)` (1c: a non-nil channel, `kaChan`; no thread token); on error the cancel function (`cancelOk`)
and the error returned. Otherwise a fresh `donec` (`alloc_broadcast_chan`, `Q := True`), the
`Session` (its fields persisted: `isSession`, which keeps the options' context and its principal for
`Close`), and the keep-alive goroutine (`wp_fork`: Perennial's fork takes no token from the caller):
it receives (`kaChan_recv`) until the keep-alive channel is closed, then closes `donec`
(`wp_broadcast_chan_close`) and cancels.

Changes: from `specs-ref`'s `NewSession.lean`: a client of any cluster state (`isClient`, not the
old `isEtcdSessionClient`), any context (`ctxOk`, not only a cancelable Perennial one); the lease
granted is stated as a model fact (`etcdLb` of a state after the caller's `σ0` where it is live)
instead of the old `sessionLeaseOk`; the grant's effect through W0's `etcdPerm` (persistent: the
grant is retried with the repeatable policy, so it may apply more than once); `isSession` names the
client. Round 1: no thread token; the client named; `σ0`. Integration (I1): over W0's `clientRest` (was `isClient`, which
gives it by `isClient_rest`): the gRPC proxy's leasing KV makes sessions after overwriting
`client.KV` (`req/go_etcd_io_etcd_client_v3_concurrency.md`, "from 1e (round 1)"); `NewSession`
never reads `KV`.

Changes: re-review N1: a granted lease also comes with the grant's pre-state `σg` (after `σ0`, the id absent there: `grantEff`'s `σ.leases id = none`; the server refuses a collision with `ErrLeaseExist`), so two sessions granted one after the other while the first lease lives have distinct leases (`ReqMutexNoTwoHolders`, `ReqElectionNoTwoLeaders`).

Margin: the code also guarantees the lease's TTL is the one granted (at least the options'); not
stated. Nothing about the lease's liveness after the grant: time is not modelled.
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

/-- `NewSession(c, opts...)`: a session over the client `c`, with the lease the options name
(`WithLease`), or one granted then (live at a state the cluster reached after `σ0`); or `nil` and an
error. The options' context (the client's if none) must be a context of the principal `who`. -/
def NewSession.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (dflt who : Principal) (sl : GoSlice) (gs : List (SessOpts → SessOpts))
    (T : State → State → Prop) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ clientRest c γ dflt ∗ sessOptsAt sl gs ∗
      optCtxOk (applySessOptsM gs SessOpts.init).ctx dflt who ∗ etcdLb γ σ0 ∗ etcdPerm γ T ∗
      ⌜effIn (fun σ σ' => readEff σ σ' ∨ ((applySessOptsM gs SessOpts.init).leaseID = W64 0 ∧
          grantEff (sint.Z (applySessOptsM gs SessOpts.init).ttl) σ σ')) T⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewSession)) (Val #c)) (Val #sl))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err); sessOptsAt sl gs ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ id : w64, isSession s c γ id ∗
          (if (applySessOptsM gs SessOpts.init).leaseID = W64 0 then
             iprop(∃ σg σ : State, etcdLb γ σg ∗ etcdLb γ σ ∗
               ⌜Reach σ0 σg ∧ σg.leases (sint.Z id) = none ∧ Reach σg σ ∧
                σ.leases (sint.Z id) ≠ none⌝)
           else iprop(⌜id = (applySessOptsM gs SessOpts.init).leaseID⌝))) ∨
       ⌜s = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
