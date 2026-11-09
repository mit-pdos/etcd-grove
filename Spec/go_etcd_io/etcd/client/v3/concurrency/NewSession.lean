/-
`concurrency.NewSession(client, opts...)` (`client/v3/concurrency/session.go`).

Users: `server/etcdserver/api/v3lock/lock.go:36` and `v3election/election.go:126` (`WithLease(req.Lease)`,
`WithContext(ctx)`, then `Orphan()`: a session over a lease the remote client holds, never
refreshed by the server; `Leader`/`Observe` pass lease `-1`), `client/leasing/kv.go:147` (a
session per monitor round, its `Done()` awaited), `server/proxy/grpcproxy/register.go:65`
(`WithTTL`, its lease on an endpoint key, `Close()` on error or shutdown), recipes
(`key.go:142`, `rwmutex.go:69`, `double_barrier.go:47`: `Client()` and `Lease()`), etcd's tests
(`tests/integration/clientv3/concurrency/session_test.go`). Snippets: `concurrency/session.go` (`ReqSessionLease`, `ReqSessionResumeLease`,
`ReqSessionDone`, `ReqSessionTTL`).

Proof sketch: `Client.GetLogger.spec`, `Client.Ctx.spec` (1c: `isLogger`, `ctxOk`, `ctxPrin`);
`sessOptAt_call` per option (the options' struct, a fresh allocation); if the options name no
lease, the `Lease` field's `Grant(ctx, ttl)` (`isClient_fields`' `leaseAt`, 1c's grant triple):
its update built from `etcdPerm γ T` (a grant's step is `grantEff`, a refusal or an error no
change), the reply's `ID` with `etcdLb` of the state after (the lease live there), or its error
returned. `Context.WithCancel.spec` over the options' context; `ctxPrin_child`; `KeepAlive(ctx, id)`
(1c's `Lease.methods`: a non-nil channel, `kaChan`, whatever the error; no thread token: the
lessor's goroutines are its own); on error the cancel function
(`cancelOk`) and the error returned. Otherwise a fresh `donec` (`alloc_broadcast_chan`, `Q :=
True`), the `Session` (its fields persisted: `isSession`), and the keep-alive goroutine (`wp_fork`,
the `threadTok`): it receives (`kaChan_recv`) until the keep-alive channel is closed, then closes `donec`
(`wp_broadcast_chan_close`) and cancels.

Changes: from `specs-ref`'s `NewSession.lean`: a client of any cluster state (`isClient`, not the
old `isEtcdSessionClient`), any context (`ctxOk`, not only a cancelable Perennial one); the lease
granted is stated as a model fact (`etcdLb` of a state where it is live) instead of the old
`sessionLeaseOk`; the grant's effect through `etcdPerm`; a thread token for the keep-alive goroutine (the
old spec forked without one).

Margin: the code also guarantees the lease's TTL is the one granted (at least the options'); not
stated (no user reads it). Nothing about the lease's liveness after the grant: time is not
modelled (the lease may expire at once, `EnvStep.leaseExpire`).
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

/-- `NewSession(c, opts...)`: a session over the client, with the lease the options name
(`WithLease`), or one granted then (live at a state the cluster reached); or `nil` and an error.
The options' context (the client's if none) must be a context. -/
def NewSession.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (sl : GoSlice) (gs : List (SessOpts → SessOpts))
    (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isClient c γ who ∗ sessOptsAt sl gs ∗
      optCtxOk (applySessOptsM gs SessOpts.init).ctx who ∗
      etcdPerm γ T ∗
      ⌜effIn (fun σ σ' => readEff σ σ' ∨ ((applySessOptsM gs SessOpts.init).leaseID = W64 0 ∧
          grantEff (sint.Z (applySessOptsM gs SessOpts.init).ttl) σ σ')) T⌝ ∗
      threadTok }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewSession)) (Val #c)) (Val #sl))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err); sessOptsAt sl gs ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ id : w64, isSession s γ who id ∗
          (if (applySessOptsM gs SessOpts.init).leaseID = W64 0 then
             iprop(∃ σ : State, etcdLb γ σ ∗ ⌜σ.leases (sint.Z id) ≠ none⌝)
           else iprop(⌜id = (applySessOptsM gs SessOpts.init).leaseID⌝))) ∨
       ⌜s = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
