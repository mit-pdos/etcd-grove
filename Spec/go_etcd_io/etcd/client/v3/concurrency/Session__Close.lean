/-
`(*concurrency.Session).Close` (`client/v3/concurrency/session.go`).

Users: `server/etcdserver/api/v3lock/lock.go:36` and `v3election/election.go:126` (`WithLease(req.Lease)`,
`WithContext(ctx)`, then `Orphan()`: a session over a lease the remote client holds, never
refreshed by the server; `Leader`/`Observe` pass lease `-1`; a session per RPC), `client/leasing/kv.go:147` (a
session per monitor round, in a loop, its `Done()` awaited), `server/proxy/grpcproxy/register.go:65`
(`WithTTL`, its lease on an endpoint key, `Close()` on error or shutdown, a new session per expiry), recipes
(`key.go:142`, `rwmutex.go:69`, `double_barrier.go:47`: `Client()` and `Lease()`), etcd's tests
(`tests/integration/clientv3/concurrency/session_test.go`). Snippet: `concurrency/session.go` (`ReqSessionClose`, `ReqSessionLoop`).

Proof sketch: `Session.Orphan.spec`; `Context.WithTimeout.spec` over the options' context (held by
`isSession`, with its principal: `ctxPrin_child`); the `Lease` field's `Revoke(ctx, id)` (1c's
`Lease.methods`: a repeatable call, so a persistent update built from `etcdPerm γ T`: a revoke's
step is `revokeEff`, an error or a refusal no change; `etcdLb_reach` inside it gives `Reach σ0`):
`nil` with `etcdLb` of the state after (the lease gone), or its error; the cancel function.

Changes: from `specs-ref`'s `Session__Close.lean` (an unfinished proof, post `sessionDone`): the
revoke's outcome stated (the lease gone at a state the cluster reached after `σ0`), its effect
through `etcdPerm`.

Margin: `ErrLeaseNotFound` also means the lease is gone (at the state it was answered); folded
into the error case.
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

/-- `s.Close()`: orphans the session and revokes its lease: `nil` and the lease gone at a state the cluster reached after `σ0`, or an error. -/
def Session.Close.spec : Prop :=
  ∀ (s c : Loc) (γ : Cluster) (id : w64) (T : State → State → Prop) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s c γ id ∗ etcdLb γ σ0 ∗ etcdPerm γ T ∗ ⌜effIn (revokeEff (sint.Z id)) T⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Session.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : State, etcdLb γ σ ∗ ⌜Reach σ0 σ ∧ σ.leases (sint.Z id) = none⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Concurrency
end EtcdGrove
end Perennial
