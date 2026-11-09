/-
## `(*EtcdServer).LeaseRenew(ctx, id)`

**Users.** The gRPC lease handler's keep-alive loop (`api/v3rpc/lease.go:136`: one call per
keep-alive request on the stream, the stream's context), the lease HTTP handler (on the leader, for
forwarded renewals). Snippet: `examples/specreq/etcdserverreq/lease.go` (`ReqKeepAlive`).

**Proof sketch.** On the leader (`isLeader`, `ensureLeadership`: 2d's, any answer;
`lease.ErrNotPrimary`: unmapped, outcome 3): the feature gate, `lessor.Lookup` (3c),
`waitAppliedIndex` (its errors: outcome 3), `checkLeaseRenew` (`checkLeaseRenew.spec`: an invalid
token or a stale auth revision, outcome 2; a missing principal, `ErrUserEmpty`, outcome 2; a denied
put permission of the lease's keys, fired: `srvStep`'s keep-alive denial), `lessor.Renew(id)` (3c:
a TTL, `ErrLeaseNotFound`, `ErrNotPrimary`). Else (or on `ErrNotPrimary`) the forwarding loop:
`context.WithTimeout`, `waitLeader` (`waitLeader.spec`), `checkLeaseRenew`, `leasehttp.RenewHTTP`
to each of the leader's peer URLs (3c's boundary: a TTL, `ErrLeaseNotFound`, other errors retried),
`time.Sleep`; the context's end: `ErrTimeout` or `ErrCanceled` (outcome 3). The permission
denial is W0's `leaseKeepAlive` step's (round 1: no `srvStep` disjunct of its own). Every answer the code
returns is fired at the return (W0's `leaseKeepAlive`: any TTL or `ErrLeaseNotFound`, at any state:
a keep-alive tells nothing of the lease's liveness).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__LeaseRenew.lean`, the lease-renew plan's
contract) restated over W0's step and the three outcomes.

**Margin.** The TTL is the leader's lessor's (any `int64`); the model has no time.

Changes: verify-round (lease-auth's request): on the leader, `lessor.Renew` takes the caller's
`threadTok` (given back); on the forwarding path, `leasehttp.RenewHTTP`'s post: `Lease.errIs
ErrLeaseNotFound` for that error (returned: `leaseErr_srv` makes it the sentinel of
`.leaseNotFound`), `errIsNot` for the others (their `errors.Is` is false: the loop goes on). Snippet
`etcdserverreq/lease.go` `ReqKeepAliveFollower`. Errors by `srvErr` (the sentinel encoding).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A keep-alive of lease `id`**: its TTL, or an error; the update fired at the return
(outcome 1), given back (outcome 2) or lost (outcome 3). -/
def EtcdServer.LeaseRenew.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (p tls : Principal) (lo : Nat) (id : w64)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗ Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ authLb γ lo ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls (.leaseKeepAlive (sint.Z id)) σ σ' res lo⌝ ∗
             etcdState γ σ', COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"LeaseRenew")) (Val #ctx)) (Val #id))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); srvGate s q ∗ threadTok ∗
      ((∃ σ σ' res, ⌜srvFiredAns res⌝ ∗ Q σ σ' res ∗
          match res with
          | .ok (.leaseKeepAlive _ t) => iprop(⌜err = GoInterface.nil ∧ ttl = W64 t⌝)
          | .err e => iprop(srvErr err e ∗ srvErrShape err)
          | _ => iprop(False)) ∨
       (srvUnfired err ∗ srvErrShape err ∗
          AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls (.leaseKeepAlive (sint.Z id)) σ σ' res lo⌝ ∗
                 etcdState γ σ', COMM Q σ σ' res }>) ∨
       (srvIndef err ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
