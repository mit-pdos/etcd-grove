/-
## `(*EtcdServer).LeaseTimeToLive(ctx, r)`

**Users.** The gRPC lease handler (`api/v3rpc/lease.go:63`), the grpc-proxy. Snippet:
`examples/specreq/etcdserverreq/lease.go` (`ReqTimeToLive`).

**Proof sketch.** `requireAuthInfo` (a refusal given back); with `keys`, `checkLeaseTimeToLive`
(`checkLeaseTimeToLive.spec`: the auth revision read first, then the principal's read permission of
the lease's keys at the auth store's state, a denial `permErr`; an invalid token a refusal);
`leaseTimeToLive(ctx, r)` (`leaseTimeToLive.spec`, untranslated: the leader's lessor after
`waitAppliedIndex`, or the leader's over `leasehttp`): a lease granted at some point (W0's
`granted` only grows) with keys attached at some revision the member applied, or `ErrLeaseNotFound`
(always a `Step` answer), or an unsettled error (`ErrLeaderChanged`, timeouts, `ErrStopped`); with
`keys`, the auth revision compared again (a change: `ErrAuthOldRevision`, a refusal). The update is
fired at the return, at the cluster's current state (every answer is one `leaseStep` allows at any
later state: `granted` and the history only grow).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__LeaseTimeToLive.lean`, the lease-read plan's
`raftLeaseRead` contract, `lease-grpc.md`) restated over W0's loose `leaseTimeToLive` step: a
one-shot update fired at the return.

**Margin.** The TTLs are any (W0's model has no time); a permission denial is fired with the
member's auth state, which W0's step allows at any state.

Changes: verify-round (A6-provability F1): the success reply has its header set (`srvHdrReply`, `replyHdrOwn`: the apply's `newHeader()`, `s.newHeader()`, `ResponseHeader{}`, or the leader's through `leasehttp`, whose decoded reply must carry one: requested of lease-auth), so the gRPC handler's `hdr.fill(resp.Header)` cannot panic.

Changes: recheck RR-1 (client-core's request 2): over `SrvCallTripleF` with `srvLeaseFact`, at the endpoint `ep` the member serves (`srvAt s γ ep`) and the caller's optional bound (`srvLeaseLbOpt`): the answer's row is gated on W0's `soleMember γ`. Under it this member is the cluster's only voter: as leader it answers from its own lessor after `waitAppliedIndex` (`v3_server.go:636-669`), at a table `j ≥ i`; otherwise `waitLeader` returns itself and `leasehttp.TimeToLiveHTTP` reaches its own peer URLs, whose handler (`leasehttp/http.go:109-160`, 4b's `leasehttp` spec over the same lessor: requested of lease-auth, a per-member view in its contract) looks the lease up in the same lessor, again at `j ≥ i`. `Demoted` (`ErrLeaderChanged`), timeouts and the HTTP errors are not `leaseAnsRes`. Without `soleMember` the answer may be another member's lessor's: no row.

Changes: verify-round (repair3-boot: the relay's server-core request): the sketch's source of the row is `leaseTimeToLive.spec`'s new post at `srvAt s γ ep` and `srvLeaseLbOpt γ ep vi` (passed through): its `soleMember γ -∗ ∃ j σ₂, ⌜i ≤ j ∧ σ₂.leaseAnsAt j rq res⌝ ∗ etcdLb γ σ₂ ∗ leaseViewLb γ ep j`, taken to the firing state `σ` by `etcdLb_reach` (`Reach σ₂ σ` keeps `σ₂.leaseTables` as a prefix, so `σ.leaseAnsAt j rq res`); on the forwarding path that contract gets it from `TimeToLiveHTTP`'s `ltlView` with 2e's `leaseURLOf_intro` (`srvAt`'s `srvEp`). The `checkLeaseTimeToLive`/`ErrAuthOldRevision` refusals are not `leaseAnsRes`. The row rests on that contract's deployment premise (`leasePeerURL` of the member's peer URLs), which `examples/lib/etcdstart` does not meet (see the contract).

Changes: verify-round F1 (`verify/F-client-api.md`): the row (here, `srvLeaseFact`'s and the
contract's) is gated on `soleMember γ ∗ peerLeaseServed γ`, the latter W0's deployment fact that
every member's peer URLs serve its lease handler (2e's `peerLeaseServed_intro`, under `leasePeerURL`
of the sole member's peer URLs), so the contract's row is true of every starter; the sketch passes
the gate through. Statement otherwise unchanged.
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

/-- **`s.LeaseTimeToLive(ctx, r)`**: lease `id`'s remaining and granted TTL (and its keys), from the leader's lessor (forwarded if this member is not the leader); the update fired at the return. -/
def EtcdServer.LeaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ep : GoString) (vi : Option Nat) (q : Qp) (ctx : GoInterface)
    (p tls : Principal) (r : Loc) (dq : DFrac) (id : Int) (keys : Bool),
  SrvCallTripleF (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"LeaseTimeToLive")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvAt s γ ep ∗ srvLeaseLbOpt γ ep vi ∗ srvGate s q ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ ClientV3.reqOwn r dq (.leaseTimeToLive id keys))
    iprop(srvGate s q ∗ threadTok ∗ ClientV3.reqOwn r dq (.leaseTimeToLive id keys)) γ p tls (.leaseTimeToLive id keys) false srvHdrReply
    (srvLeaseFact γ ep (.leaseTimeToLive id keys) vi)

end spec
end EtcdServer
end EtcdGrove
end Perennial
