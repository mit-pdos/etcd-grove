/-
## `(*EtcdServer).LeaseLeases(ctx, r)`

**Users.** The gRPC lease handler (`api/v3rpc/lease.go:79`). Snippet:
`examples/specreq/etcdserverreq/lease.go` (`ReqLeases`).

**Proof sketch.** `s.lessor.Leases()` (3c: the leases of the lessor at the member's applied point,
each in W0's `granted`, distinct ids); `checkLeaseLeases` (`checkLeaseLeases.spec`: a denial of a
key's read permission is `permErr`; a changed auth revision `ErrAuthOldRevision`, a refusal); the
statuses' slice; `newHeader()` (`newHeader.spec`). Fired at the return (W0's `leaseLeases` step:
any granted ids, at any later state).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__LeaseLeases.lean`) restated over W0's step,
the header's ids inside the answer (`lease-grpc.md`'s lesson: no server ids in the statement).

**Margin.** The ids are the member's applied ones, live there; W0's model says only granted.

Changes: verify-round (A6-provability F1): the success reply has its header set (`srvHdrReply`, `replyHdrOwn`: the apply's `newHeader()`, `s.newHeader()`, `ResponseHeader{}`, or the leader's through `leasehttp`, whose decoded reply must carry one: requested of lease-auth), so the gRPC handler's `hdr.fill(resp.Header)` cannot panic.

Changes: recheck RR-1 (client-core's request 2): over `SrvCallTripleF` with `srvLeaseFact`, at the endpoint `ep` the member serves (`srvAt s γ ep`) and the caller's optional bound `leaseViewLb γ ep i` (`srvLeaseLbOpt`): the ids are read from the member's own lessor (`s.lessor.Leases()`, `v3_server.go:737`, no forwarding), at a table `j ≥ i` (the lessor only moves forward), so the answer is `leaseAnsAt j` and gives `leaseViewLb γ ep j`; a `checkLeaseLeases` refusal is not `leaseAnsRes`.
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

/-- **`s.LeaseLeases(ctx, r)`**: the ids of the leases the member's lessor holds (each granted at some point); the update fired at the return. -/
def EtcdServer.LeaseLeases.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ep : GoString) (vi : Option Nat) (q : Qp) (ctx : GoInterface)
    (p tls : Principal) (r : Loc) (dq : DFrac),
  SrvCallTripleF (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"LeaseLeases")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvAt s γ ep ∗ srvLeaseLbOpt γ ep vi ∗ srvGate s q ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ ClientV3.reqOwn r dq .leaseLeases)
    iprop(srvGate s q ∗ threadTok ∗ ClientV3.reqOwn r dq .leaseLeases) γ p tls (.leaseLeases) false srvHdrReply
    (srvLeaseFact γ ep .leaseLeases vi)

end spec
end EtcdServer
end EtcdGrove
end Perennial
