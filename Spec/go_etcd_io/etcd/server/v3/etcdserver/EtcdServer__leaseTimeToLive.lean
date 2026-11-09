/-
## `(*EtcdServer).leaseTimeToLive(ctx, r)` (internal helper; untranslated, an assumed contract)

Users: `LeaseTimeToLive` (`v3_server.go:713`). The code: on the leader, `waitAppliedIndex`, the
lessor's `Lookup` (3c: a lease of the member's lease table, its remaining TTL, granted TTL and keys),
`ErrLeaseNotFound`, `ErrLeaderChanged` if the lessor was demoted meanwhile; else forwarded to the
leader (`waitLeader`, `leasehttp.TimeToLiveHTTP`: the leader's answer, 3c's boundary), `ErrTimeout`/
`ErrCanceled` at the context's end. **Assumes** the leader's peer URLs are etcd members' (the
forwarding path panics on a malformed peer reply: `issues/etcd-leasehttp-timetolive-nil-{response,
header}-panic.md`). Changes: round 1, the answer is justified at a state `σ₁` the answering lessor
reflects, at or after the caller's bound `σ₀` (and at every state after `σ₁`: the lease tables and
the history are kept), not at `σ₀` itself (provability F4). Margin: the TTLs; the key set (W0's
mismatch: `le.Keys()` may see a transaction's attachments half done, `req/`).

Changes: verify-round (A6-provability F1): the success reply has its header set (`srvHdrReply`, `replyHdrOwn`: the apply's `newHeader()`, `s.newHeader()`, `ResponseHeader{}`, or the leader's through `leasehttp`, whose decoded reply must carry one: requested of lease-auth), so the gRPC handler's `hdr.fill(resp.Header)` cannot panic.

Changes: verify-round, second pass (lease-auth's request): the forwarding path gets the reply from `TimeToLiveHTTP`'s `ltlReply` through `ltlReply_replyHdr` (header set: `srvHdrReply`); its premise `leasePeerURL (url ++ LeaseInternalPrefix)` for each of the leader's peer URLs is the trusted deployment premise, taken here from the membership view's member (every member's peer URL set was reserved by `cluster_alloc`/`urls_reserve`, whose hosts serve etcd's peer handler): requested of lease-auth as a law relating it to the reserved addresses.
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

/-- An answer of W0's `leaseTimeToLive` step at a state `σ₁` the cluster reached at or after
the caller's bound `σ₀`, and at every state after it, or an unsettled error. The caller fires its
update at the return. -/
def EtcdServer.leaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p : Principal) (r : Loc) (dq : DFrac)
    (id : Int) (keys : Bool) (σ₀ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ threadTok ∗ etcdLb γ σ₀ ∗
      ClientV3.reqOwn r dq (.leaseTimeToLive id keys) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"leaseTimeToLive")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ClientV3.reqOwn r dq (.leaseTimeToLive id keys) ∗
      ((∃ res σ₁, etcdLb γ σ₁ ∗
          ⌜Reach σ₀ σ₁ ∧ ∀ σ, Reach σ₁ σ → Step p (.leaseTimeToLive id keys) σ σ res⌝ ∗
          srvReply srvHdrReply res resp err) ∨
       (⌜resp = null⌝ ∗ srvIndef err ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
