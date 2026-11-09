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

Changes: verify-round (repair3-boot: the relay's server-core request): at the endpoint `ep` the
member serves (`srvAt s γ ep`, 2e's) with the caller's optional bound (`srvLeaseLbOpt γ ep vi`), the
success outcome also gives `srvLeaseFact`'s `TimeToLive` row in the form the caller converts:
`soleMember γ -∗` an answer read from a table `j ≥ i` of a state `σ₂` the cluster reached
(`etcdLb γ σ₂`, `σ₂.leaseAnsAt j`), with the member's view of `j`. `LeaseTimeToLive` takes it to the
state its update fires at by `etcdLb_reach` (the lease tables are kept). **Why it is true** (under
`soleMember γ` the member `id` that `srvAt` binds `ep` to is the cluster's only voter, so its own
leader whenever there is one, and no `MemberUpdate` changes its URLs: none has a `urlsRight`):
- on the leader path, `waitAppliedIndex` then `s.lessor.Lookup(id)` reads member `id`'s lessor at
  its current table `j`, at or past every view `i` of that member (`srvAt`'s realization; the lessor
  only moves forward); `nil` is `ErrLeaseNotFound` (`t id = none`), a lease is the reply with
  `ID = r.ID` (`t id ≠ none`); `Demoted` is `ErrLeaderChanged`, not `leaseAnsRes`;
- on the forwarding path, `waitLeader` returns member `id` itself; for each `u ∈ leader.PeerURLs`
  (the membership view's record of `id`, a member of an applied state: `etcdLb`), 2e's
  `leaseURLOf_intro` (with `srvAt`'s `srvEp` and this contract's deployment premise
  `leasePeerURL (u ++ LeaseInternalPrefix)`) gives `leaseURLOf γ ep (u ++ …)`; `TimeToLiveHTTP`'s
  `ltlView` then gives `j ≥ i`, `σ₂ = σ₀`, the view of `j` and whether `id` is in table `j`: a `200`
  is `found` (`ltlReply`: `ID = id`), `ErrLeaseNotFound` (a `404`) is not found; another error is
  retried or is `ErrTimeout`/`ErrCanceled` (`srvIndef`).
**The deployment premise is not met by this repository's starters** (repair3-boot):
`examples/lib/etcdstart` serves only `s.RaftHandler()` on the peer address, so a forwarded request
gets a `404`, which `TimeToLiveHTTP` reports as `ErrLeaseNotFound`. A sole member restarted after a
stop (a new server object at the same `ep`, in the same generation) and asked before its first
election would answer `ErrLeaseNotFound` for a lease a client saw at `ep`: the row is false there.
The fix is the harness's (serve `s.LeaseHandler()` at `/leases` and `/leases/internal` beside the raft
handler, as `etcdhttp.newPeerHandler` does), with a spec of `LeaseHandler` that makes
`leasePeerURL` derivable (open questions 3.2, C24).

Changes: verify-round F1, F3 (`verify/F-client-api.md`). F1: the row was gated on `soleMember γ`
alone, so the trusted contract was false under `etcdstart` (the case above). It is now gated on
`soleMember γ ∗ peerLeaseServed γ` (W0: every member's peer URLs serve its own lessor's lease
handler; 2e's `peerLeaseServed_intro` gives it for a one-member cluster only under 4b's deployment
premise `leasePeerURL` of the member's peer URLs, which a starter meets by serving
`s.LeaseHandler()` on the peer address, as `etcdhttp.newPeerHandler` does). So the contract is true
of every starter: under `etcdstart` the gate cannot be met (no `leasePeerURL` there), and the base
outcome (`Step` at `σ₁`, `leaseStep`'s not-found admissible at table 0) holds. The forwarding
path's sketch now: from the gate, 2e's `peerLeaseServed_url` (at the leader's record in the
membership view, a member of an applied state, `srvAt`'s `srvEp`) gives `leaseURLOf γ ep (u ++ …)`
for each `u ∈ leader.PeerURLs`, and 4b's `leaseURLOf_peerURL` its `leasePeerURL`. F3:
`TimeToLiveHTTP` takes the caller's view bound: this contract passes its own `srvLeaseLbOpt γ ep vi`
(`Leasehttp.leaseLbOpt`, persistent, held from the call's start, so at every forwarding attempt),
and `ltlView γ ep vi` with that `leaseURLOf` gives `j ≥ i`, `σ₂ = σ₀`, the view of `j` and whether
`id` is in table `j`. The leader path is unchanged.
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
update at the return. With the caller's view bound `i` of `ep`'s member, and in a cluster that
never had another member (`soleMember γ`) and whose members' peer URLs serve their lessors' lease
handlers (`peerLeaseServed γ`), the answer was read from a table `j ≥ i` of that member's (see the
Changes above). -/
def EtcdServer.leaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ep : GoString) (vi : Option Nat) (ctx : GoInterface) (p : Principal)
    (r : Loc) (dq : DFrac) (id : Int) (keys : Bool) (σ₀ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvAt s γ ep ∗ srvLeaseLbOpt γ ep vi ∗ Context.ctxOk ctx ∗ threadTok ∗ etcdLb γ σ₀ ∗
      ClientV3.reqOwn r dq (.leaseTimeToLive id keys) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"leaseTimeToLive")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ClientV3.reqOwn r dq (.leaseTimeToLive id keys) ∗
      ((∃ res σ₁, etcdLb γ σ₁ ∗
          ⌜Reach σ₀ σ₁ ∧ ∀ σ, Reach σ₁ σ → Step p (.leaseTimeToLive id keys) σ σ res⌝ ∗
          (match vi with
           | some i => (iprop(⌜¬ ClientV3.leaseAnsRes res⌝ ∨
               (soleMember γ ∗ peerLeaseServed γ -∗ ∃ (j : Nat) (σ₂ : State),
                 ⌜i ≤ j ∧ σ₂.leaseAnsAt j (.leaseTimeToLive id keys) res⌝ ∗ etcdLb γ σ₂ ∗
                 leaseViewLb γ ep j)) : IProp GF)
           | none => iprop(True)) ∗
          srvReply srvHdrReply res resp err) ∨
       (⌜resp = null⌝ ∗ srvIndef err ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
