/-
## `leasehttp.TimeToLiveHTTP(ctx, id, keys, url, rt)` (`http.go:224`): trusted (names only)

**Users.** 2c's `EtcdServer.leaseTimeToLive` on a follower (`v3_server.go`, the forwarded
`LeaseTimeToLive`: the leader's peer URLs, `s.peerRt`), whose success reply must carry a header
(`srvHdrReply`: the gRPC handler's `hdr.fill(resp.LeaseTimeToLiveResponse.Header)`, A6-provability
F1).

**Why it is true** (`http.go:224-282`). An HTTP POST of the encoded `LeaseInternalRequest` with the
context; `408`: `ErrLeaseHTTPTimeout`; `404`: `lease.ErrLeaseNotFound` (the global's value);
another status: a `fmt.Errorf` error; a `200` body unmarshalled into a fresh
`*leasepb.LeaseInternalResponse` (an error: a wrapped one), then `lresp.LeaseTimeToLiveResponse.ID`
compared with `id` (mismatch: an error). The leader's handler (`http.go:108-140`) encodes
`LeaseInternalResponse{LeaseTimeToLiveResponse: {Header: &ResponseHeader{}, ID, TTL, GrantedTTL,
Keys}}`, so under `leasePeerURL url` a `200` body decodes to a content with the inner message and
its header set (`ltlReply`; canonical, `Proto.norm c = c`, as `proto.Unmarshal`'s), and the `.ID`
read does not dereference `nil`. Without the premise a peer's malformed `200` reply panics there
(`issues/etcd-leasehttp-timetolive-nil-response-panic.md`), which is why it is a premise. No panic
otherwise, for any `id`, `url` or context.

**The premise `leasePeerURL url` is a deployment premise** (not derivable here). Its caller passes
`u ++ LeaseInternalPrefix` for each peer URL `u` of the leader in its membership view. What the
cluster's vocabulary knows of a peer address (rafthttp's `peerAddr ν a`: `Http.protoAt a P` with
`raftCompat ν P`) fixes `P` only under `/raft` and *allows* the mux's `404`/`301` elsewhere. It does
not exclude a `200` with another body on `/leases/internal`, which is exactly what the premise
rules out. It is true of every etcd member: embed's peer handler serves `NewHandler`'s encoding,
and this repository's starters serve only rafthttp's mux, which answers `404`. Carried by
`EtcdServer.leaseTimeToLive.spec` (2c's assumed contract: "the leader's peer URLs are etcd
members'"), hence by the server's top-level specs that reach the forwarded `LeaseTimeToLive`. A law
deriving it would need the peer port's protocol to fix the lease path too: requested of
server-boot (`raftCompat`, or a `leaseCompat` beside it, in the report).

**The handler's view** (`ltlView γ ep vi url id found`, on the `200` and the `404` replies). The
caller names the member `ep` it expects and its view bound `vi` of that member, held at the call
(`leaseLbOpt γ ep vi`: `leaseViewLb γ ep i`, or nothing). The handler waits for its server's
`ApplyWait` (`h.waitch()`, `http.go:115-120`), then looks the lease up in its lessor (`:124`): `404`
if absent, else a `200` (or `500` if demoted: another error). So the answer is the lessor's table at
the moment of the lookup, after the call began, hence at or past the view `i` the caller held. Stated
per member through `leaseURLOf` (the URL is `ep`'s member's handler), which the caller may show
later (a run-wide fact): a caller that cannot show it gets nothing from it.

**Changes.** New (second pass, server-core's request): the old tree had no spec (2c's
`leaseTimeToLive` was names-only).
Changes: verify-round (server-core's RR request 2): the success and `ErrLeaseNotFound` replies also
give `ltlView url (sint.Z id) found` (found: `true`, `false`), the serving member's lessor view,
which 2c's `leaseTimeToLive` needs for `srvLeaseFact`'s gated row (under `soleMember`, the leader's
URL is the member's own: `leaseURLOf`).
Changes: verify-round F3 (`verify/F-client-api.md`: unsound): the view bound is the caller's,
held before the call (binders `γ ep vi`, the precondition `leaseLbOpt γ ep vi`), not quantified in
the post's persistent wand, which accepted a view obtained after the answer (a `404`, then a grant
of `id` with its `leaseViewLb γ ep jg`: the wand gave a table `j ≥ jg` without `id`, contradicting
the grant; `False`). The pre's other parts and the outcomes are unchanged.
**Margin.** The TTLs and keys (any); the other errors' kinds.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.leasehttp.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasehttp

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.leasehttp.Assumptions]

/-- **Asks the leader for lease `id`'s TTL**: the decoded reply (owned, canonical, of lease `id`,
its header set), the lessor's `ErrLeaseNotFound`, or another error; the first two with the
handler's view of `ep`'s member from the caller's bound `vi` (`ltlView`). -/
def TimeToLiveHTTP.spec : Prop :=
  ∀ (ctx : GoInterface) (id : w64) (keys : Bool) (url : GoString) (rt : GoInterface)
    (γ : EtcdModel.Cluster) (ep : GoString) (vi : Option Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp ∗
      Context.ctxOk ctx ∗ rtOk rt ∗ threadTok ∗ ⌜leasePeerURL url⌝ ∗ leaseLbOpt γ ep vi }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.leasehttp.TimeToLiveHTTP))
      (Val #ctx)) (Val #id)) (Val #keys)) (Val #url)) (Val #rt))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ c : Proto.Content,
          Proto.msgAt go_etcd_io.etcd.server.v3.lease.leasepb.LeaseInternalResponse.ty resp
            (DFrac.own 1) c ∗ ⌜Proto.norm c = c ∧ ltlReply c (sint.Z id)⌝ ∗ ltlView γ ep vi url (sint.Z id) true) ∨
       (⌜resp = null⌝ ∗ Lease.errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗
          ltlView γ ep vi url (sint.Z id) false) ∨
       (⌜resp = null⌝ ∗ ∃ t, Lease.errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound t ∗
          errIsNot err t)) }}

end spec

end Leasehttp
end EtcdGrove
end Perennial
