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

**Changes.** New (second pass, server-core's request): the old tree had no spec (2c's
`leaseTimeToLive` was names-only).
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
its header set), the lessor's `ErrLeaseNotFound`, or another error. -/
def TimeToLiveHTTP.spec : Prop :=
  ∀ (ctx : GoInterface) (id : w64) (keys : Bool) (url : GoString) (rt : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp ∗
      Context.ctxOk ctx ∗ rtOk rt ∗ threadTok ∗ ⌜leasePeerURL url⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.leasehttp.TimeToLiveHTTP))
      (Val #ctx)) (Val #id)) (Val #keys)) (Val #url)) (Val #rt))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ c : Proto.Content,
          Proto.msgAt go_etcd_io.etcd.server.v3.lease.leasepb.LeaseInternalResponse.ty resp
            (DFrac.own 1) c ∗ ⌜Proto.norm c = c ∧ ltlReply c (sint.Z id)⌝) ∨
       (⌜resp = null⌝ ∗ Lease.errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err) ∨
       (⌜resp = null⌝ ∗ ∃ t, Lease.errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound t ∗
          errIsNot err t)) }}

end spec

end Leasehttp
end EtcdGrove
end Perennial
