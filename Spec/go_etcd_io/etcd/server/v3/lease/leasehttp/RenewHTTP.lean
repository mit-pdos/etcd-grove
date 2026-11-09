/-
## `leasehttp.RenewHTTP(ctx, id, url, rt)` (`http.go`): trusted (names only)

**Users.** 2c's `EtcdServer.LeaseRenew` on a follower (the keep-alive forwarded to the leader's
`/leases` endpoint over the peers' round tripper). embed's server side (`NewHandler`, mounted by
`etcdhttp.NewPeerHandler`) is out of scope: this repository's starters serve only the raft handler,
so a forwarded keep-alive gets a `404`, which the error disjunct covers.

**Why it is true.** An HTTP POST of the encoded `LeaseKeepAliveRequest` with the context, the
response decoded (`ErrLeaseNotFound` on 404, other errors returned): no panic for any `id`, `url`
(a bad URL is an error) or context. The TTL it returns says nothing of the lease in W0's model.

**Changes** (from `specs-ref`'s `RenewHTTP.lean`): unchanged in substance; the round tripper's
contract is `net/http`'s `Http.roundTripperOk` (`rtOk`, no longer provisional: integration I5). **Margin.** The TTL.
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

/-- **Forwards a keep-alive to the leader** (some TTL, or an error). -/
def RenewHTTP.spec : Prop :=
  ∀ (ctx : GoInterface) (id : w64) (url : GoString) (rt : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp ∗ Context.ctxOk ctx ∗ rtOk rt ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.leasehttp.RenewHTTP)) (Val #ctx)) (Val #id)) (Val #url)) (Val #rt))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); threadTok }}

end spec

end Leasehttp
end EtcdGrove
end Perennial
