/-
## `leasehttp.RenewHTTP(ctx, id, url, rt)` (`http.go`): trusted (names only)

**Users.** 2c's `EtcdServer.LeaseRenew` on a follower (the keep-alive forwarded to the leader's
`/leases` endpoint over the peers' round tripper).

**Why it is true.** An HTTP POST of the encoded `LeaseKeepAliveRequest` with the context, the
response decoded (`ErrLeaseNotFound` on 404, other errors returned): no panic for any `id`, `url`
(a bad URL is an error) or context. The TTL it returns says nothing of the lease in W0's model (a
keep-alive guarantees nothing: `Model.lean`'s header), so the post states nothing of it.

**Changes** (from `specs-ref`'s `RenewHTTP.lean`): unchanged in substance; the round tripper's
contract provisional (`rtOk`, the `net/http` boundary: 2a's/2f's). **Margin.** The TTL.
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
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp ∗ Context.ctxOk ctx ∗ rtOk rt }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.leasehttp.RenewHTTP)) (Val #ctx)) (Val #id)) (Val #url)) (Val #rt))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); True }}

end spec

end Leasehttp
end EtcdGrove
end Perennial
