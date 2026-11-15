/-
## `leasehttp.RenewHTTP(ctx, id, url, rt)` (`http.go`): trusted (names only)

**Users.** 2c's `EtcdServer.LeaseRenew` on a follower (the keep-alive forwarded to the leader's
`/leases` endpoint over the peers' round tripper). embed's server side (`NewHandler`, mounted by
`etcdhttp.NewPeerHandler`) is out of scope: this repository's starters serve only the raft handler,
so a forwarded keep-alive gets a `404`, which the error disjunct covers.

**Why it is true.** An HTTP POST of the encoded `LeaseKeepAliveRequest` with the context, the
response decoded: no panic for any `id`, `url` (a bad URL is an error) or context. The TTL it
returns says nothing of the lease in W0's model. **Its errors** (`http.go:166-218`): exactly
`lease.ErrLeaseNotFound` (the value of the global: `return -1, lease.ErrLeaseNotFound`) on a `404`;
otherwise `proto.Marshal`'s or `http.NewRequest`'s error, `cc.Do`'s `*url.Error` (wrapping the
round tripper's or the context's error), `readResponse`'s, `ErrLeaseHTTPTimeout` (another
`errors.New` value), a `fmt.Errorf` without `%w`, or `fmt.Errorf("lease: %w ...")` of
`proto.Unmarshal`'s error: none of them is, or wraps, the lessor's sentinel (the round tripper,
`net/http`'s transport over rafthttp's, never returns it), and each one's `Is`/`Unwrap` methods are
the standard library's and protobuf's (no panic), so `errors.Is(err, lease.ErrLeaseNotFound)` is
safe and `false` (`errIsNot`).

**Changes** (from `specs-ref`'s `RenewHTTP.lean`): unchanged in substance; the round tripper's
contract is `net/http`'s `Http.roundTripperOk` (`rtOk`, no longer provisional: integration I5).
Verify round (A9 3c F9): the post says what the caller inspects: `nil`, the lessor's
`ErrLeaseNotFound` (the global's value, `Lease.errIs`), or an error on which `errors.Is` with that
value is safe and `false` (`errIsNot`); it said nothing of the error.
**Margin.** The TTL; the other errors' kinds.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.leasehttp.Api

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

/-- **Forwards a keep-alive to the leader**: some TTL and `nil`, the lessor's `ErrLeaseNotFound`
(the leader's `404`), or another error, which is not (and wraps nothing that is)
`ErrLeaseNotFound`. -/
def RenewHTTP.spec : Prop :=
  ∀ (ctx : GoInterface) (id : w64) (url : GoString) (rt : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp ∗ Context.ctxOk ctx ∗ rtOk rt ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.leasehttp.RenewHTTP)) (Val #ctx)) (Val #id)) (Val #url)) (Val #rt))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); threadTok ∗
      (⌜err = GoInterface.nil⌝ ∨
       Lease.errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∨
       ∃ t, Lease.errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound t ∗ errIsNot err t) }}

end spec

end Leasehttp
end EtcdGrove
end Perennial
