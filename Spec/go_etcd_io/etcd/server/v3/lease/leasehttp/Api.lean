/-
# `server/lease/leasehttp`: vocabulary (batch 2e)

The lease HTTP endpoints a follower forwards to the leader (`RenewHTTP`, `TimeToLiveHTTP`: the
latter's spec added in the second pass, for 2c's `leaseTimeToLive`). Trusted (names only).

* `rtOk rt` (persistent): `rt` is an `http.RoundTripper` that may be used from any goroutine
  (`rafthttp.NewRoundTripper`'s, the server's `peerRt`). Integration (I5): no longer provisional:
  it is the `net/http` boundary's `Http.roundTripperOk rt` (`Spec/net/http/Api.lean`), which
  `rafthttp.NewRoundTripper.spec` gives (the name kept as an abbreviation).
* `errIsNot err t` (transparent; verify round, A9 3c F9): `errors.Is(err, t)` may be called (the
  error tree of `err` with its methods' specs, Perennial's `errorWalkTree`) and answers `false`:
  what `RenewHTTP`'s caller needs of an error it does not return (`EtcdServer.LeaseRenew` tests
  `errors.Is(err, lease.ErrLeaseNotFound)` and retries the others).
* `leasePeerURL url` (opaque `Prop`, second pass): **the trusted deployment premise** that `url` is
  an etcd member's lease endpoint (`NewHandler`'s), so that a `200` reply is its handler's encoding.
  Nothing proves it; 2c's `leaseTimeToLive` already assumes the leader's peer URLs are members'.
  Without it `TimeToLiveHTTP` panics on a malformed reply
  (`issues/etcd-leasehttp-timetolive-nil-response-panic.md`, `...-nil-header-panic.md`).
* `ltlReply c id` (opaque, pure, second pass): the decoded `LeaseInternalResponse` content `c` has a
  `LeaseTimeToLiveResponse` of lease `id` whose `Header` is set (the handler's
  `&pb.ResponseHeader{}`: an empty message field is encoded and decodes non-`nil`); its laws:
  `ltlReply_norm` (kept by `Proto.norm`: it reads message fields' presence and an integer). 3h's
  vocabulary turns it into the fields (requested of server-core with 2c's `replyHdrOwn`).
-/
module

public import Spec.context.Api
public import Spec.net.http.Api
public import Spec.go_etcd_io.etcd.server.v3.lease.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasehttp
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.lease.leasehttp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasehttp

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `rt` is a usable `http.RoundTripper` (persistent): `net/http`'s `Http.roundTripperOk`. -/
abbrev rtOk (rt : GoInterface) : IProp GF := Http.roundTripperOk rt

def rtOk_persistent.spec : Prop := ∀ rt, Persistent (rtOk (GF := GF) rt)

/-- **Trusted deployment premise: `url` is an etcd member's lease endpoint** (see the header). -/
opaque leasePeerURL (url : GoString) : Prop

/-- **The decoded reply `c` is the leader's answer for lease `id`, its header set** (see the
header). -/
opaque ltlReply (c : Proto.Content) (id : Int) : Prop

/-- `ltlReply` survives `Proto.norm` (the second pass's request of the owners of message
relations: grpc-v3rpc's `holds_norm`). -/
def ltlReply_norm.spec : Prop := ∀ c id, ltlReply c id ↔ ltlReply (Proto.norm c) id

/-- **`errors.Is(err, t)` may be called and answers `false`** (transparent): an error tree of
`err` (`S`, closed under its `Unwrap`s, with the specs of its errors' `Is` and `Unwrap` methods:
Perennial's `errorWalkTree`, as `errors.Is.spec` takes it), typed for `t`, every walk of which
answers `false`. -/
def errIsNot (err t : GoInterface) : IProp GF :=
  iprop(∃ (S : GoError → Prop) (I : GoInterfaceOk → Bool → Prop)
      (U : GoInterfaceOk → List GoError → Prop),
    errors.errorWalkTree S I U t ∗
      ⌜err ≠ GoInterface.nil ∧ S err ∧ errors.TreeTyped S t ∧ ∀ b, errors.IsWalk true I U t err b → b = false⌝)

end res

end Leasehttp
end EtcdGrove
end Perennial
