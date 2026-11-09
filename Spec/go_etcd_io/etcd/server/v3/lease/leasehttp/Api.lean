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
* `leaseURLOf γ ep url` (persistent, opaque; verify-round, server-core's RR request 2): **the lease
  endpoint `url` is `NewHandler`'s over the lessor of the member serving the clients at `ep`** in
  cluster `γ` (the member 2e's `srvEp γ ep id` binds `ep` to, of whichever server object of it).
  Introduced by 2e's `leaseURLOf_intro` (`etcdserver/ApiBoot.lean`, repair3-boot) for a peer URL
  `u` of that member at a state the cluster reached, under this package's `leasePeerURL (u ++
  LeaseInternalPrefix)` (embed's peer handler serves `leasehttp.NewHandler(s.lessor, s.ApplyWait)`
  on the member's own peer URLs; this repository's starters do not). 2c reaches it for the leader's
  URL only under W0's `soleMember γ` (the leader is the member itself). Its heap binders are
  explicit (repair3-boot: the section's variables gave it none, and its realization names 2e's
  `srvEp` at the heap).
* `ltlView γ ep url id found` (transparent, persistent): what the handler at `url` answered, as a
  per-member view: if `url` is `ep`'s member's (`leaseURLOf`), then for every view bound `i` of that
  member, the answer was read from a table `j ≥ i` of the cluster's (`etcdLb` of a state that has
  it), with the member's view of `j`, in which lease `id` is present iff `found`. True of the
  handler (`http.go:109-160`): it waits for `h.waitch()` (the server's `ApplyWait`: its applied
  index at least its committed index when the request arrived, so its lessor at least at any view
  it gave before), then `h.l.Lookup(id)` reads the lessor's current table, `j` (the lessor only
  moves forward); a lease not there: `404` (`found = false`); a found one answered `200`
  (`found = true`) unless demoted (`500`, another error).
-/
module

public import Spec.context.Api
public import Spec.net.http.Api
public import Spec.go_etcd_io.etcd.server.v3.lease.Api
public import Spec.go_etcd_io.etcd.api.v3.State
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

/-- **The lease endpoint `url` is the handler over the lessor of the member serving `ep`** (see
the header; introduced by 2e's `leaseURLOf_intro`). -/
opaque leaseURLOf [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : EtcdModel.Cluster) (ep url : GoString) : IProp GF := iprop(True)

def leaseURLOf_persistent.spec : Prop := ∀ γ ep url, Persistent (leaseURLOf (GF := GF) γ ep url)

/-- **The handler at `url` answered lease `id` (present iff `found`) from a table at or past the
view of `ep`'s member, if it is that member's** (persistent; see the header). -/
def ltlView (url : GoString) (id : Int) (found : Bool) : IProp GF :=
  iprop(□ ∀ (γ : EtcdModel.Cluster) (ep : GoString) (i : Nat),
    leaseURLOf γ ep url -∗ EtcdModel.leaseViewLb γ ep i -∗
      ∃ (j : Nat) (σ₀ : EtcdModel.State) (t : Int → Option EtcdModel.LeaseRec),
        ⌜i ≤ j ∧ σ₀.leaseTables[j]? = some t ∧ ((t id).isSome = found)⌝ ∗
        EtcdModel.etcdLb γ σ₀ ∗ EtcdModel.leaseViewLb γ ep j)

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
