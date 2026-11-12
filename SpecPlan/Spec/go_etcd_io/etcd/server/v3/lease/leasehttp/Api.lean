/-
# `server/lease/leasehttp`: vocabulary (batch 2e)

The lease HTTP endpoints a follower forwards to the leader (`RenewHTTP`, `TimeToLiveHTTP`: the
latter's spec added in the second pass, for 2c's `leaseTimeToLive`). Trusted (names only).

* `rtOk rt` (persistent): `rt` is an `http.RoundTripper` that may be used from any goroutine
  (`rafthttp.NewRoundTripper`'s, the server's `peerRt`). Integration (I5): no longer provisional:
  it is the `net/http` boundary's `Http.roundTripperOk rt` (`SpecPlan/Spec/net/http/Api.lean`), which
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
  URL only under W0's `soleMember γ` (the leader is the member itself) and `peerLeaseServed γ`
  (2e's `peerLeaseServed_url`; verify-round F1). Its heap binders are
  explicit (repair3-boot: the section's variables gave it none, and its realization names 2e's
  `srvEp` at the heap).
* `leaseLbOpt γ ep vi` (transparent): the caller's optional view bound of `ep`'s member
  (`leaseViewLb γ ep i` for `vi = some i`; nothing for `none`); 2c's `srvLeaseLbOpt` is this
  (verify-round F3: one definition).
* `ltlView γ ep vi url id found` (transparent, persistent): what the handler at `url` answered, as a
  per-member view: for the caller's view bound `vi = some i` (held **before** the call: the
  precondition's `leaseLbOpt`), if `url` is `ep`'s member's (`leaseURLOf`), the answer was read from
  a table `j ≥ i` of the cluster's (`etcdLb` of a state that has it), with the member's view of `j`,
  in which lease `id` is present iff `found`; for `vi = none`, nothing. True of the handler
  (`http.go:109-160`): it waits for `h.waitch()` (the server's `ApplyWait`: its applied index at
  least its committed index when the request arrived, so its lessor at least at any view it gave
  before the call), then `h.l.Lookup(id)` reads the lessor's current table, `j` (the lessor only
  moves forward); a lease not there: `404` (`found = false`); a found one answered `200`
  (`found = true`) unless demoted (`500`, another error). `leaseURLOf` may be shown after the call:
  it is a run-wide fact about `url` (its peer-URL set is single-use and its host's `addrFree` spent
  once, so `url` had no other handler before). Verify-round F3 (`verify/F-client-api.md`): the view
  bound was quantified inside the persistent wand (`□ ∀ γ ep i, … leaseViewLb γ ep i -∗ …`), so a
  view obtained after the answer (a grant after a `404`) could be fed to it: `False`.
* `leaseURLOf_peerURL`: a `leaseURLOf` endpoint is an etcd member's (`leasePeerURL`; its
  realization's conjunct), so a caller holding it meets `TimeToLiveHTTP`'s deployment premise.
-/
module

public import SpecPlan.Spec.context.Api
public import SpecPlan.Spec.net.http.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Api
public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.State
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasehttp
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.server.v3.lease.leasehttp

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

/-- An endpoint over a member's lessor is an etcd member's lease endpoint (verify-round F1). -/
def leaseURLOf_peerURL.spec : Prop := ∀ γ ep url,
  leaseURLOf (GF := GF) γ ep url ⊢ ⌜leasePeerURL url⌝

/-- **The caller's optional view bound of `ep`'s member** (see the header; 2c's `srvLeaseLbOpt`). -/
def leaseLbOpt (γ : EtcdModel.Cluster) (ep : GoString) (vi : Option Nat) : IProp GF :=
  match vi with | some i => EtcdModel.leaseViewLb γ ep i | none => iprop(True)

/-- **The handler at `url` answered lease `id` (present iff `found`) from a table at or past the
caller's view bound `vi` of `ep`'s member, if it is that member's** (persistent; see the header). -/
def ltlView (γ : EtcdModel.Cluster) (ep : GoString) (vi : Option Nat) (url : GoString) (id : Int)
    (found : Bool) : IProp GF :=
  match vi with
  | some i => iprop(□ (leaseURLOf γ ep url -∗
      ∃ (j : Nat) (σ₀ : EtcdModel.State) (t : Int → Option EtcdModel.LeaseRec),
        ⌜i ≤ j ∧ σ₀.leaseTables[j]? = some t ∧ ((t id).isSome = found)⌝ ∗
        EtcdModel.etcdLb γ σ₀ ∗ EtcdModel.leaseViewLb γ ep j))
  | none => iprop(True)

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
