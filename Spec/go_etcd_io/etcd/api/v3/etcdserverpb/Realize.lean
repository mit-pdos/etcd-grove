/-
# etcdserverpb (batch 3h): the realization of the client's message and stub slots

The laws over the client's vocabulary (1b's `ApiWatch.lean`, 1c's `ApiClient.lean`/`ApiLease.lean`):
the watch messages' and the non-KV messages' relation to protobuf's content (`watchReqOwn_msgAt`,
`reqOwn_msgAt`, `replyOwn_msgAt`), the fields of the lease replies the client's lessor copies
(`replyOwn_lease*`), `UserAddOptions` (`userAddOptsAt_unfold`), `StatusResponse`
(`statusRespOwn_msgAt`). The stubs' constructors (`NewKVClient.spec`, ...) are in their own files
and import this module.

**Laws offered by 2b** (`v3rpc/ApiWatch.lean`: `watchReqOwn_unfold`, `wireWatchRespOwn_unfold`,
`wireWatchRespOwn_persist`) are accepted as stated: they are this batch's obligations (the field
realization of `watchReqOwn`, `wireWatchRespOwn`), not restated here. A create's raw key `""` models
the key `"\x00"` (`createRange`), as 1b asked (round 1, item 4).

**Integration I3**: 1b's watch messages (`EventM`, `WireWatchReq`, `WireWatchRespM`, `eventOwn`,
`watchReqOwn`, `wireWatchRespOwn`) now live in W0's `api/v3/Wire.lean`; this module realizes them
there as before (`*_msgAt` below). W0's new laws `eventOwn_persist`, `eventOwn_discard_persistent`
and `msgOwn_discard_persistent` (integration I1) are this batch's obligations too: each message
predicate is `∃ c, Proto.msgAt T p dq c ∗ ⌜holds c m⌝` (the relation laws), and `Proto.msgAt`'s
`persist` and its persistence at `DFrac.discard` (`Proto/Api.lean`) give them (`protoRest` likewise:
the bookkeeping fields under `msgAt`). The watch contract (`ClientV3.watchSpec`, 2a's, now in
the client's `ApiWatch.lean`) is stated over `watchReqHolds`/`watchRespHolds`, which integration X
moved to `Api.lean` with `eventHolds`, `watch_holds_fun`, `watch_holds_depth` (the client's
`ApiWatch` cannot import this module, which imports it).

**Intended realization**: as `Api.lean`'s (each predicate the field-level predicate of its unfold
law; `msgAt` of each type the same; each relation "the content's fields are the model's").

**Not realizable today** (the translation, `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`, names
only): the fields of `Member`, `MemberAddResponse`, `MemberListResponse`, `AlarmResponse`,
`StatusResponse` (1c's `Client.Sync`, `MemberList`, `Status` snippets). Their contents are related to
the models (`replyOwn_msgAt`, `bodyHolds`), so gRPC transports them; reading a field in Go needs the
struct translated (an open question of the batch report).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import Spec.go_etcd_io.etcd.client.v3.ApiWatch
public import Spec.go_etcd_io.etcd.client.v3.ApiLease
public import GeneratedProof.go_etcd_io.etcd.api.v3.authpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.api.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def watchReqOwn_msgAt.spec : Prop := ∀ p dq r,
  watchReqOwn (GF := GF) p dq r ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.WatchRequest.ty p dq c ∗ ⌜watchReqHolds c r⌝
def wireWatchRespOwn_msgAt.spec : Prop := ∀ p dq m,
  wireWatchRespOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.WatchResponse.ty p dq c ∗ ⌜watchRespHolds c m⌝
def eventOwn_msgAt.spec : Prop := ∀ p dq e,
  eventOwn (GF := GF) p dq e ⊣⊢ ∃ c, Proto.msgAt mvccpb.Event.ty p dq c ∗ ⌜eventHolds c e⌝

/-- **A non-KV request** (1c's `reqOwn`): `msgAt` of its type holding its model. -/
def reqOwn_msgAt.spec : Prop := ∀ p dq rq,
  reqOwn (GF := GF) p dq rq ⊣⊢ ∃ c, Proto.msgAt (reqType rq) p dq c ∗ ⌜reqHolds c rq⌝

/-- **A reply** (1c's `replyOwn`, owned): `msgAt` of its type holding the body (`replyModels`). -/
def replyOwn_msgAt.spec : Prop := ∀ p b,
  replyOwn (GF := GF) p b ⊣⊢
    ∃ c, Proto.msgAt (bodyType b) p (DFrac.own 1) c ∗ ⌜replyModels go!"" b c⌝

/-- **The lease replies' fields** (the client's `lessor.Grant`, `TimeToLive`, `Leases` copy them):
the header (some, possibly `nil`), the model's ids and TTLs, lent until given back. -/
def replyOwn_lease.spec : Prop :=
  (∀ (p : Loc) (id ttl : Int), replyOwn (GF := GF) p (.leaseGrant id ttl) ⊢
    ∃ (h : Loc) (ho : Option HeaderM) (e : GoString),
      p.[etcdserverpb.LeaseGrantResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[etcdserverpb.LeaseGrantResponse, go!"ID"] ↦ W64 id ∗
      p.[etcdserverpb.LeaseGrantResponse, go!"TTL"] ↦ W64 ttl ∗
      p.[etcdserverpb.LeaseGrantResponse, go!"Error"] ↦ e ∗
      (p.[etcdserverpb.LeaseGrantResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
       p.[etcdserverpb.LeaseGrantResponse, go!"ID"] ↦ W64 id ∗
       p.[etcdserverpb.LeaseGrantResponse, go!"TTL"] ↦ W64 ttl ∗
       p.[etcdserverpb.LeaseGrantResponse, go!"Error"] ↦ e -∗ replyOwn p (.leaseGrant id ttl))) ∧
  (∀ (p : Loc) (id ttl gttl : Int) (ks : List Key),
    replyOwn (GF := GF) p (.leaseTimeToLive id ttl gttl ks) ⊢
    ∃ (h : Loc) (ho : Option HeaderM) (ksl : GoSlice) (kps : List GoSlice),
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Header"] ↦ h ∗
        optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"ID"] ↦ W64 id ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"TTL"] ↦ W64 ttl ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"GrantedTTL"] ↦ W64 gttl ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Keys"] ↦ ksl ∗ ksl ↦* kps ∗
      ([∗list] s; k ∈ kps; ks, s ↦*□ k) ∗
      (p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Header"] ↦ h ∗
        optOwn respHeaderOwn h (DFrac.own 1) ho ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"ID"] ↦ W64 id ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"TTL"] ↦ W64 ttl ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"GrantedTTL"] ↦ W64 gttl ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Keys"] ↦ ksl ∗ ksl ↦* kps -∗
       replyOwn p (.leaseTimeToLive id ttl gttl ks))) ∧
  (∀ (p : Loc) (ids : List Int), replyOwn (GF := GF) p (.leaseLeases ids) ⊢
    ∃ (h : Loc) (ho : Option HeaderM) (lsl : GoSlice) (lps : List Loc),
      p.[etcdserverpb.LeaseLeasesResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[etcdserverpb.LeaseLeasesResponse, go!"Leases"] ↦ lsl ∗ lsl ↦* lps ∗
      ([∗list] l; id ∈ lps; ids, l.[etcdserverpb.LeaseStatus, go!"ID"] ↦ W64 id) ∗
      (p.[etcdserverpb.LeaseLeasesResponse, go!"Header"] ↦ h ∗
        optOwn respHeaderOwn h (DFrac.own 1) ho ∗
       p.[etcdserverpb.LeaseLeasesResponse, go!"Leases"] ↦ lsl ∗ lsl ↦* lps ∗
       ([∗list] l; id ∈ lps; ids, l.[etcdserverpb.LeaseStatus, go!"ID"] ↦ W64 id) -∗
       replyOwn p (.leaseLeases ids)))

/-- **`UserAddWithOptions`' options** (1c's `userAddOptsAt`): `nil` (a password required), or a
read-only `authpb.UserAddOptions` whose `NoPassword` is `noPw`. -/
def userAddOptsAt_unfold.spec : Prop := ∀ (p : Loc) (noPw : Bool),
  userAddOptsAt (GF := GF) p noPw ⊣⊢
    ⌜p = null ∧ noPw = false⌝ ∨
    (protoRest authpb.UserAddOptions p DFrac.discard ∗
      p.[authpb.UserAddOptions, go!"NoPassword"] ↦□ noPw)

/-- **A `StatusResponse`** (1c's `statusRespOwn`, no model: the client reads nothing of it but
passes it on): an owned message of that type. -/
def statusRespOwn_msgAt.spec : Prop := ∀ p,
  statusRespOwn (GF := GF) p ⊣⊢ ∃ c, Proto.msgAt etcdserverpb.StatusResponse.ty p (DFrac.own 1) c

end laws

end EtcdServerPb
end EtcdGrove
end Perennial
