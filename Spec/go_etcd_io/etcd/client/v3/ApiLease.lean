/-
# etcd's Go client: the lease API (batch 1c)

The contract behind W0's slot `leaseAt v γ who` (the client's `Lease` field): a bundle of the
`Lease` interface's triples (`Lease.methods`, one def per method: `Lease.GrantTriple`, ...), in the
shape of the other non-KV calls (`ApiClient.lean`'s `CallTriple`), each call by the principal its
context carries (`ctxPrin who ctx p`).

## What each call says

* **`Grant(ctx, ttl)`**: the request `.leaseGrant 0 ttl` (the server chooses the id), the caller's
  update **persistent**: the client's retry wrapper marks `LeaseGrant` repeatable
  (`retry.go`), so an attempt that granted a lease and then failed with `Unavailable` is resent and
  grants another one. The program's invariant sees every grant (each firing is a step); the caller
  gets the last one's answer (`leaseGrantReply`: the id, an int64, and the granted TTL, at least the
  one asked: `Model.lean`'s `leaseStep`). A lease granted by an abandoned attempt is never kept
  alive: it expires (an environment step) if the cluster expires leases (`EnvCfg.leaseExpiry`), else
  lives on with no key.
* **`Revoke(ctx, id)`**: `.leaseRevoke id`, persistent for the same reason: a resent revoke after an
  applied one answers `ErrLeaseNotFound`. So a caller learns from `ErrLeaseNotFound` only that some
  firing found the lease gone, not that this call did not revoke it.
* **`TimeToLive(ctx, id, opts...)`**, **`Leases(ctx)`**: reads (persistent), answered from the lease
  table of the member that serves the call (`leaseStep`, W0's `State.leaseAnsAt`).
  `TimeToLive` of a lease the lessor does not know is a reply, not an error: `TTL = -1`,
  `GrantedTTL = 0`, no keys (`leaseTTLReply`).
* **Per member** (W0's round 3): for a client frozen at one endpoint `ep` (`clientVia c ep`, its
  `Lease` field calling through `c`: `leaseOf v c`), a grant answered `.ok` gives `leaseViewLb γ ep`
  of the table after it, and a read holding `leaseViewLb γ ep i` is answered from a table `j ≥ i`
  and gives `leaseViewLb γ ep j` (`Lease.GrantTriple`'s and `LeaseRead.Triple`'s `via`): what
  `examples/etcd/{leasegrant,leaseexpiry,leasecatchup}` rely on.
* **`KeepAlive(ctx, id)`**: no update. **A keep-alive tells nothing about the lease's state**: the
  model's keep-alive step changes nothing and its answer is any TTL. What is still observable, and
  what the spec gives: a channel (`kaChan ch id`, persistent) whose every value is a response about
  lease `id` with a positive TTL (`kaRespAt`, read-only: one response is shared by every channel of
  the lease). That it closes (the lease lost, `ctx` done, the lessor closed) is liveness, not stated
  (`nonissues/etcd-client-keepalive-close-never-closed.md`: one interleaving never closes it).
  Receiving never panics, whoever receives. No thread token (1d's need).
* **`KeepAliveOnce(ctx, id)`**: one keep-alive, retried until it gets an answer or a halting error:
  a response about `id` with a positive TTL, or with TTL `≤ 0` and `ErrLeaseNotFound`, or an error.
* **`Close()`**: stops the keep-alive loops (it waits for the receive loop). Returns `nil`. The
  goroutines it stops hold nothing a caller gave, so it gives nothing back.

## Vocabulary

* `lessorHandle l c γ who` (persistent): a `*lessor` over the client `c` (`NewLease`'s; `null` over
  a caller's remote). Intended realization: its `remote` a `remoteLeaseAt` value once `c` is ready,
  `callOpts` the client's, `lg` an `isLogger` (never `nil`:
  `nonissues/etcd-client-lessor-nil-logger.md`), and an invariant over `l.mu` holding `keepAlives`
  (each entry's channels with their `kaChan` invariants, the close token of each channel held by
  the entry until it closes it), `donec` (closed once), `stream`, `streamCancel`, `loopErr`.
* `leaseOf v c` (persistent): the `Lease` value `v` calls through `c` (`lessorHandle_leaseAt`,
  `clientCore_leaseOf`).
* `kaChan ch id` (persistent): a keep-alive channel of lease `id` (`kaChan_recv`).
* `kaRespAt p id` (def): a `*LeaseKeepAliveResponse` read-only, about lease `id`, positive TTL.
* `remoteLeaseAt v γ who` (**the gRPC boundary**): the `etcdserverpb.LeaseClient` value `v` meets the
  wire contract (`remoteLeaseAt_call`, `remoteLeaseAt_keepAlive`: the stream's halves `kaSendAt`,
  `kaRecvAt`, slots of 2a; `kaSent`, `kaSent_sent`: a response is about a lease id sent on the
  stream). Realized for `*retryLeaseClient` (`retryLeaseHandle_remoteLeaseAt`).

## Requirement snippets

`examples/specreq/clientv3lease/`: `grant.go` (a grant's id and TTL, a put with the lease),
`session.go` (concurrency's `Session`; keep-alive values), `reads.go` (`TimeToLive`'s not-found
reply, `Leases`, `KeepAliveOnce`), `member.go` (the per-member lease reads).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-- The unary lease requests. -/
def reqIsLease : Req → Prop
  | .leaseGrant .. | .leaseRevoke _ | .leaseTimeToLive .. | .leaseLeases => True
  | _ => False

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- A reply's header (possibly `nil`), with the given fraction. -/
def hdrOwn (h : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ hm : Option HeaderM, optOwn respHeaderOwn h dq hm)

/-- A slice of keys, read-only. -/
def keysAt (sl : GoSlice) (keys : List Key) : IProp GF :=
  iprop(∃ sls : List GoSlice, sl ↦*□ sls ∗ [∗list] s; k ∈ sls; keys, s ↦*□ k)

/-- What `Grant` returns for the answer `res`: the client's `LeaseGrantResponse` (owned) with the
granted id and TTL. -/
def leaseGrantReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.leaseGrant id ttl) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (h : Loc) (e : GoString),
      resp ↦ ({ ResponseHeader' := h, ID' := W64 id, TTL' := W64 ttl, Error' := e } :
        go_etcd_io.etcd.client.v3.LeaseGrantResponse) ∗ hdrOwn h (DFrac.own 1))
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What `TimeToLive(id)` returns for the answer `res`: the client's `LeaseTimeToLiveResponse`;
a lease the lessor does not know is the reply `TTL = -1`, `GrantedTTL = 0`, no keys. -/
def leaseTTLReply (id : Int) (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.leaseTimeToLive id' ttl gttl keys) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (h : Loc) (ks : GoSlice),
      resp ↦ ({ ResponseHeader' := h, ID' := W64 id', TTL' := W64 ttl, GrantedTTL' := W64 gttl,
                Keys' := ks } : go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse) ∗
      hdrOwn h (DFrac.own 1) ∗ keysAt ks keys)
  | .err .leaseNotFound => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (h : Loc) (ks : GoSlice),
      resp ↦ ({ ResponseHeader' := h, ID' := W64 id, TTL' := W64 (-1), GrantedTTL' := W64 0,
                Keys' := ks } : go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse) ∗
      hdrOwn h (DFrac.own 1) ∗ keysAt ks [])
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What `Leases` returns for the answer `res`: the ids, in the lessor's order. -/
def leaseLeasesReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.leaseLeases ids) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (h : Loc) (sl : GoSlice),
      resp ↦ ({ ResponseHeader' := h, Leases' := sl } : go_etcd_io.etcd.client.v3.LeaseLeasesResponse) ∗
      hdrOwn h (DFrac.own 1) ∗
      sl ↦* (ids.map (fun i => ({ ID' := W64 i } : go_etcd_io.etcd.client.v3.LeaseStatus))))
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- **A keep-alive response about lease `id`, with a positive TTL** (read-only). -/
def kaRespAt (p : Loc) (id : w64) : IProp GF :=
  iprop(∃ (h : Loc) (ttl : w64),
    p ↦□ ({ ResponseHeader' := h, ID' := id, TTL' := ttl } :
      go_etcd_io.etcd.client.v3.LeaseKeepAliveResponse) ∗
    ⌜0 < sint.Z ttl⌝ ∗ hdrOwn h DFrac.discard)

/-- A keep-alive response about lease `id` with the TTL `ttl` (owned: `KeepAliveOnce`'s). -/
def kaRespOwn (p : Loc) (id ttl : w64) : IProp GF :=
  iprop(∃ h : Loc, p ↦ ({ ResponseHeader' := h, ID' := id, TTL' := ttl } :
      go_etcd_io.etcd.client.v3.LeaseKeepAliveResponse) ∗ hdrOwn h (DFrac.own 1))

/-- **A keep-alive channel of lease `id`** (persistent; `kaChan_recv`). -/
opaque kaChan (ch : Loc) (id : w64) : IProp GF := iprop(True)

/-- A `*lessor` over the client `c` (`null`: over a caller's remote), of `γ` as `who` (persistent). -/
opaque lessorHandle (l c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The `Lease` value `v` calls through the client `c`** (persistent; `null`: a caller's remote). -/
opaque leaseOf (v : GoInterface) (c : Loc) : IProp GF := iprop(True)

/-- **The `LeaseClient` value `v` meets the wire contract** (unary lease RPCs and the keep-alive
stream). -/
opaque remoteLeaseAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- A `*retryLeaseClient` over the connection of the client `c`. -/
opaque retryLeaseHandle (r c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The sending half of a keep-alive stream** (exclusive; slot, 2a), the lease ids `ids` sent
on it so far (every `Send`, failed ones too). -/
opaque kaSendAt (sc : GoInterface) (ids : List Int) : IProp GF := iprop(True)
/-- **The lease id `id` was sent on the keep-alive stream `sc`** (persistent; slot, 2a): what a
response received on it is about (the handler answers each request with its `ID`). -/
opaque kaSent (sc : GoInterface) (id : Int) : IProp GF := iprop(True)
/-- **The receiving half of a keep-alive stream** (exclusive; slot, 2a). -/
opaque kaRecvAt (sc : GoInterface) : IProp GF := iprop(True)

/-- **The lessor's entry `ka` of lease `id`** (exclusive; internal to the lessor's proof): its
`donec` and channels with their close tokens (`keepAlive.close`). -/
opaque kaEntry (ka : Loc) (id : w64) : IProp GF := iprop(True)

/-- **An entry's `donec`** (persistent; internal): receiving from it is safe (closed once, by its
entry's `close`). -/
opaque kaDonec (ch : Loc) : IProp GF := iprop(True)

/-- The keep-alive stream's Go type (`Lease_LeaseKeepAliveClient`). -/
def kaStreamTy : go.GoType :=
  google_golang_org.grpc.BidiStreamingClient.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveRequest.ty
    go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse.ty

/-! ## The lease contract -/

/-- The per-member premise of a lease call through the `Lease` value `v`: none, or the client it
calls through is frozen at `ep` (`via = some ep`). -/
def leaseViaPre (v : GoInterface) (via : Option GoString) : IProp GF :=
  match via with
  | none => iprop(True)
  | some ep => iprop(∃ c, leaseOf v c ∗ clientVia c ep)

/-- **`Grant(ctx, ttl)`**: `.leaseGrant 0 ttl`, the update persistent; through a member `ep`, a
grant answered `.ok` gives `leaseViewLb γ ep` of the table it created. -/
def Lease.GrantTriple (m : GoString → val) (v : GoInterface) (P : IProp GF) (γ : Cluster)
    (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (ttl : w64) (via : Option GoString)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ leaseViaPre v via ∗
      callAU γ p (.leaseGrant 0 (sint.Z ttl)) true Q }}
    (App (App (Val (m go!"Grant")) (Val #ctx)) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ σ σ' res, Q σ σ' res ∗ leaseGrantReply res resp err ∗
        match via, res with
        | some ep, .ok _ => leaseViewLb γ ep (σ'.leaseTables.length - 1)
        | _, _ => iprop(True)) ∨
      (⌜resp = null⌝ ∗ indefCall err) }}

/-- **A lease read** (`TimeToLive`, `Leases`) `e` sending `rq`, the update persistent; through a
member `ep` with `leaseViewLb γ ep i` (`via = some (ep, i)`), answered from a table `j ≥ i`, whose
lower bound it gives. -/
def LeaseRead.Triple (e : Expr) (v : GoInterface) (P B : IProp GF) (γ : Cluster) (p : Principal)
    (rq : Req) (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (via : Option (GoString × Nat)) (Q : State → State → Resp → IProp GF),
  {{ P ∗ leaseViaPre v (via.map (·.1)) ∗
      (match via with | some (ep, i) => leaseViewLb γ ep i | none => iprop(True)) ∗
      callAU γ p rq true Q }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((∃ σ σ' res, Q σ σ' res ∗ reply res resp err ∗
         match via with
         | some (ep, i) => iprop(∃ j, ⌜i ≤ j ∧ σ.leaseAnsAt j rq res⌝ ∗ leaseViewLb γ ep j)
         | none => iprop(True)) ∨
       (⌜resp = null⌝ ∗ indefCall err)) }}

/-- `Revoke(ctx, id)`. -/
def Lease.RevokeTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ id : w64, Call.Triple (m go!"Revoke") P γ who [ #id] (.leaseRevoke (sint.Z id))

/-- `TimeToLive(ctx, id, opts...)` (`keys`: `WithAttachedKeys`). -/
def Lease.TimeToLiveTriple (m : GoString → val) (v : GoInterface) (P : IProp GF) (γ : Cluster)
    (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (id : w64) (opts : GoSlice) (gs : List (Bool → Bool)),
  LeaseRead.Triple (App (App (App (Val (m go!"TimeToLive")) (Val #ctx)) (Val #id)) (Val #opts)) v
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ leaseOptsAt opts gs) (leaseOptsAt opts gs) γ p
    (.leaseTimeToLive (sint.Z id) (gs.foldl (fun b g => g b) false)) (leaseTTLReply (sint.Z id))

/-- `Leases(ctx)`. -/
def Lease.LeasesTriple (m : GoString → val) (v : GoInterface) (P : IProp GF) (γ : Cluster)
    (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal),
  LeaseRead.Triple (App (Val (m go!"Leases")) (Val #ctx)) v
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p) iprop(True) γ p .leaseLeases leaseLeasesReply

/-- `KeepAlive(ctx, id)`: a keep-alive channel of lease `id`. -/
def Lease.KeepAliveTriple (m : GoString → val) (P : IProp GF) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (id : w64),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (App (Val (m go!"KeepAlive")) (Val #ctx)) (Val #id))
  {{ (ch : Loc) (err : GoInterface), RET (PairV #ch #err); ⌜ch ≠ null⌝ ∗ kaChan ch id }}

/-- `KeepAliveOnce(ctx, id)`. -/
def Lease.KeepAliveOnceTriple (m : GoString → val) (P : IProp GF) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (id : w64),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (App (Val (m go!"KeepAliveOnce")) (Val #ctx)) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ ttl, kaRespOwn resp id ttl ∗ ⌜0 < sint.Z ttl⌝) ∨
      (⌜err = errVal .leaseNotFound⌝ ∗ ∃ ttl, kaRespOwn resp id ttl ∗ ⌜sint.Z ttl ≤ 0⌝) ∨
      (⌜resp = null⌝ ∗ ∃ k, callErr err k) }}

/-- `Close()`. -/
def Lease.CloseTriple (m : GoString → val) (P : IProp GF) : Prop :=
  {{ P }}
    (App (Val (m go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

/-- **The `Lease` interface's triples** (`m s`: the receiver's method `s`; `v` the `Lease` value the
per-member premise is about). -/
def Lease.methods (m : GoString → val) (v : GoInterface) (P : IProp GF) (γ : Cluster)
    (who : Principal) : Prop :=
  Lease.GrantTriple m v P γ who ∧ Lease.RevokeTriple m P γ who ∧ Lease.TimeToLiveTriple m v P γ who ∧
  Lease.LeasesTriple m v P γ who ∧ Lease.KeepAliveTriple m P who ∧ Lease.KeepAliveOnceTriple m P who ∧
  Lease.CloseTriple m P

/-! ## Laws -/

def handles1cLease_persistent.spec : Prop :=
  (∀ ch id, Persistent (kaChan (GF := GF) ch id)) ∧
  (∀ l c γ who, Persistent (lessorHandle (GF := GF) l c γ who)) ∧
  (∀ v c, Persistent (leaseOf (GF := GF) v c)) ∧
  (∀ v γ who, Persistent (remoteLeaseAt (GF := GF) v γ who)) ∧
  (∀ r c γ who, Persistent (retryLeaseHandle (GF := GF) r c γ who)) ∧
  (∀ ch, Persistent (kaDonec (GF := GF) ch)) ∧
  (∀ sc id, Persistent (kaSent (GF := GF) sc id))

/-- **Receiving from a keep-alive channel**: a response about the lease with a positive TTL, or the
channel closed (and then closed for good). -/
def kaChan_recv.spec : Prop := ∀ (ch : Loc) (id : w64),
  {{ kaChan (GF := GF) ch id }}
    (App (Val (chan.receive (go.GoType.PointerType go_etcd_io.etcd.client.v3.LeaseKeepAliveResponse.ty)))
      (Val #ch))
  {{ (v : Loc) (ok : Bool), RET (PairV #v #ok); if ok then kaRespAt v id else ⌜v = null⌝ }}

/-- The bundle's triples. -/
def leaseAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Lease.methods (fun s => v @!! go_etcd_io.etcd.client.v3.Lease.ty @!! s) v (leaseAt (GF := GF) v γ who)
    γ who

/-- A `*lessor` over a ready client meets the lease contract and calls through it. -/
def lessorHandle_leaseAt.spec : Prop := ∀ l c γ who,
  lessorHandle (GF := GF) l c γ who ∗ clientReady c ⊢
    leaseAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l) γ who ∗
    leaseOf (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l) c

/-- A built client's `Lease` field calls through it. -/
def clientCore_leaseOf.spec : Prop := ∀ c γ who,
  clientCore (GF := GF) c γ who ⊢
    ∃ v, c.[go_etcd_io.etcd.client.v3.Client, go!"Lease"] ↦□ v ∗ leaseOf v c

/-- The wire contract's unary RPCs. -/
def remoteLeaseAt_call.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal) (rq : Req),
  reqIsLease rq → RemoteCallTriple (fun s => v @!! go_etcd_io.etcd.api.v3.etcdserverpb.LeaseClient.ty @!! s)
    (remoteLeaseAt (GF := GF) v γ who) γ who rq

/-- **Opening a keep-alive stream** (`LeaseKeepAlive(ctx, opts...)`): its two halves, or an error. -/
def remoteLeaseAt_keepAlive.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface) (p : Principal) (opts : GoSlice) (rep : Bool),
  {{ remoteLeaseAt (GF := GF) v γ who ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ callOptsOk opts rep }}
    (App (App (Val (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.LeaseClient.ty @!! go!"LeaseKeepAlive"))
      (Val #ctx)) (Val #opts))
  {{ (sc err : GoInterface), RET (PairV #sc #err);
      (⌜err = GoInterface.nil⌝ ∗ kaSendAt sc [] ∗ kaRecvAt sc) ∨
      (⌜sc = GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

/-- **Sending a keep-alive** (slot, 2a): the request message read (any fraction), given back; its id
recorded as sent (whether or not the send succeeded). -/
def kaSendAt_send.spec : Prop := ∀ (sc : GoInterface) (ids : List Int) (req : Loc) (dq : DFrac)
    (id : w64),
  {{ kaSendAt (GF := GF) sc ids ∗ reqOwn req dq (.leaseKeepAlive (sint.Z id)) }}
    (App (Val (sc @!! kaStreamTy @!! go!"Send")) (Val #req))
  {{ (err : GoInterface), RET #err; kaSendAt sc (ids ++ [sint.Z id]) ∗
      reqOwn req dq (.leaseKeepAlive (sint.Z id)) ∗
      (⌜err = GoInterface.nil⌝ ∨ ∃ k, callErr err k) }}

/-- **Closing the sending half** (slot, 2a). -/
def kaSendAt_closeSend.spec : Prop := ∀ (sc : GoInterface) (ids : List Int),
  {{ kaSendAt (GF := GF) sc ids }}
    (App (Val (sc @!! kaStreamTy @!! go!"CloseSend")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∨ ∃ k, callErr err k }}

/-- **The stream's context** (slot, 2a). -/
def kaSendAt_context.spec : Prop := ∀ (sc : GoInterface) (ids : List Int),
  {{ kaSendAt (GF := GF) sc ids }}
    (App (Val (sc @!! kaStreamTy @!! go!"Context")) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; kaSendAt sc ids ∗ Context.ctxOk ctx }}

/-- **Receiving a keep-alive response** (slot, 2a): a fresh message about a lease id sent on the
stream (`kaSent`), or an error. -/
def kaRecvAt_recv.spec : Prop := ∀ (sc : GoInterface),
  {{ kaRecvAt (GF := GF) sc }}
    (App (Val (sc @!! kaStreamTy @!! go!"Recv")) (Val #()))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); kaRecvAt sc ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (h : Loc) (id ttl : w64),
          protoRest go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse p (DFrac.own 1) ∗
          p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"Header"] ↦ h ∗
          p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"ID"] ↦ id ∗
          p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"TTL"] ↦ ttl ∗
          hdrOwn h (DFrac.own 1) ∗ kaSent sc (sint.Z id)) ∨
       (⌜p = null⌝ ∗ ∃ k, callErr err k)) }}

/-- A response's lease id is one the sender sent (slot, 2a). -/
def kaSent_sent.spec : Prop := ∀ (sc : GoInterface) (ids : List Int) (id : Int),
  kaSendAt (GF := GF) sc ids ∗ kaSent sc id ⊢ ⌜id ∈ ids⌝

/-- A `*retryLeaseClient` over a ready client meets the wire contract. -/
def retryLeaseHandle_remoteLeaseAt.spec : Prop := ∀ r c γ who,
  retryLeaseHandle (GF := GF) r c γ who ∗ clientReady c ⊢
    remoteLeaseAt
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty) #r) γ who

end res

end ClientV3
end EtcdGrove
end Perennial
