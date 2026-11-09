/-
# etcd's Go client: the lease API (batch 1c)

The contract behind W0's slot `leaseAt v γ who` (the client's `Lease` field): a bundle of the
`Lease` interface's triples (`Lease.methods`), in the shape of the other non-KV calls
(`ApiClient.lean`'s `CallTriple`).

## What each call says

* **`Grant(ctx, ttl)`**: the request `.leaseGrant 0 ttl` (the server chooses the id), the caller's
  update **persistent**: the client's retry wrapper marks `LeaseGrant` repeatable
  (`retry.go`), so an attempt that granted a lease and then failed with `Unavailable` is resent and
  grants another one. The program's invariant sees every grant (each firing is a step); the caller
  gets the last one's answer (`leaseGrantReply`: the id and the granted TTL, at least the one asked:
  `Model.lean`'s `leaseStep`). A lease granted by an abandoned attempt is never kept alive and
  expires (an environment step).
* **`Revoke(ctx, id)`**: `.leaseRevoke id`, persistent for the same reason: a resent revoke after an
  applied one answers `ErrLeaseNotFound`. So a caller learns from `ErrLeaseNotFound` only that some
  firing found the lease gone, not that this call did not revoke it.
* **`TimeToLive(ctx, id, opts...)`**, **`Leases(ctx)`**: reads (persistent), answered by a lessor that
  may be behind or deposed (`leaseStep`). `TimeToLive` of a lease the lessor does not know is a
  reply, not an error: `TTL = -1`, `GrantedTTL = 0`, no keys (the gRPC handler's mapping of
  `ErrLeaseNotFound`; `leaseTTLReply`).
* **`KeepAlive(ctx, id)`**: no update. **A keep-alive tells nothing about the lease's state**: the
  model's keep-alive step changes nothing and its answer is any TTL (time is not modelled, and a
  deposed leader may still renew a lease the new leader revoked: W0's decision). What is still
  observable, and what the spec gives: a channel (`kaChan ch id`, persistent) whose every value is a
  response about lease `id` with a positive TTL (`kaRespAt`, read-only: one response is shared by
  every channel of the lease), and which is eventually closed (when the lease's TTL is reported
  `≤ 0`, its deadline passes without a response, `ctx` is done, the lessor stops; liveness, not
  stated: a WP is partial). Receiving never panics, whoever receives.
* **`KeepAliveOnce(ctx, id)`**: one keep-alive, retried until it gets an answer or a halting error:
  a response about `id` with a positive TTL, or with TTL `≤ 0` and `ErrLeaseNotFound`, or an error.
* **`Close()`**: stops the keep-alive loops (it waits for the receive loop); every keep-alive channel
  is closed by then or shortly after; later `KeepAlive`s return a closed channel and an error.
  Returns `nil`. The goroutines it stops hold nothing a caller gave (no counted resource is taken
  by the lease API: the loops are the lessor's own), so it gives nothing back.

## Vocabulary

* `lessorHandle l γ who` (persistent): a `*lessor` (`NewLease`'s). Intended realization: its
  `remote` a `remoteLeaseAt` value, `callOpts` the client's, `lg` an `isLogger` (never `nil`:
  `NewLeaseFromLeaseClient` with a `nil` client leaves it `nil`, and the loops' `l.lg.Warn` then
  panics on a stream error; its spec takes a client), and an invariant over `l.mu` holding `keepAlives` (each entry's channels with their
  `kaChan` invariants, the close token of each channel held by the entry until it closes it), the
  `donec` channel (closed once, by the receive loop or by `Close`), `stream`, `streamCancel`,
  `loopErr`.
* `kaChan ch id` (persistent): a keep-alive channel of lease `id` (`kaChan_recv`). Intended
  realization: Perennial's channel invariant (`isChan`) whose every value meets `kaRespAt _ id`, the
  close token in the lessor's invariant.
* `kaRespAt p id` (def): a `*LeaseKeepAliveResponse` read-only, about lease `id`, positive TTL.
* `remoteLeaseAt v γ who` (**the gRPC boundary**): the `etcdserverpb.LeaseClient` value `v` meets the
  wire contract: the unary lease RPCs (`remoteLeaseAt_call`, `ApiClient.lean`'s
  `RemoteCallTriple`) and the keep-alive stream (`remoteLeaseAt_keepAlive`: a bidirectional stream
  whose halves are `kaSendAt`, `kaRecvAt`, slots of 2a). Realized for `*retryLeaseClient`
  (`retryLeaseHandle_remoteLeaseAt`).

## Requirement snippets

`examples/specreq/clientv3lease/`: `grant.go` (a grant's id and TTL, a put with the lease),
`session.go` (concurrency's `Session`: grant, keep alive until the channel closes, revoke),
`reads.go` (`TimeToLive`'s not-found reply, `Leases`), `once.go` (`KeepAliveOnce`).
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

/-- A `*lessor` of `γ` as `who` (persistent). -/
opaque lessorHandle (l : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The `LeaseClient` value `v` meets the wire contract** (unary lease RPCs and the keep-alive
stream). -/
opaque remoteLeaseAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- A `*retryLeaseClient`. -/
opaque retryLeaseHandle (r : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The sending half of a keep-alive stream** (exclusive; slot, 2a). -/
opaque kaSendAt (sc : GoInterface) : IProp GF := iprop(True)
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

/-- **The `Lease` interface's triples.** -/
def Lease.methods (v : GoInterface) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  let m := fun (s : GoString) => v @!! go_etcd_io.etcd.client.v3.Lease.ty @!! s
  (∀ (ctx : GoInterface) (ttl : w64),
    CallTriple (App (App (Val (m go!"Grant")) (Val #ctx)) (Val #ttl))
      iprop(P ∗ Context.ctxOk ctx) iprop(True) γ who (.leaseGrant 0 (sint.Z ttl)) true
      leaseGrantReply) ∧
  (∀ (ctx : GoInterface) (id : w64),
    CallTriple (App (App (Val (m go!"Revoke")) (Val #ctx)) (Val #id))
      iprop(P ∗ Context.ctxOk ctx) iprop(True) γ who (.leaseRevoke (sint.Z id)) true ansReply) ∧
  (∀ (ctx : GoInterface) (id : w64) (opts : GoSlice) (gs : List (Bool → Bool)),
    CallTriple (App (App (App (Val (m go!"TimeToLive")) (Val #ctx)) (Val #id)) (Val #opts))
      iprop(P ∗ Context.ctxOk ctx ∗ leaseOptsAt opts gs) (leaseOptsAt opts gs) γ who
      (.leaseTimeToLive (sint.Z id) (gs.foldl (fun b g => g b) false)) true
      (leaseTTLReply (sint.Z id))) ∧
  (∀ (ctx : GoInterface),
    CallTriple (App (Val (m go!"Leases")) (Val #ctx))
      iprop(P ∗ Context.ctxOk ctx) iprop(True) γ who .leaseLeases true leaseLeasesReply) ∧
  (∀ (ctx : GoInterface) (id : w64),
    {{ P ∗ Context.ctxOk ctx }}
      (App (App (Val (m go!"KeepAlive")) (Val #ctx)) (Val #id))
    {{ (ch : Loc) (err : GoInterface), RET (PairV #ch #err); ⌜ch ≠ null⌝ ∗ kaChan ch id }}) ∧
  (∀ (ctx : GoInterface) (id : w64),
    {{ P ∗ Context.ctxOk ctx }}
      (App (App (Val (m go!"KeepAliveOnce")) (Val #ctx)) (Val #id))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ ttl, kaRespOwn resp id ttl ∗ ⌜0 < sint.Z ttl⌝) ∨
        (⌜err = errVal .leaseNotFound⌝ ∗ ∃ ttl, kaRespOwn resp id ttl ∗ ⌜sint.Z ttl ≤ 0⌝) ∨
        (⌜resp = null⌝ ∗ ∃ k, callErr err k) }}) ∧
  ({{ P }}
     (App (Val (m go!"Close")) (Val #()))
   {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }})

/-! ## Laws -/

def handles1cLease_persistent.spec : Prop :=
  (∀ ch id, Persistent (kaChan (GF := GF) ch id)) ∧
  (∀ l γ who, Persistent (lessorHandle (GF := GF) l γ who)) ∧
  (∀ v γ who, Persistent (remoteLeaseAt (GF := GF) v γ who)) ∧
  (∀ r γ who, Persistent (retryLeaseHandle (GF := GF) r γ who)) ∧
  (∀ ch, Persistent (kaDonec (GF := GF) ch))

/-- **Receiving from a keep-alive channel**: a response about the lease with a positive TTL, or the
channel closed (and then closed for good). -/
def kaChan_recv.spec : Prop := ∀ (ch : Loc) (id : w64),
  {{ kaChan (GF := GF) ch id }}
    (App (Val (chan.receive (go.GoType.PointerType go_etcd_io.etcd.client.v3.LeaseKeepAliveResponse.ty)))
      (Val #ch))
  {{ (v : Loc) (ok : Bool), RET (PairV #v #ok); if ok then kaRespAt v id else ⌜v = null⌝ }}

/-- The bundle's triples. -/
def leaseAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Lease.methods v (leaseAt (GF := GF) v γ who) γ who

/-- A `*lessor` meets the lease contract (its methods' specs, `lessor__*.lean`). -/
def lessorHandle_leaseAt.spec : Prop := ∀ l γ who,
  lessorHandle (GF := GF) l γ who ⊢
    leaseAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l) γ who

/-- The wire contract's unary RPCs. -/
def remoteLeaseAt_call.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal) (rq : Req),
  reqIsLease rq → RemoteCallTriple (fun s => v @!! go_etcd_io.etcd.api.v3.etcdserverpb.LeaseClient.ty @!! s)
    (remoteLeaseAt (GF := GF) v γ who) γ who rq

/-- **Opening a keep-alive stream** (`LeaseKeepAlive(ctx, opts...)`): its two halves, or an error
(the stream interceptor's token fetch, or the open's). -/
def remoteLeaseAt_keepAlive.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface) (opts : GoSlice) (rep : Bool),
  {{ remoteLeaseAt (GF := GF) v γ who ∗ Context.ctxOk ctx ∗ callOptsOk opts rep }}
    (App (App (Val (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.LeaseClient.ty @!! go!"LeaseKeepAlive"))
      (Val #ctx)) (Val #opts))
  {{ (sc err : GoInterface), RET (PairV #sc #err);
      (⌜err = GoInterface.nil⌝ ∗ kaSendAt sc ∗ kaRecvAt sc) ∨
      (⌜sc = GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

/-- **Sending a keep-alive** (slot, 2a): the request message read (any fraction), given back. -/
def kaSendAt_send.spec : Prop := ∀ (sc : GoInterface) (req : Loc) (dq : DFrac) (id : w64),
  {{ kaSendAt (GF := GF) sc ∗ reqOwn req dq (.leaseKeepAlive (sint.Z id)) }}
    (App (Val (sc @!! kaStreamTy @!! go!"Send")) (Val #req))
  {{ (err : GoInterface), RET #err; kaSendAt sc ∗ reqOwn req dq (.leaseKeepAlive (sint.Z id)) ∗
      (⌜err = GoInterface.nil⌝ ∨ ∃ k, callErr err k) }}

/-- **Closing the sending half** (slot, 2a). -/
def kaSendAt_closeSend.spec : Prop := ∀ (sc : GoInterface),
  {{ kaSendAt (GF := GF) sc }}
    (App (Val (sc @!! kaStreamTy @!! go!"CloseSend")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∨ ∃ k, callErr err k }}

/-- **The stream's context** (slot, 2a): done once the stream ends. -/
def kaSendAt_context.spec : Prop := ∀ (sc : GoInterface),
  {{ kaSendAt (GF := GF) sc }}
    (App (Val (sc @!! kaStreamTy @!! go!"Context")) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; kaSendAt sc ∗ Context.ctxOk ctx }}

/-- **Receiving a keep-alive response** (slot, 2a): a fresh message (about some lease the stream
was sent, with any TTL: the model's keep-alive answer), or an error. -/
def kaRecvAt_recv.spec : Prop := ∀ (sc : GoInterface),
  {{ kaRecvAt (GF := GF) sc }}
    (App (Val (sc @!! kaStreamTy @!! go!"Recv")) (Val #()))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); kaRecvAt sc ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (h : Loc) (id ttl : w64),
          protoRest go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse p (DFrac.own 1) ∗
          p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"Header"] ↦ h ∗
          p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"ID"] ↦ id ∗
          p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"TTL"] ↦ ttl ∗
          hdrOwn h (DFrac.own 1)) ∨
       (⌜p = null⌝ ∗ ∃ k, callErr err k)) }}

/-- A `*retryLeaseClient` meets the wire contract. -/
def retryLeaseHandle_remoteLeaseAt.spec : Prop := ∀ r γ who,
  retryLeaseHandle (GF := GF) r γ who ⊢
    remoteLeaseAt
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty) #r) γ who

end res

end ClientV3
end EtcdGrove
end Perennial
