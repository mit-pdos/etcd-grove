/-
# etcd's leasing KV (`client/v3/leasing`): the vocabulary (batch 1e)

`leasing.NewKV(cl, pfx, opts...)` wraps a client's `KV` in a **leasing KV**: a `clientv3.KV` that
caches keys it holds a lease on (a *lease key* `pfx ++ k`, put with its session's lease) and answers
`Get`s of them, and transactions of only such `Get`s, from that cache. The only user in etcd is the
gRPC proxy with `--experimental-leasing-prefix` (`server/etcdmain/grpc_proxy.go:488`:
`client.KV, _, _ = leasing.NewKV(client, prefix)`), which then serves its whole KV API (`Range`,
`Put`, `DeleteRange`, `Txn` through `Do`, `Compact`) from it (`proxy/grpcproxy/kv.go`); and the
integration tests (`tests/integration/clientv3/lease/leasing_test.go`).

## What this KV meets of the KV contract (W0, `client/v3/Api.lean`), plainly

The leasing KV is meant to be indistinguishable from the plain client (its doc: it "serves
linearizable reads from a local cache"). Of the anchor's KV contract it meets exactly:

* **`Compact`**: `KV.CompactTriple`, unchanged (it calls the wrapped client's).
* **`GetStream`**: `KV.GetStreamTriple`, trivially: it always returns gRPC's `Unimplemented`, an
  error that settles nothing (`indefCall`).

It does **not** meet `KV.GetTriple`, `KV.PutTriple`, `KV.DeleteTriple`, `KV.DoTriple`,
`KV.TxnTriple` (its transactions' `Commit`), for four independent reasons, each true of the pinned
code (`.lake/src/client/leasing`, the fork `a4d2bb17`):

1. **Its writes are not at most once.** A `Put` or `Delete` of a key it has not cached is committed
   twice whenever no other client holds the key's lease (`tryModifyOp` commits it and returns no
   waiter channel, which `put`/`delete` read as "not committed" and commit again through
   `revoke`: `issues/leasing-modify-uncached-once.md`, the default path of every first write of a
   key); and after an error of its first attempt (which may still take effect) it resends the
   write through `revoke`. So the caller's update for a write is fired any number of times: it must
   be **persistent** (`□`), not the contract's exclusive one.
2. **It writes keys the caller did not ask it to**: lease keys under `pfx` (a `Get` puts one, a
   write to a key another client holds puts `"REVOKE"` into it, the lease monitors delete them),
   and its session grants and keeps alive a lease. The program must permit these steps
   (`protoUpd`, given to `NewKV`), and a write's update must accept a protocol step in place of an
   answer (`LStep`'s `none`): `revoke` sends one transaction that is either the caller's write
   (its guard holds) or the `"REVOKE"` put (it does not), and which one is known only at its
   commit, so a single update must cover both.
3. **Its cached answers are not linearizable**, even without its bugs: a holder's cache is valid
   only while its lease key exists, and the lease key is deleted when its session's lease expires,
   which the model (W0's `EnvStep.leaseExpire`, at any time: time is not modelled) lets happen while
   the holder still serves its cache (until its session monitor notices; etcd-io/etcd#19091). The
   protocol fences *writers* by revisions (every write is guarded by `CreateRevision(pfx ++ k) <
   rev + 1`), but not *cached readers*: a cached read contacts no member. With its bugs, a cached
   answer is not even an answer the cluster ever gave: after its own puts the cache holds a
   key-value computed from the put's arguments (`issues/leasing-update-stale.md`: a version or value
   etcd never had); it keeps keys a failed range delete deleted (`issues/leasing-evictrange-key.md`),
   keys whose lease ended before it cached them (`issues/leasing-stale-entry-after-reset.md`), keys a
   range delete went through without revoking (`issues/leasing-wait-rescind-no-delete.md`); a
   cached transaction may take the wrong branch (`issues/leasing-evalcmp-missing-key.md`) and then
   skips the other branch's writes; a `Get` of a key another client holds ignores its options
   (`issues/leasing-get-failed-acquire-options.md`). So a cached answer (`CachedAns`) is stated
   only by what the code does guarantee of it: about the requested keys only, at a revision the
   cluster has reached, which may be **below** revisions the caller saw since (a cached `Get`
   answers with the entry's header, `cache.go`'s `copyGetResponseMetadataOnly`: W0's
   `req/go_etcd_io_etcd_client_v3_leasing.md`; W0's `ReqRevisionsMonotone` fails through it).
4. **Its errors settle nothing**: it returns errors of its own protocol requests (`ErrLeaseNotFound`
   once its session's lease is gone, a permission denied on the lease prefix, its own context's
   cancellation), which are no answer to the caller's request; and a write's error may follow an
   attempt that took effect. So an error carries no update's `Q` (the contract's definite errors
   do).

Two more differences of shape: a range delete drops the caller's `WithPrevKV` (`deleteRangeRPC`
sends its own `OpDelete(key, WithRange(end))`: no previous key-values; a finding, `execReq`); and
the replies of `Put` and of a transaction are read-only (their header is shared with the cache,
`leaseCache.Update` keeps the pointer: `putReplyL`, `txnReplyL`). And every call but `Compact`,
`GetStream` and `Txn` takes a thread token for the cache's reader slots (given back), and `Get` and
`Do` a share of the "open" token (`lkvOpen`), which the close function takes whole (a `Get` adds a
lease monitor to the KV's wait group: `nonissues/etcd-leasing-get-during-close-waitgroup.md`).

**The leasing contract** (`LKV.*Triple`, `LTxn.*Triple`) is therefore the KV contract with the
caller's update persistent for every request and over `LStep pfx who rq` instead of `Step who rq`,
an error that settles nothing in place of the definite/indefinite split, and the shape differences
above; the context premises are W0's (`Context.ctxOk ctx`, `ctxPrin ctx who`). It is a weakening: a value meeting the KV contract (`ClientV3.kvAt`) meets the leasing
contract for any `pfx` (every `Step` is an `LStep`; a definite error's `Q` may be dropped).

**What would make it meet the KV contract** (decisions for the user, `notes/specs-only/batch-1e.md`):
the six fixes (branches `leasing-*` of upamanyus/etcd, each in its issue) make the writes at most
once if `put`/`delete` also stop resending after an error, and make a cached answer the key's record
at a past revision: then `CachedAns` becomes "the request's answer at a past state" (W0's
serializable-read semantics: `Step who (.range {r with serializable := true})`), and the leasing
KV's `Get` meets `KV.GetTriple` for the serializable version of the request. Linearizable cached
reads need a model of time (a lease that is not revoked before its TTL), which W0 excludes.

## Vocabulary

* `ProtoStep pfx who σ σ'` (pure): a step the leasing protocol takes on its own account: none, or a
  request of `who` whose effect on the KV is confined to keys under `pfx`, or a lease grant or
  keep-alive of `who` (its session).
* `CachedRange r σ rev a`, `CachedAns rq σ res` (pure): what the pinned code guarantees of an
  answer it gives without the request reaching a member (see 3. above).
* `execReq rq` (pure): the request the leasing KV makes of `rq` (a range delete without
  `prevKv`).
* `LStep pfx who rq σ σ' r` (pure): what the leasing KV may do with the caller's update for `rq`:
  `some res`, the request's step answering `res` or a cached answer at an unchanged state; `none`,
  a protocol step. `LQ Q` the update's `COMM`: `Q` for an answer, `True` for a protocol step.
* `protoUpd γ who pfx` (def, persistent): **the program's permission for the protocol's steps**
  (`□` atomic update performing any `ProtoStep`), which `NewKV` takes, as the cluster takes
  `envUpd`. The program chooses `pfx` and keeps an invariant stable under these steps (one whose
  keys are outside `pfx` and attached to none of `who`'s leases sees only revisions advance).
* `LeasingNames` (opaque): a leasing KV's ghost names (its "open" token, its internal invariants).
* `isLeasingKV lkv γ who pfx γL` (persistent): `lkv` is a `*leasingKV` over a client of `γ` as
  `who`, with lease prefix `pfx`. Intended realization: its immutable fields (`cl`, `kv`, `pfx`,
  `ctx`, `cancel`, `sessionOpts`), `isClient cl γ who` and `kvAt` of its `kv`, `protoUpd γ who pfx`,
  the session options, an invariant holding its cache's lock (`Internal.lean`'s `lcAt`: the cache's
  fields and the session's, each entry's response with its `etcdLb` facts, `cachedRespOk`), the
  wait group's invariant (its counter the running monitors, each with a thread token; the open
  token's authority, so that no `Add` happens once `Close` holds it all), and the pool of the
  cache's reader slots (`notes/bounds-plan.md`, B2).
* `lkvAt v γ who pfx γL` (persistent): the `v3.KV` interface value `v` meets the leasing contract
  (a bundle of its methods' triples, `lkvAt_methods`); `isLeasingKV_lkvAt` for a `*leasingKV`.
* `lkvOpen γL q` (fractional): a share of the "open" token: `Get`/`Do` take a share, the close
  function the whole.
* `closeFnAt cf γL` (persistent): `cf` is the close function `NewKV` returns (`lkv.Close`).
* `ltxnAt iv γ who pfx ctx st` (exclusive): a leasing transaction under construction (`txnLeasing`,
  W0's `TxnSt`), with its four triples (`ltxnAt_methods`).
* `sessOptsOk osl cl` (**slot, 1d**, persistent): `osl` is a read-only slice of
  `concurrency.SessionOption`s with which `concurrency.NewSession(cl, osl...)` meets its spec.

## Requirement snippets

`examples/specreq/leasing/`: `lifecycle.go` (`NewKV` as the proxy and the tests call it, the close
function), `reads.go` (a `Get`'s answer is about its key, at a revision reached; a plain read after
it), `writes.go` (a write's reply revision is reached; errors), `txn.go` (transactions through
`Do` and `Txn`), and `unmet.go`: the requirements the KV contract's users have that the pinned code
violates (each with its issue), which no spec here can give.
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.leasing
public import Spec.PkgInit.go_etcd_io.etcd.client.v3.leasing
public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## What the leasing KV does to the cluster's state (pure) -/

/-- The key an event is about. -/
def evKey : Event → Key
  | .put k _ => k
  | .delete k => k

/-- **A step of the leasing protocol** by `who` with lease prefix `pfx`: no change, or a request of
`who` whose effect on the store is confined to keys under `pfx` (the lease keys: an acquisition's
put, a `"REVOKE"` put, a rescind's delete; every read), or a lease grant or keep-alive of `who`
(its session's). -/
def ProtoStep (pfx : Key) (who : Principal) (σ σ' : State) : Prop :=
  σ' = σ ∨
  ∃ (rq : Req) (res : Resp), Step who rq σ σ' res ∧
    ((∃ evs : List Event, (∀ ev ∈ evs, pfx <+: evKey ev) ∧ σ' = σ.withKV (σ.kv.commit evs)) ∨
     (∃ id ttl, rq = .leaseGrant id ttl) ∨ (∃ id, rq = .leaseKeepAlive id))

/-- **A range answered from the cache**, as far as the pinned code guarantees: at a revision the
cluster has reached (`σ` is a state it has been in), about the requested key only (at most one
key-value, of that key), `more` false, a count of at most one. Nothing is said of the key-value's
record (see the header, 3.). -/
def CachedRange (r : RangeReq) (σ : State) (rev : Nat) (a : RangeAns) : Prop :=
  rev ≤ σ.kv.rev ∧ a.kvs.length ≤ 1 ∧ (∀ kv ∈ a.kvs, kv.key = r.key) ∧ a.more = false ∧
    a.count ≤ 1

/-- **An answer given without the request reaching a member** (a cached `Get`, a transaction
`txnLeasing.eval` answers from the cache, a `Get` answered by a failed acquisition): for a range,
`CachedRange`; for a transaction, a branch `ok` (whichever the cache's comparison picked:
`issues/leasing-evalcmp-missing-key.md`) all of whose operations are ranges, each answered as a
cached range, at a revision reached. Nothing else is answered so. -/
def CachedAns (rq : Req) (σ : State) (res : Resp) : Prop :=
  match rq, res with
  | .range r, .ok (.range rev a) => CachedRange r σ rev a
  | .txn t, .ok (.txn rev ok rs) =>
      rev ≤ σ.kv.rev ∧
      List.Forall₂ (fun (op : RequestOp) (o : OpResp) =>
          ∃ (r : RangeReq) (rv : Nat) (a : RangeAns), op = .range r ∧ o = .range rv a ∧
            CachedRange r σ rv a)
        (if ok then t.success else t.failure) rs
  | _, _ => False

/-- **The request the leasing KV makes of `rq`**: `rq` itself, but a range delete without its
`prevKv` (`deleteRangeRPC` builds `OpDelete(key, WithRange(end))` from the key and the range end
only: the caller's `WithPrevKV` is dropped, and the reply has no previous key-values). -/
def execReq : Req → Req
  | .deleteRange d => if d.rangeEnd = [] then .deleteRange d else .deleteRange { d with prevKv := false }
  | rq => rq

/-- **What the leasing KV may do with the caller's update for `rq`**: `some res`, the request's step
(`execReq`) answering `res`, or a cached answer at an unchanged state; `none`, a step of the
protocol (`ProtoStep`), no answer to the request. -/
def LStep (pfx : Key) (who : Principal) (rq : Req) (σ σ' : State) : Option Resp → Prop
  | some res => Step who (execReq rq) σ σ' res ∨ (σ' = σ ∧ CachedAns rq σ res)
  | none => ProtoStep pfx who σ σ'

/-- A leasing transaction's operations may not be transactions (`gatherOps` appends into a nested
transaction's `thenOps`, which the caller owns read-only: see `LTxn.ThenTriple`). -/
def flatTxn (o : OpM) : Prop :=
  o.t = tTxn → ∀ o' ∈ o.thenOps ++ o.elseOps, o'.t ≠ tTxn

/-! ## Resources -/

/-- A leasing KV's ghost names: opaque. -/
opaque LeasingNames : Type := Unit

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The `COMM` of the caller's update: `Q` of an answer; nothing for a protocol step. -/
def LQ (Q : State → State → Resp → IProp GF) (σ σ' : State) : Option Resp → IProp GF
  | some res => Q σ σ' res
  | none => iprop(True)

/-- **The program's permission for the leasing protocol's steps** (persistent): any `ProtoStep` of
`who` with prefix `pfx`, at any time. `NewKV` takes it; its session monitor, lease monitors and
revocations fire it. -/
def protoUpd (γ : Cluster) (who : Principal) (pfx : Key) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ ∀∀ (σ' : State), ⌜ProtoStep pfx who σ σ'⌝ ∗ etcdState γ σ', COMM True }>)

/-- **Slot (1d)**: `osl` is a read-only slice of session options with which
`concurrency.NewSession(cl, osl...)` meets 1d's spec (the proxy passes none, `sessOptsOk_nil`). -/
opaque sessOptsOk (osl : GoSlice) (cl : Loc) : IProp GF := iprop(True)

/-- **A `*leasingKV`** over a client of `γ` as `who`, lease prefix `pfx` (persistent). -/
opaque isLeasingKV (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) :
  IProp GF := iprop(True)

/-- **The `v3.KV` value `v` meets the leasing contract** (persistent; `lkvAt_methods`). -/
opaque lkvAt (v : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) :
  IProp GF := iprop(True)

/-- **A share `q` of the leasing KV's "open" token** (`Get` and `Do` take a share, the close
function the whole). -/
opaque lkvOpen (γL : LeasingNames) (q : Qp) : IProp GF := iprop(True)

/-- **`cf` is the close function of the leasing KV `γL`** (persistent; `closeFnAt_call`). -/
opaque closeFnAt (cf : GoFunc) (γL : LeasingNames) : IProp GF := iprop(True)

/-- **A leasing transaction under construction** (the `v3.Txn` value `iv`, exclusive), built over
the context `ctx`, holding `st`. -/
opaque ltxnAt (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key) (ctx : GoInterface)
  (st : TxnSt) : IProp GF := iprop(True)

/-! ### Replies -/

/-- What the leasing KV's `Put` returns for the answer `res`: W0's `putReply`, read-only (the
header is shared with the cache). -/
def putReplyL (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.put rev prev) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ m, putRespOwn resp DFrac.discard m ∗
      ⌜m.hdr.revision = W64 rev ∧ m.prevKv = prev.map KeyValueM.ofKV⌝)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What the leasing KV's `Commit` returns for the answer `res`: W0's `txnReply`, read-only (the
header is shared with the cache once a put of a cached key committed). -/
def txnReplyL (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.txn rev ok rs) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ m, txnRespOwn resp DFrac.discard m ∗
      ⌜m.hdr.revision = W64 rev ∧ m.ofResps ok rs⌝)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What the leasing KV's `Do` returns for the answer `res`. -/
def doReplyL (res : Resp) (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface) :
    IProp GF :=
  match res with
  | .ok (.range _ _) => iprop(⌜r.put' = null ∧ r.del' = null ∧ r.txn' = null⌝ ∗ getReply res r.get' err)
  | .ok (.put _ _) => iprop(⌜r.get' = null ∧ r.del' = null ∧ r.txn' = null⌝ ∗ putReplyL res r.put' err)
  | .ok (.deleteRange _ _ _) =>
      iprop(⌜r.put' = null ∧ r.get' = null ∧ r.txn' = null⌝ ∗ deleteReply res r.del' err)
  | .ok (.txn _ _ _) => iprop(⌜r.put' = null ∧ r.get' = null ∧ r.del' = null⌝ ∗ txnReplyL res r.txn' err)
  | .err e => iprop(⌜err = errVal e ∧ r.put' = null ∧ r.get' = null ∧ r.del' = null ∧ r.txn' = null⌝)
  | _ => iprop(False)

/-! ## The leasing contract (`LKV.*Triple`, `LTxn.*Triple`)

W0's KV contract (`client/v3/Api.lean`) with: the caller's update persistent for every request and
over `LStep pfx who rq` (an answer of the request made, `execReq`, or a cached answer; or a
protocol step); an error that settles nothing (no `Q`); the thread token and, for `Get`/`Do`, the
receiver's resource `P` given back. -/

/-- **`Get(ctx, key, opts...)`**: the range `OpGet(key, opts...)` builds: answered by a member
(linearized, or serializable as asked) or from the cache (`CachedAns`). -/
def LKV.GetTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key) : Prop :=
  ∀ (ctx : GoInterface) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ optsAt opts gs ∗ ⌜¬ prefixAndFromKey gs⌝ ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp),
             ⌜LStep pfx who (.range (opGetM key gs).rangeReq) σ σ' r⌝ ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ optsAt opts gs ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ getReply res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Put(ctx, key, val, opts...)`**: the put `OpPut(key, val, opts...)` builds, applied any
number of times (the update persistent); on success, the answer of one application. -/
def LKV.PutTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key) : Prop :=
  ∀ (ctx : GoInterface) (key v : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ optsAt opts gs ∗ ⌜¬ (opPutM key v gs).putPanics⌝ ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp),
             ⌜LStep pfx who (.put (opPutM key v gs).putReq) σ σ' r⌝ ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #v)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ optsAt opts gs ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ putReplyL res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Delete(ctx, key, opts...)`**: the delete `OpDelete(key, opts...)` builds (a range delete
without `prevKv`: `execReq`), applied any number of times. -/
def LKV.DeleteTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key) : Prop :=
  ∀ (ctx : GoInterface) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ optsAt opts gs ∗
      ⌜¬ prefixAndFromKey gs ∧ ¬ (opDeleteM key gs).deletePanics⌝ ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp),
             ⌜LStep pfx who (.deleteRange (opDeleteM key gs).deleteReq) σ σ' r⌝ ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ optsAt opts gs ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ deleteReply res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Do(ctx, op)`**: the request of `op` (of a type at every depth, and a transaction's operations
not themselves transactions: `flatTxn`), as `Get`, `Put`, `Delete` or a transaction's
`Commit`. -/
def LKV.DoTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key) : Prop :=
  ∀ (ctx : GoInterface) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (rq : Req)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ opAt op o ∗ ⌜o.toReq = some rq ∧ flatTxn o⌝ ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), ⌜LStep pfx who rq σ σ' r⌝ ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (Val f) (Val #ctx)) (Val #op))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      P ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ doReplyL res r err) ∨
       ⌜r.put' = null ∧ r.get' = null ∧ r.del' = null ∧ r.txn' = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Txn(ctx)`**: a new leasing transaction over `ctx`, nothing set. -/
def LKV.TxnTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key) : Prop :=
  ∀ (ctx : GoInterface),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who }}
    (App (Val f) (Val #ctx))
  {{ (iv : GoInterface), RET #iv; ltxnAt iv γ who pfx ctx TxnSt.empty }}

/-- **`If(cs...)`** (first of the three; the wrapped client's transaction panics otherwise). -/
def LTxn.IfTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (cs : GoSlice) (ms : List (Option EtcdModel.Compare)),
  {{ ltxnAt (GF := GF) iv γ who pfx ctx st ∗ cmpsAt cs ms ∗
      ⌜st.cif = false ∧ st.cthen = false ∧ st.celse = false⌝ }}
    (App (Val f) (Val #cs))
  {{ (r : GoInterface), RET #r; ⌜r = iv⌝ ∗
      ltxnAt iv γ who pfx ctx
        { st with cif := true, cmps := st.cmps ++ ms.map (fun c => c.getD Compare.zero) } }}

/-- **`Then(ops...)`** (before `Else`, once): the operations' requests appended. They may not be
transactions (`gatherOps` would append into a nested transaction's `thenOps`, beyond its length:
the caller's memory, owned read-only). -/
def LTxn.ThenTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (ops : GoSlice) (os : List OpM) (rs : List RequestOp),
  {{ ltxnAt (GF := GF) iv γ who pfx ctx st ∗ opsAt ops os ∗ ⌜OpM.toReqOps os = some rs⌝ ∗
      ⌜∀ o ∈ os, o.t ≠ tTxn⌝ ∗ ⌜st.cthen = false ∧ st.celse = false⌝ }}
    (App (Val f) (Val #ops))
  {{ (r : GoInterface), RET #r; ⌜r = iv⌝ ∗
      ltxnAt iv γ who pfx ctx { st with cthen := true, sus := st.sus ++ rs } }}

/-- **`Else(ops...)`** (once): as `Then`. -/
def LTxn.ElseTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (ops : GoSlice) (os : List OpM) (rs : List RequestOp),
  {{ ltxnAt (GF := GF) iv γ who pfx ctx st ∗ opsAt ops os ∗ ⌜OpM.toReqOps os = some rs⌝ ∗
      ⌜∀ o ∈ os, o.t ≠ tTxn⌝ ∗ ⌜st.celse = false⌝ }}
    (App (Val f) (Val #ops))
  {{ (r : GoInterface), RET #r; ⌜r = iv⌝ ∗
      ltxnAt iv γ who pfx ctx { st with celse := true, fas := st.fas ++ rs } }}

/-- **`Commit()`**: the transaction so far, answered from the cache (`CachedAns`) or by a member
(applied any number of times), over the context it was built with; the transaction given back. -/
def LTxn.CommitTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (Q : State → State → Resp → IProp GF),
  {{ ltxnAt (GF := GF) iv γ who pfx ctx st ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), ⌜LStep pfx who (.txn st.req) σ σ' r⌝ ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (Val f) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ltxnAt iv γ who pfx ctx st ∗
      threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ txnReplyL res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-! ## Laws -/

def handles_persistent.spec : Prop :=
  (∀ lkv γ who pfx γL, Persistent (isLeasingKV (GF := GF) lkv γ who pfx γL)) ∧
  (∀ v γ who pfx γL, Persistent (lkvAt (GF := GF) v γ who pfx γL)) ∧
  (∀ cf γL, Persistent (closeFnAt (GF := GF) cf γL)) ∧
  (∀ osl cl, Persistent (sessOptsOk (GF := GF) osl cl))

/-- The open token splits and joins. -/
def lkvOpen_split.spec : Prop := ∀ (γL : LeasingNames) (q1 q2 : Qp),
  lkvOpen (GF := GF) γL (q1 + q2) ⊣⊢ lkvOpen γL q1 ∗ lkvOpen γL q2

/-- **The bundle's triples**: the leasing contract, and W0's for `Compact` and `GetStream`. -/
def lkvAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) (q : Qp),
  LKV.GetTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Get")
    (iprop(lkvAt (GF := GF) v γ who pfx γL ∗ lkvOpen γL q)) γ who pfx ∧
  LKV.PutTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Put")
    (lkvAt (GF := GF) v γ who pfx γL) γ who pfx ∧
  LKV.DeleteTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Delete")
    (lkvAt (GF := GF) v γ who pfx γL) γ who pfx ∧
  LKV.DoTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Do")
    (iprop(lkvAt (GF := GF) v γ who pfx γL ∗ lkvOpen γL q)) γ who pfx ∧
  LKV.TxnTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Txn")
    (lkvAt (GF := GF) v γ who pfx γL) γ who pfx ∧
  KV.CompactTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Compact")
    (lkvAt (GF := GF) v γ who pfx γL) γ who ∧
  KV.GetStreamTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"GetStream")
    (lkvAt (GF := GF) v γ who pfx γL) γ who

/-- A `*leasingKV` meets the leasing contract (its methods' specs, `leasingKV__*.lean`). -/
def isLeasingKV_lkvAt.spec : Prop := ∀ lkv γ who pfx γL,
  isLeasingKV (GF := GF) lkv γ who pfx γL ⊢
    lkvAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty) #lkv)
      γ who pfx γL

/-- A leasing transaction's triples. -/
def ltxnAt_methods.spec : Prop := ∀ (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (ctx : GoInterface),
  LTxn.IfTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"If") iv γ who pfx ctx ∧
  LTxn.ThenTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Then") iv γ who pfx ctx ∧
  LTxn.ElseTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Else") iv γ who pfx ctx ∧
  LTxn.CommitTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Commit") iv γ who pfx ctx

/-- **The close function**: with the whole open token (no `Get` running or to come), it cancels
the KV's context and waits for its monitors. -/
def closeFnAt_call.spec : Prop := ∀ (cf : GoFunc) (γL : LeasingNames),
  {{ closeFnAt (GF := GF) cf γL ∗ lkvOpen γL 1 }}
    (App (Val #cf) (Val #()))
  {{ RET #(); True }}

/-- **Slot (1d)**: no session options (the proxy's call). -/
def sessOptsOk_nil.spec : Prop := ∀ cl, ⊢ sessOptsOk (GF := GF) slice.nil cl

end res

end Leasing
end EtcdGrove
end Perennial
