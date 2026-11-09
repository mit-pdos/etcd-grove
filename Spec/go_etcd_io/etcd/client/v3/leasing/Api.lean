/-
# etcd's leasing KV (`client/v3/leasing`): the vocabulary (batch 1e)

`leasing.NewKV(cl, pfx, opts...)` wraps a client's `KV` in a **leasing KV**: a `clientv3.KV` that
caches keys it holds a lease on (a *lease key* `pfx ++ k`, put with its session's lease) and answers
single-key `Get`s of them at revision `0`, and transactions of only such `Get`s, from that cache. The
only user in etcd is the gRPC proxy with `--experimental-leasing-prefix`
(`server/etcdmain/grpc_proxy.go:488`: `client.KV, _, _ = leasing.NewKV(client, prefix)`), which then
serves its KV API from it (`proxy/grpcproxy/kv.go`: `Range`, `Put`, `DeleteRange`, `Txn` through
`Do`, `Compact`; the watch proxy's permission check and `/health` through `Do`/`Get`); and the
integration tests (`tests/integration/clientv3/lease/leasing_test.go`).

## What this KV meets of the KV contract (W0, `client/v3/Api.lean`), plainly

The leasing KV is meant to be indistinguishable from the plain client (its doc: it "serves
linearizable reads from a local cache"). Of W0's KV contract it meets exactly:

* **`Compact`**: `KV.CompactTriple`, unchanged (it calls the wrapped client's).
* **`GetStream`**: `KV.GetStreamTriple`, trivially: it always returns gRPC's `Unimplemented`, an
  error that settles nothing (`indefCall`).

It does **not** meet `KV.GetTriple`, `KV.PutTriple`, `KV.DeleteTriple`, `KV.DoTriple`,
`KV.TxnTriple` (its transactions' `Commit`), for four independent reasons, each true of the pinned
code (`.lake/src/client/leasing`, the fork `a4d2bb17`):

1. **Its writes are not at most once, and may take effect after the call returned.** A `Put` or
   `Delete` of a key it has not cached is committed twice whenever no other client holds the key's
   lease (`issues/leasing-modify-uncached-once.md`); and after an error of its first attempt
   (which may still take effect) it resends the write through `revoke`, so a first attempt may
   land after the resend succeeded and the call returned
   (`nonissues/leasing-write-resend-after-error.md`: `Put(k, v1)` then `Put(k, v2)`, both
   successful, may leave `v1`). So the caller's update for a write is fired any number of times,
   also after the return: it must be **persistent** (`□`), and a client's invariant must be stable
   under a late re-application of every leasing write it issued.
2. **It writes keys the caller did not ask it to**: lease keys under `pfx` (a `Get` puts one, a
   write to a key another client holds puts `"REVOKE"` into it, the lease monitors delete them),
   and its session grants a lease. The program must permit these steps (`protoUpd`, given to
   `NewKV`), and a write's update must accept a protocol step in place of an answer (`LStep`'s
   `none`): `revoke` sends one transaction that is either the caller's write (its guard holds) or
   the `"REVOKE"` put (it does not), known only at its commit.
3. **Its cached answers are serializable at best, not linearizable.** A cached `Get` contacts no
   member and answers with the entry's header, whose revision may be below revisions the caller saw
   since (W0's `req/go_etcd_io_etcd_client_v3_leasing.md`). The protocol fences *writers* by
   revisions, never cached *readers*: with W0's default configuration a session's lease may expire
   while the holder still serves its cache (etcd-io/etcd#19091); with `EnvCfg.leaseExpiry = false`
   that window closes, but a writer that is not a leasing client, the stale header and the bugs
   remain. What the code does guarantee (the old proof's "Theorem 1, cached reads"): for a key
   **never written through this leasing KV**, a cached answer is W0's serializable answer
   (`Step who (.range {r with serializable := true})`: the request's answer at a past state), or a
   plain get's (`issues/leasing-get-failed-acquire-options.md`). For a key written through it the
   cache holds a record computed from the write's arguments (`issues/leasing-update-stale.md`: a
   version or value etcd never had; after a delete, no key-value with a count of one): only its
   shape is guaranteed (`CachedRange`). The keys written through the KV are the program's to know:
   `lkvMarks γL M` (persistent, required by every write for the keys it writes) and `lkvClean γL K`
   (exclusive, the keys never marked; `NewKV` gives all keys). A cached transaction may take the
   wrong branch (`issues/leasing-evalcmp-missing-key.md`) and then skips the other branch's writes;
   its ranges are each answered as above, at their own entry's revision.
4. **Its errors settle nothing**: it returns errors of its own protocol requests (`ErrLeaseNotFound`
   once its session's lease is gone, a permission denied on the lease prefix, its own context's
   cancellation), which are no answer to the caller's request; a write's error may follow an
   attempt that took effect.

Two more differences of shape: a range delete drops the caller's `WithPrevKV` (`deleteRangeRPC`
sends its own `OpDelete(key, WithRange(end))`: `issues/leasing-delete-range-drops-prevkv.md`,
`execReq`); the replies of `Put` and of a transaction are read-only (their header is shared with the
cache, `leaseCache.Update` keeps the pointer: `putReplyL`, `txnReplyL`). Every call but `Compact`,
`Txn` and `If`/`Then`/`Else` takes a thread token for the cache's reader slots (given back;
`GetStream` takes W0's), and `Get`/`Do` take a share of the "open" token (`lkvOpen`), which the close
function takes whole (a `Get` adds a lease monitor to the KV's wait group:
`nonissues/etcd-leasing-get-during-close-waitgroup.md`). A transaction's operations nested at any
depth must have branch slices with no spare capacity (`opCapOk`: `gatherOps` appends into them,
`nonissues/leasing-gatherops-spare-capacity.md`); the proxy's `make`s give it.

**The leasing contract** (`LKV.*Triple`, `LTxn.*Triple`) is W0's contract with: the caller's update
persistent for every request and its step `lstep γL pfx p lo rq` (`Step p rq … lo`, the request leasing
makes, `execReq rq`, a cached answer, or a protocol step; a cached answer's shape-only case naming
the marked keys it answers about); an error that settles nothing; the marks of the keys a write
writes; the shape differences above. It is a weakening: a value meeting W0's KV contract meets it
(`kvAt_lkvAt`, `txnAt_ltxnAt`, with `lkvAlloc` for the ghost names), so a client (the proxy) is
proved once over both kinds of KV.

**What would make it meet W0's contract** (decisions for the user, `notes/specs-only/batch-1e.md`):
the six fixes (branches `leasing-*` of upamanyus/etcd, each in its issue), `put`/`delete` not
resending after an error, and the `WithPrevKV` fix make writes at most once (W0's exclusive update)
and every cached answer serializable; linearizable cached reads need a model of time.

## Vocabulary

* `ProtoStep pfx σ σ'` (pure): a step the leasing protocol takes on its own account: none, a
  request of any principal whose effect on the store is confined to keys under `pfx`, a lease
  grant or keep-alive request, or a lease granted (its session's: 1d's `Concurrency.grantEff`, any
  TTL).
* `CachedRange r σ rev a` (the shape: rev reached, at most one key-value, of the key; `more` false;
  count at most one), `CachedSer who r σ rev a` (W0's serializable answer, up to the lease of a
  keys-only answer), `CachedRange1 who M r σ rev a` (a cached single-key range at revision `0`:
  serializable, a plain get's, or, for a marked key or an invalid sort, the shape), `CachedAns who M
  rq σ res` (ranges and transactions of such ranges).
* `execReq rq`; `reqWrites rq` (the keys a write request writes, at any depth).
* `LStep pfx who M lo rq σ σ' r`; `lstep γL pfx who lo rq σ σ' r := ∃ M, ⌜LStep … M …⌝ ∗
  lkvMarks γL M` (`who` the call's principal, `lo` its auth window, W0's `Step … lo`);
  `LQ Q` (the update's `COMM`).
* `protoUpd γ pfx := etcdPerm γ (ProtoStep pfx)` (W0's permission shape).
* `LeasingNames` (opaque); `isLeasingKV lkv γ who pfx γL` (persistent handle); `lkvAt v γ who pfx γL`
  (persistent bundle); `lkvOpen γL q` (fractional); `closeFnAt cf γL`; `ltxnAt iv γ who pfx γL ctx
  st` (exclusive); `lkvMarks γL M` (persistent), `lkvClean γL K` (exclusive); `opCapOk op`,
  `opsCapOk sl` (persistent).

## Requirement snippets

`examples/specreq/leasing/`: `lifecycle.go` (`NewKV` as the proxy and the tests call it, with
options, the close function), `reads.go`, `writes.go`, `txn.go` (positional responses, nested
transactions, one client over both kinds of KV), and `unmet.go`: the requirements the KV
contract's users have that the pinned code violates (each with its issue), which no spec here gives.
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.leasing
public import Spec.PkgInit.go_etcd_io.etcd.client.v3.leasing
public import Spec.go_etcd_io.etcd.client.v3.Api
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## What the leasing KV does to the cluster's state (pure) -/

/-- **A step of the leasing protocol** with lease prefix `pfx`: no change; a request of any
principal (the protocol's requests run with the caller's context, hence the call's principal:
`acquire`, `revoke`, a `get`'s lease monitor; or with the KV's own context, the client's default
principal: `rescind`, the session) whose events are all on keys under `pfx` (the lease keys: an
acquisition's put, a `"REVOKE"` put, a rescind's delete; every read), or that is a lease grant or
keep-alive (the session's); or a lease granted as 1d's `Concurrency.grantEff` states it (any TTL:
what `NewSession`'s `effIn` asks of the permission).
The principal is not restricted: the protocol's own requests are made for every caller. -/
def ProtoStep (pfx : Key) (σ σ' : State) : Prop :=
  σ' = σ ∨
  (∃ (q : Principal) (rq : Req) (res : Resp), Step q rq σ σ' res ∧
    ((∃ evs : List Event, (∀ ev ∈ evs, pfx <+: ev.key) ∧ σ' = σ.withKV (σ.kv.commit evs)) ∨
     (∃ id ttl, rq = .leaseGrant id ttl) ∨ (∃ id, rq = .leaseKeepAlive id))) ∨
  (∃ ttl : Int, Concurrency.grantEff ttl σ σ')

/-- **The shape of a cached range answer**: at a revision the cluster has reached, about the
requested key only (at most one key-value, of that key), `more` false, a count of at most one. -/
def CachedRange (r : RangeReq) (σ : State) (rev : Nat) (a : RangeAns) : Prop :=
  rev ≤ σ.kv.rev ∧ a.kvs.length ≤ 1 ∧ (∀ kv ∈ a.kvs, kv.key = r.key) ∧ a.more = false ∧
    a.count ≤ 1

/-- Two key-values alike, up to the lease of a keys-only answer (etcd's keys-only read reports
lease `0`, `issues/etcd-range-keys-only-lease.md`; the cache keeps the record's). -/
def kvUpToLease (ko : Bool) (a b : KV) : Prop :=
  if ko then { a with lease := 0 } = { b with lease := 0 } else a = b

/-- **W0's serializable answer** to `r` (the request's answer at a past state, `Step`'s view),
up to the lease of a keys-only answer. -/
def CachedSer (who : Principal) (r : RangeReq) (σ : State) (rev : Nat) (a : RangeAns) : Prop :=
  ∃ a' : RangeAns, Step who (.range { r with serializable := true }) σ σ (.ok (.range rev a')) ∧
    List.Forall₂ (kvUpToLease r.keysOnly) a.kvs a'.kvs ∧ a.more = a'.more ∧ a.count = a'.count

/-- A plain get of `k` (`OpGet(k)`: what a failed acquisition answers). -/
def plainGet (k : Key) : RangeReq := (opGetM k []).rangeReq

/-- **A cached single-key range** (`isBadOp` false: no range end, revision `0` or below): W0's
serializable answer to `r`, or to a plain get of its key; or, for a key marked as written
through the KV (`M`) or a request etcd would refuse for its sort, only the shape. -/
def CachedRange1 (who : Principal) (M : Key → Prop) (r : RangeReq) (σ : State) (rev : Nat)
    (a : RangeAns) : Prop :=
  r.rangeEnd = [] ∧ r.revision ≤ 0 ∧
  (CachedSer who r σ rev a ∨ CachedSer who (plainGet r.key) σ rev a ∨
   ((M r.key ∨ ¬ r.validSort) ∧ CachedRange r σ rev a))

/-- **An answer given without the request reaching a member** (a cached `Get`, a transaction
`txnLeasing.eval` answers from the cache, a `Get` answered by a failed acquisition): a cached
single-key range; or a transaction whose branch `ok` (whichever the cache's comparison picked,
`issues/leasing-evalcmp-missing-key.md`) is all such ranges, each at its entry's revision. -/
def CachedAns (who : Principal) (M : Key → Prop) (rq : Req) (σ : State) (res : Resp) : Prop :=
  match rq, res with
  | .range r, .ok (.range rev a) => CachedRange1 who M r σ rev a
  | .txn t, .ok (.txn rev ok rs) =>
      rev ≤ σ.kv.rev ∧
      List.Forall₂ (fun (op : RequestOp) (o : OpResp) =>
          ∃ (r : RangeReq) (rv : Nat) (a : RangeAns), op = .range r ∧ o = .range rv a ∧
            CachedRange1 who M r σ rv a)
        (if ok then t.success else t.failure) rs
  | _, _ => False

/-- **The request the leasing KV makes of `rq`**: `rq` itself, but a range delete without its
`prevKv` (`deleteRangeRPC` builds `OpDelete(key, WithRange(end))` from the key and the range end
only). -/
def execReq : Req → Req
  | .deleteRange d => if d.rangeEnd = [] then .deleteRange d else .deleteRange { d with prevKv := false }
  | rq => rq

mutual
/-- The keys an operation writes (at any depth, both branches). -/
def opWrites : RequestOp → Key → Prop
  | .put p, k => k = p.key
  | .deleteRange d, k => d.range.mem k
  | .txn _ s f, k => opsWrites s k ∨ opsWrites f k
  | _, _ => False
def opsWrites : List RequestOp → Key → Prop
  | [], _ => False
  | op :: ops, k => opWrites op k ∨ opsWrites ops k
end

/-- **The keys a request writes** (a put's key, a delete's range, a transaction's writes). -/
def reqWrites : Req → Key → Prop
  | .put p => fun k => k = p.key
  | .deleteRange d => d.range.mem
  | .txn t => fun k => opsWrites t.success k ∨ opsWrites t.failure k
  | _ => fun _ => False

/-- **What the leasing KV may do with the caller's update for `rq`** (of the call's principal
`who`, its auth window starting at `lo`: W0's `Step … lo`), the keys marked as written through it
being `M`: `some res`, the request's step (or `execReq`'s) answering `res`, or a cached answer at
an unchanged state; `none`, a step of the protocol, no answer to the request. -/
def LStep (pfx : Key) (who : Principal) (M : Key → Prop) (lo : Nat) (rq : Req) (σ σ' : State) :
    Option Resp → Prop
  | some res => Step who rq σ σ' res lo ∨ Step who (execReq rq) σ σ' res lo ∨
      (σ' = σ ∧ CachedAns who M rq σ res)
  | none => ProtoStep pfx σ σ'

/-! ## Resources -/

/-- A leasing KV's ghost names: opaque. -/
opaque LeasingNames : Type := Unit

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The keys `M` may have been written through the leasing KV `γL`** (persistent). -/
opaque lkvMarks [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γL : LeasingNames) (M : Key → Prop) : IProp GF := iprop(True)

/-- **The keys `K` were never written through the leasing KV `γL`** (exclusive; `NewKV` gives every
key, `lkvClean_mark` gives up some to write them). -/
opaque lkvClean [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γL : LeasingNames) (K : Key → Prop) : IProp GF := iprop(True)

/-- **A step of the leasing KV for the caller's request** (see `LStep`): with the marks of the keys
whose cached answers are only shaped. -/
def lstep (γL : LeasingNames) (pfx : Key) (who : Principal) (lo : Nat) (rq : Req) (σ σ' : State)
    (r : Option Resp) : IProp GF :=
  iprop(∃ M : Key → Prop, ⌜LStep pfx who M lo rq σ σ' r⌝ ∗ lkvMarks γL M)

/-- The `COMM` of the caller's update: `Q` of an answer; nothing for a protocol step. -/
def LQ (Q : State → State → Resp → IProp GF) (σ σ' : State) : Option Resp → IProp GF
  | some res => Q σ σ' res
  | none => iprop(True)

/-- **The program's permission for the leasing protocol's steps** (persistent; W0's `etcdPerm`):
any `ProtoStep` with prefix `pfx`, at any time. -/
def protoUpd (γ : Cluster) (pfx : Key) : IProp GF :=
  etcdPerm γ (ProtoStep pfx)

/-- **A `*leasingKV`** over a client of `γ` as `who`, lease prefix `pfx` (persistent). -/
opaque isLeasingKV [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) :
  IProp GF := iprop(True)

/-- **The `v3.KV` value `v` meets the leasing contract** (persistent; `lkvAt_methods`). -/
opaque lkvAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (v : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) :
  IProp GF := iprop(True)

/-- **A share `q` of the leasing KV's "open" token** (`Get` and `Do` take a share, the close
function the whole). -/
opaque lkvOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γL : LeasingNames) (q : Qp) : IProp GF := iprop(True)

/-- **`cf` is the close function of the leasing KV `γL`** (persistent; `closeFnAt_call`). -/
opaque closeFnAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cf : GoFunc) (γL : LeasingNames) : IProp GF := iprop(True)

/-- **A leasing transaction under construction** (the `v3.Txn` value `iv`, exclusive), built over
the context `ctx` (whose principal is `who`, the call's: as W0's `txnAt`), holding `st`. -/
opaque ltxnAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames)
  (ctx : GoInterface) (st : TxnSt) : IProp GF := iprop(True)

/-- **The `Op` `op`'s nested transactions have branch slices with no spare capacity** (persistent;
`opCapOk_intro`): what `gatherOps`' `append(thenOps, elseOps...)` needs to write no caller memory. -/
opaque opCapOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (op : go_etcd_io.etcd.client.v3.Op) : IProp GF := iprop(True)

/-- A read-only slice of `Op`s each `opCapOk`. -/
def opsCapOk (sl : GoSlice) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.Op, sl ↦*□ vs ∗ [∗list] v ∈ vs, opCapOk v)

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

W0's KV contract (`client/v3/Api.lean`) with: the caller's update persistent for every request, its
step `lstep γL pfx p lo rq` (as W0's: the call's principal `p` from `ctxPrin who ctx p`, `who` the
KV's client's default; a read's auth window `lo` with `authLb γ lo`, `0` for `Put` and `Delete`); a write's marks; an error that settles nothing (no `Q`); the thread
token and, for `Get`/`Do`, the receiver's resource `P` given back. -/

/-- **`Get(ctx, key, opts...)`**: the range `OpGet(key, opts...)` builds: answered by a member
(linearized, or serializable as asked) or from the cache (`CachedAns`). -/
def LKV.GetTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (key : GoString) (opts : GoSlice)
    (gs : List (OpM → OpM)) (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗ ⌜¬ prefixAndFromKey gs⌝ ∗
      threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp),
             lstep γL pfx p lo (.range (opGetM key gs).rangeReq) σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ optsAt opts gs ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ getReply res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Put(ctx, key, val, opts...)`**: the put `OpPut(key, val, opts...)` builds, applied any
number of times, possibly after the return (the update persistent); on success, the answer of one
application. The key marked as written through the KV. -/
def LKV.PutTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (key v : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗ ⌜¬ (opPutM key v gs).putPanics⌝ ∗
      lkvMarks γL (reqWrites (.put (opPutM key v gs).putReq)) ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp),
             lstep γL pfx p 0 (.put (opPutM key v gs).putReq) σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #v)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ optsAt opts gs ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ putReplyL res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Delete(ctx, key, opts...)`**: the delete `OpDelete(key, opts...)` builds (a range delete
without `prevKv`: `execReq`), applied any number of times; its range marked. -/
def LKV.DeleteTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗
      ⌜¬ prefixAndFromKey gs ∧ ¬ (opDeleteM key gs).deletePanics⌝ ∗
      lkvMarks γL (reqWrites (.deleteRange (opDeleteM key gs).deleteReq)) ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp),
             lstep γL pfx p 0 (.deleteRange (opDeleteM key gs).deleteReq) σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ optsAt opts gs ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ deleteReply res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Do(ctx, op)`**: the request of `op` (of a type at every depth, its nested transactions'
branch slices without spare capacity: `opCapOk`), as `Get`, `Put`, `Delete` or a transaction's
`Commit`; its writes marked. -/
def LKV.DoTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM)
    (rq : Req) (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ opAt op o ∗ opCapOk op ∗
      ⌜o.toReq = some rq⌝ ∗ lkvMarks γL (reqWrites rq) ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), lstep γL pfx p lo rq σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (Val f) (Val #ctx)) (Val #op))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      P ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ doReplyL res r err) ∨
       ⌜r.put' = null ∧ r.get' = null ∧ r.del' = null ∧ r.txn' = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **`Txn(ctx)`**: a new leasing transaction over `ctx`, nothing set, of the context's principal
`p` (as W0's `KV.TxnTriple`). -/
def LKV.TxnTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (Val f) (Val #ctx))
  {{ (iv : GoInterface), RET #iv; ltxnAt iv γ p pfx γL ctx TxnSt.empty }}

/-- **`If(cs...)`** (first of the three; the wrapped client's transaction panics otherwise): the
transaction returned (the receiver itself). -/
def LTxn.IfTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (cs : GoSlice) (ms : List (Option EtcdModel.Compare)),
  {{ ltxnAt (GF := GF) iv γ who pfx γL ctx st ∗ cmpsAt cs ms ∗
      ⌜st.cif = false ∧ st.cthen = false ∧ st.celse = false⌝ }}
    (App (Val f) (Val #cs))
  {{ (r : GoInterface), RET #r;
      ltxnAt r γ who pfx γL ctx
        { st with cif := true, cmps := st.cmps ++ ms.map (fun c => c.getD Compare.zero) } }}

/-- **`Then(ops...)`** (before `Else`, once): the operations' requests appended; their nested
transactions' branch slices without spare capacity (`opsCapOk`). -/
def LTxn.ThenTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (ops : GoSlice) (os : List OpM) (rs : List RequestOp),
  {{ ltxnAt (GF := GF) iv γ who pfx γL ctx st ∗ opsAt ops os ∗ opsCapOk ops ∗
      ⌜OpM.toReqOps os = some rs⌝ ∗ ⌜st.cthen = false ∧ st.celse = false⌝ }}
    (App (Val f) (Val #ops))
  {{ (r : GoInterface), RET #r;
      ltxnAt r γ who pfx γL ctx { st with cthen := true, sus := st.sus ++ rs } }}

/-- **`Else(ops...)`** (once): as `Then`. -/
def LTxn.ElseTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (ops : GoSlice) (os : List OpM) (rs : List RequestOp),
  {{ ltxnAt (GF := GF) iv γ who pfx γL ctx st ∗ opsAt ops os ∗ opsCapOk ops ∗
      ⌜OpM.toReqOps os = some rs⌝ ∗ ⌜st.celse = false⌝ }}
    (App (Val f) (Val #ops))
  {{ (r : GoInterface), RET #r;
      ltxnAt r γ who pfx γL ctx { st with celse := true, fas := st.fas ++ rs } }}

/-- **`Commit()`**: the transaction so far, answered from the cache (`CachedAns`) or by a member
(applied any number of times), over the context it was built with; its writes marked; the
transaction given back. -/
def LTxn.CommitTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (lo : Nat) (Q : State → State → Resp → IProp GF),
  {{ ltxnAt (GF := GF) iv γ who pfx γL ctx st ∗ authLb γ lo ∗ lkvMarks γL (reqWrites (.txn st.req)) ∗
      threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), lstep γL pfx who lo (.txn st.req) σ σ' r ∗
             etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (Val f) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ltxnAt iv γ who pfx γL ctx st ∗
      threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ txnReplyL res resp err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-! ## Laws -/

def handles_persistent.spec : Prop :=
  (∀ lkv γ who pfx γL, Persistent (isLeasingKV (GF := GF) lkv γ who pfx γL)) ∧
  (∀ v γ who pfx γL, Persistent (lkvAt (GF := GF) v γ who pfx γL)) ∧
  (∀ cf γL, Persistent (closeFnAt (GF := GF) cf γL)) ∧
  (∀ γL M, Persistent (lkvMarks (GF := GF) γL M)) ∧
  (∀ op, Persistent (opCapOk (GF := GF) op))

/-- The open token splits and joins. -/
def lkvOpen_split.spec : Prop := ∀ (γL : LeasingNames) (q1 q2 : Qp),
  lkvOpen (GF := GF) γL (q1 + q2) ⊣⊢ lkvOpen γL q1 ∗ lkvOpen γL q2

/-- **Marks**: none needed; fewer than given; joined. -/
def lkvMarks_none.spec : Prop := ∀ γL, ⊢ lkvMarks (GF := GF) γL (fun _ => False)
def lkvMarks_mono.spec : Prop := ∀ γL (M M' : Key → Prop), (∀ k, M k → M' k) →
  lkvMarks (GF := GF) γL M' ⊢ lkvMarks γL M
def lkvMarks_join.spec : Prop := ∀ γL (M M' : Key → Prop),
  lkvMarks (GF := GF) γL M ∗ lkvMarks γL M' ⊢ lkvMarks γL (fun k => M k ∨ M' k)

/-- **Clean keys**: split over disjoint sets; a clean key is never marked; give up clean keys to
mark them. -/
def lkvClean_split.spec : Prop := ∀ γL (K K' : Key → Prop), (∀ k, ¬ (K k ∧ K' k)) →
  lkvClean (GF := GF) γL (fun k => K k ∨ K' k) ⊣⊢ lkvClean γL K ∗ lkvClean γL K'
def lkvClean_marks.spec : Prop := ∀ γL (K M : Key → Prop),
  lkvClean (GF := GF) γL K ∗ lkvMarks γL M ⊢ ⌜∀ k, ¬ (K k ∧ M k)⌝
def lkvClean_mark.spec : Prop := ∀ γL (K M : Key → Prop),
  lkvClean (GF := GF) γL K ⊢ |==> lkvClean γL (fun k => K k ∧ ¬ M k) ∗ lkvMarks γL M

/-- **Ghost names for a KV that is not a leasing one** (to use a plain KV through the leasing
contract, `kvAt_lkvAt`). -/
def lkvAlloc.spec : Prop :=
  ⊢ |==> ∃ γL : LeasingNames, lkvOpen (GF := GF) γL 1 ∗ lkvClean γL (fun _ => True)

/-- **What `opCapOk` needs**: an `Op` that is not a transaction, or a transaction whose branch
slices have no spare capacity and whose operations are `opCapOk`. -/
def opCapOk_intro.spec : Prop := ∀ (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  opAt (GF := GF) op o ∗
    (⌜o.t ≠ tTxn⌝ ∨
     (⌜op.thenOps'.cap = op.thenOps'.len ∧ op.elseOps'.cap = op.elseOps'.len⌝ ∗
       opsCapOk op.thenOps' ∗ opsCapOk op.elseOps'))
  ⊢ opCapOk op

/-- **The bundle's triples**: the leasing contract, and W0's for `Compact` and `GetStream`. -/
def lkvAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) (q : Qp),
  LKV.GetTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Get")
    (iprop(lkvAt (GF := GF) v γ who pfx γL ∗ lkvOpen γL q)) γ who pfx γL ∧
  LKV.PutTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Put")
    (lkvAt (GF := GF) v γ who pfx γL) γ who pfx γL ∧
  LKV.DeleteTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Delete")
    (lkvAt (GF := GF) v γ who pfx γL) γ who pfx γL ∧
  LKV.DoTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Do")
    (iprop(lkvAt (GF := GF) v γ who pfx γL ∗ lkvOpen γL q)) γ who pfx γL ∧
  LKV.TxnTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Txn")
    (lkvAt (GF := GF) v γ who pfx γL) γ who pfx γL ∧
  KV.CompactTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Compact")
    (lkvAt (GF := GF) v γ who pfx γL) γ who ∧
  KV.GetStreamTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"GetStream")
    (lkvAt (GF := GF) v γ who pfx γL) γ who

/-- A `*leasingKV` meets the leasing contract (its methods' specs, `leasingKV__*.lean`). -/
def isLeasingKV_lkvAt.spec : Prop := ∀ lkv γ who pfx γL,
  isLeasingKV (GF := GF) lkv γ who pfx γL ⊢
    lkvAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty) #lkv)
      γ who pfx γL

/-- **A value meeting W0's KV contract meets the leasing contract** (every `Step` is an `LStep`; the
marks, open token and thread token framed; a definite error's `Q` dropped), for any prefix and
ghost names. -/
def kvAt_lkvAt.spec : Prop := ∀ v γ who pfx γL,
  kvAt (GF := GF) v γ who ⊢ lkvAt v γ who pfx γL

/-- **A W0 transaction is a leasing one** (its `Commit`'s update restricted to `Step`). -/
def txnAt_ltxnAt.spec : Prop := ∀ iv γ who pfx γL ctx st,
  txnAt (GF := GF) iv γ who ctx st ⊢ ltxnAt iv γ who pfx γL ctx st

/-- A leasing transaction's triples. -/
def ltxnAt_methods.spec : Prop := ∀ (iv : GoInterface) (γ : Cluster) (who : Principal) (pfx : Key)
    (γL : LeasingNames) (ctx : GoInterface),
  LTxn.IfTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"If") iv γ who pfx γL ctx ∧
  LTxn.ThenTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Then") iv γ who pfx γL ctx ∧
  LTxn.ElseTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Else") iv γ who pfx γL ctx ∧
  LTxn.CommitTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Commit") iv γ who pfx γL ctx

/-- **The close function**: with the whole open token (no `Get` running or to come), it cancels
the KV's context and waits for its monitors. -/
def closeFnAt_call.spec : Prop := ∀ (cf : GoFunc) (γL : LeasingNames),
  {{ closeFnAt (GF := GF) cf γL ∗ lkvOpen γL 1 }}
    (App (Val #cf) (Val #()))
  {{ RET #(); True }}

end res

end Leasing
end EtcdGrove
end Perennial
