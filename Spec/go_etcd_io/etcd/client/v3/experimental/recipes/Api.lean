/-
# etcd's client recipes: the vocabulary (batch 1f)

`go.etcd.io/etcd/client/v3/experimental/recipes`: a barrier, a double barrier, a FIFO queue, a
priority queue and a readers-writer mutex, each a few KV calls of the client (`client/v3/Api.lean`,
batch W0) and a watch (batch 1b) over keys of the cluster `γ` (`api/v3/State.lean`'s `etcdState`).
Their users are etcd's integration tests (`tests/integration/clientv3/experimental/recipes`); no
other code of the pinned etcd, raft, Kubernetes or `examples/` imports the package.

## How the recipes reach the cluster's state

A recipe sends requests over the client's KV and reads a watch. Every KV call takes an atomic update
over `etcdState γ`, which the program keeps in its own invariant (`notes/specs-only/top.md`), so a
recipe needs its caller's updates:

* **The operation that changes what the recipe is about takes the caller's atomic update**, in the
  shape of W0's KV contract (TaDa): the update is fired once, at the request that linearizes the
  operation, with the caller's `Q`, and every other request the operation sends either reads or
  does nothing (a compare that failed, a refusal), which the recipe absorbs by aborting the update
  and retrying. These are `Barrier.Hold` and `Release`, `Queue.Enqueue` and `Dequeue`,
  `PriorityQueue.Enqueue` and `Dequeue`, the creation of the `RWMutex`'s key in `Lock`/`RLock`
  and its deletion in `Unlock`/`RUnlock`, `RemoteKV.Put`/`Delete` and the key helpers.
* **Reads go through `etcdPeek γ`** (persistent): the caller's permission to look at the state
  without changing it. From it a recipe makes the persistent update of each `Get` (a read's step
  leaves the state unchanged, `Model.lean`'s `kvStep`) and learns `etcdLb γ σ` of the state it read.
  Every caller can give it (its invariant holds `etcdState`; the update closes it unchanged).
* **The double barrier's writes are a guarded permission** (`dbPerm`, persistent), not one update
  per call: `Enter` and `Leave` send up to three writes each (a waiter key, the `ready` key, their
  own key's deletion), none of which is the barrier's linearization; the permission lists them, one
  for `Enter` and one for `Leave`, the `ready` key's put guarded by a revision where `count` waiters
  were present, its delete by one where exactly one was. The caller's invariant must be stable
  under the steps of the permissions it gives.
* **What a waiting call learns is a fact of the cluster's history**: `etcdLb γ σ` with a pure
  condition on `σ.kv` (the whole history is kept, `Model.lean`), anchored at a state `σ0` the caller
  passes (`etcdLb γ σ0`: "after the call started"). Combined with the caller's invariant through
  `etcdLb_reach` (the history only grows), such a fact says what happened between the call's start
  and its return: the barrier key deleted (`goneAt`), the `ready` key put, every earlier lock key
  gone (`rwHeld`).

**Contexts.** Every KV call the recipes make passes `context.TODO()` (or the handle's `ctx` field,
a `context.TODO()`), which meets W0's `Context.ctxOk` and `ctxPrin ctx who` for any principal
(`ctxPrin_todo`); the watches pass `context.WithCancel(context.Background())` (`Context.WithCancel`,
`ctxPrin_background`, `ctxPrin_child`). So no recipe spec takes a context: the handles' realizations
hold `ctxOk` and `ctxPrin` of their `ctx` field for the client's principal.

## Pure vocabulary

* `decStr`, `padDec w`: Go's `%v`/`%d` and `%0wd` of an integer; `uniqueKeyIn p k`: `k` is
  `p/<UnixNano>` (`newUniqueKV`); `seqKey p n`: `p/<n, 16 digits>` (`newSequentialKV`);
  `pqPrefix key pr`: the priority queue's prefix for priority `pr`. `pfxRange p`: the keys
  `WithPrefix()` reads.
* The requests the recipes send: `putNewReq` (create a key if absent: `putNewKV`), `deleteRevReq`
  (delete a key at a mod revision: `deleteRevKey`), `seqPutReq` (`newSequentialKV`'s guarded put),
  `putReq0`, `delReq`; `txnSucceeded`, `txnCmpFailed` (a transaction's answer).
* What the recipes guarantee, as facts of a store or a history: `frontByRev` (the queue's front: the
  least mod revision), `frontByKey` (the priority queue's front: every key before it arrived after a
  given revision), `goneAt` (a key absent, or deleted, at a revision), `rwHeld` (no key of a range
  below a revision: the mutex's acquisition), `storeCount`, `readyPutAt`, `createdAt`.
* The watch's events: `WatchEv` (a revision and an `Event`), `watchHist h rg rev` (every event of
  the range `rg` in the history `h` from revision `rev` on, in order), `WatchEv.typ`, `WatchEv.kvM`
  (the `mvccpb.Event` a watch delivers for it), `matchCount` (`waitEvents`' greedy match).
* `RecipeErr`: the package's error variables (`ErrKeyExists`, ...); `RKSt`: a `RemoteKV`'s fields;
  `okOrErr`, `putNewRet`, `deleteRevRet`: what a call returns for its request's answer.

## Resources

* `etcdPeek γ` (def, persistent): see above.
* `recipeErr e` (a Go value): the package's error `e`; laws `recipeErr_ne` (not `nil`, distinct
  from one another and from `errVal`), `init.spec` (the package variables hold them, read-only).
* `rkOwn rk γ who st` (exclusive): the `*RemoteKV` `rk` with fields `st` (`kv` a `kvAt` value of
  `γ` as `who` while `st.live`, `nil` once deleted). Intended realization: the struct's points-to,
  `kvAt` of the field. `ekOwn ek` the same of an `*EphemeralKV`'s embedded `RemoteKV`.
* `barrierAt b c γ who key`, `queueAt q c γ who kp`, `pqueueAt q c γ who key` (persistent): the
  handle's fields (read-only after construction: the client `c` with `isClient c γ who`, a
  `context.TODO()`, the key or prefix). Intended realization: the struct's persistent points-to.
* `dbOwn b γ who key count id my`, `rwmOwn m γ who id pfx my` (exclusive: `Enter`/`Lock` write
  `myKey`): the session's client and lease `id`, the key and count or prefix, and `myKey`'s
  `ekOwn` (`my`: `none` while `nil`).
* `dbPerm γ who key count id leave` (def, persistent): the double barrier's writes (`dbWrite`),
  `Enter`'s or `Leave`'s: a program that never leaves never permits the `ready` key's delete.
* **Slots of other batches** (defined here so that the statements type-check; the owner's own
  predicate replaces each at integration, `notes/specs-only/req/`):
  * `sessionAt s γ who id` (**1d**, persistent): the `*concurrency.Session` `s` of a client of `γ`
    as `who` with lease `id` (`s.Client()` returns a client `c` with `isClient c γ who`, `s.Lease()`
    returns `id`). Nothing about the lease's liveness: it may expire at any time (`Model.lean`).
  * `watchChanAt wc γ rg rev seen` (**1b**, exclusive): the consumer of a `WatchChan` watching the
    range `rg` from revision `rev`, having received the events `seen`; `watchChanAt_recv` is what a
    receive gives (an error response, or events extending `seen` within the cluster's history from
    `rev`, or the channel closed: any time). `watchEvOwn p e` (**1b/3h**, persistent): the
    `*mvccpb.Event` `p` delivered for `e` (`watchEvOwn_unfold`).

## Laws

`handles_persistent`, `recipeErr_ne`, `recipeErr_fresh`, `errorsIs_recipeErr`, `init.spec`, `ekOwn` (def), `watchChanAt_recv` (slot, 1b),
`watchEvOwn_unfold` (slot, 1b/3h).

## Requirement snippets

`examples/specreq/recipes/`: `barrier.go` (hold, double hold refused, a waiter released only after
a release, a waiter on an absent key), `queue.go` (FIFO with one producer and one consumer, every
item dequeued once, a dequeue whose watch closes errs), `pqueue.go` (priority order with the items
enqueued before the dequeues), `rwmutex.go` (a writer, or a reader, acquires only once the older
writer's key is gone), `doublebarrier.go` (`Enter` returns once the `ready` key was put; `nil` only
with fewer than `count` waiters at its first read; `Leave` after `Enter`), `watch.go` (`WaitEvents`
returns the first delete after a revision).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api
public import Spec.PkgInit.go_etcd_io.etcd.client.v3.experimental.recipes
public import GeneratedProof.go_etcd_io.etcd.client.v3.experimental.recipes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## Keys -/

/-- The decimal digits of `n` (Go's `%d` of a non-negative integer). -/
def digitsStr (n : Nat) : GoString := (Nat.toDigits 10 n).map (fun c => W8 (c.toNat : Int))

/-- Go's `%v` (and `%d`) of an integer. -/
def decStr (n : Int) : GoString :=
  if n < 0 then [W8 45] ++ digitsStr n.natAbs else digitsStr n.toNat

/-- Go's `%0wd` of an integer: padded with zeros to width `w`, the sign counted. -/
def padDec (w : Nat) (n : Int) : GoString :=
  let d := digitsStr n.natAbs
  if n < 0 then [W8 45] ++ List.replicate (w - 1 - d.length) (W8 48) ++ d
  else List.replicate (w - d.length) (W8 48) ++ d

/-- `k` is a key `newUniqueKV(prefix p)` may choose: `fmt.Sprintf("%s/%v", p, time.Now().UnixNano())`. -/
def uniqueKeyIn (p k : GoString) : Prop := ∃ n : Int, k = p ++ go!"/" ++ decStr n

/-- `newSequentialKV`'s key number `n` under `p`: `fmt.Sprintf("%s/%016d", p, n)`. -/
def seqKey (p : GoString) (n : Int) : GoString := p ++ go!"/" ++ padDec 16 n

/-- `newSequentialKV`'s bookkeeping key for `p`: `"__" + p`. -/
def seqBase (p : GoString) : GoString := go!"__" ++ p

/-- The priority queue's prefix for priority `pr` (`q.key` is `key + "/"`):
`fmt.Sprintf("%s%05d", q.key, pr)`. -/
def pqPrefix (key : GoString) (pr : w16) : GoString := key ++ go!"/" ++ padDec 5 (uint.Z pr)

/-- The keys `Get(p, WithPrefix())` reads. -/
def pfxRange (p : GoString) : KeyRange := (opGetM p [withPrefixM]).rangeReq.range

/-- The double barrier's waiter prefix and `ready` key. -/
def waitersPfx (key : GoString) : GoString := key ++ go!"/waiters"
def readyKey (key : GoString) : GoString := key ++ go!"/ready"

/-! ## The requests the recipes send -/

/-- A put with no option but the lease (`OpPut(k, v, WithLease(lease))`). -/
def putReq0 (k v : GoString) (lease : Int) : PutReq :=
  { key := k, value := v, lease := lease, prevKv := false, ignoreValue := false, ignoreLease := false }

/-- A single key's delete (`OpDelete(k)`). -/
def delReq (k : GoString) : DeleteReq := { key := k, rangeEnd := [], prevKv := false }

/-- `putNewKV(kv, k, v, lease)`'s transaction: `If(Version(k) = 0).Then(OpPut(k, v, WithLease(lease)))`. -/
def putNewReq (k v : GoString) (lease : Int) : Req :=
  .txn { compare := [{ result := cmpEqual, target := cmpTVersion, key := k, rangeEnd := [],
                       targetUnion := .version 0 }],
         success := [.put (putReq0 k v lease)], failure := [] }

/-- `deleteRevKey(kv, k, rev)`'s transaction: `If(ModRevision(k) = rev).Then(OpDelete(k))`. -/
def deleteRevReq (k : GoString) (rev : Int) : Req :=
  .txn { compare := [{ result := cmpEqual, target := cmpTMod, key := k, rangeEnd := [],
                       targetUnion := .modRevision rev }],
         success := [.deleteRange (delReq k)], failure := [] }

/-- `newSequentialKV`'s transaction: `If(ModRevision(base) < bound).Then(OpPut(base, ""),
OpPut(k, v))` (`bound` is the `Get`'s header revision plus one). -/
def seqPutReq (base k v : GoString) (bound : Int) : Req :=
  .txn { compare := [{ result := cmpLess, target := cmpTMod, key := base, rangeEnd := [],
                       targetUnion := .modRevision bound }],
         success := [.put (putReq0 base [] 0), .put (putReq0 k v 0)], failure := [] }

/-- A transaction's answer: its comparisons held. -/
def txnSucceeded (res : Resp) : Prop := ∃ R rs, res = .ok (.txn R true rs)

/-- A transaction's answer: its comparisons failed (with no `Else`, nothing happened). -/
def txnCmpFailed (res : Resp) : Prop := ∃ R rs, res = .ok (.txn R false rs)

/-! ## What the recipes guarantee, as facts of stores and histories -/

/-- `s` holds `n` keys of the range `rng`. -/
def storeCount (s : EtcdModel.Store) (rng : KeyRange) (n : Nat) : Prop :=
  ∃ l, s.rangeKVs rng l ∧ l.length = n

/-- **The queue's front**: `k` is a key of `rng` in `s` with the least mod revision among them. -/
def frontByRev (rng : KeyRange) (s : EtcdModel.Store) (k : Key) (kr : KeyRec) : Prop :=
  rng.mem k ∧ s k = some kr ∧
    ∀ k' kr', rng.mem k' → s k' = some kr' → kr.modRev ≤ kr'.modRev

/-- **The priority queue's front, as of revision `r0`**: `k` is a key of `rng` in `s`, and every key of
`rng` in `s` before it in key order was written after `r0` (with `r0` the call's start: `k` is the
first in key order among the items present when the call started). -/
def frontByKey (rng : KeyRange) (s : EtcdModel.Store) (r0 : Nat) (k : Key) (kr : KeyRec) : Prop :=
  rng.mem k ∧ s k = some kr ∧
    ∀ k' kr', rng.mem k' → s k' = some kr' → keyLt k' k → r0 < kr'.modRev

/-- **The key `k` is gone at revision `r`** of the history `h`: absent from the store there, or
deleted by one of that revision's events (a revision may delete and re-put a key, in sibling
nested transactions: `issues/etcd-txn-check-intervals-sibling.md`, which a watch reports as a
delete followed by a put). -/
def goneAt (h : KVHist) (k : Key) (r : Nat) : Prop :=
  h.storeAt r k = none ∨ Event.delete k ∈ h.eventsAt r

/-- **The readers-writer mutex's acquisition**: every key of `rng` in `s` has a mod revision at
least `R` (the acquirer's key's creation): every key queued before it is gone (or rewritten). -/
def rwHeld (rng : KeyRange) (R : Nat) (s : EtcdModel.Store) : Prop :=
  ∀ k kr, rng.mem k → s k = some kr → R ≤ kr.modRev

/-- The key `k` was created at revision `R` of the history `h`, with value `v` and lease `lease`
(the event of revision `R` that put it, as the first version of the key). -/
def createdAt (h : KVHist) (k v : GoString) (lease : Int) (R : Nat) : Prop :=
  Event.put k { createRev := R, modRev := R, version := 1, value := v, lease := lease } ∈ h.eventsAt R

/-- The double barrier's `ready` key was put at revision `r` of the history `h`. -/
def readyPutAt (h : KVHist) (key : GoString) (r : Nat) : Prop :=
  ∃ kr, Event.put (readyKey key) kr ∈ h.eventsAt r

/-! ## Watch events -/

/-- An event's key. -/
def eventKey : Event → Key
  | .put k _ => k
  | .delete k => k

/-- **An event as a watch delivers it**: the revision and the change. -/
structure WatchEv where
  rev : Nat
  ev : Event

/-- `mvccpb.Event_EventType`: `PUT` (0), `DELETE` (1). -/
def evPut : w32 := W32 0
def evDelete : w32 := W32 1

def WatchEv.typ (e : WatchEv) : w32 :=
  match e.ev with
  | .put _ _ => evPut
  | .delete _ => evDelete

def WatchEv.key (e : WatchEv) : Key := eventKey e.ev

/-- The `Kv` of the `mvccpb.Event` delivered for `e`: a put's new record; a delete's key with its
revision as mod revision, the rest zero. -/
def WatchEv.kvM (e : WatchEv) : KeyValueM :=
  match e.ev with
  | .put k kr => KeyValueM.ofKV (KV.ofRec k kr)
  | .delete k => { key := k, createRevision := W64 0, modRevision := W64 e.rev, version := W64 0,
                   value := [], lease := W64 0 }

/-- **Every event of the range `rg` in the history `h` from revision `rev` on**, in order. -/
def watchHist (h : KVHist) (rg : KeyRange) (rev : Nat) : List WatchEv :=
  ((List.range (h.rev + 1)).filter (fun r => decide (rev ≤ r))).flatMap
    (fun r => ((h.eventsAt r).filter (fun e => decide (rg.mem (eventKey e)))).map
      (fun e => ({ rev := r, ev := e } : WatchEv)))

/-- `waitEvents`' greedy match of the types `ts` over the events `es`: how many it matched. -/
def matchCount (ts : List w32) (es : List WatchEv) : Nat :=
  es.foldl (fun i e => if ts[i]? = some e.typ then i + 1 else i) 0

/-! ## Errors and objects -/

/-- The package's error variables. -/
inductive RecipeErr where
  | keyExists | waitMismatch | tooManyClients | noWatcher | watchClosed

/-- A `RemoteKV`'s fields: live (its `kv` set) or deleted (`kv` `nil`), its key, the revision it
was created at, its value. -/
structure RKSt where
  live : Bool
  key : GoString
  rev : w64
  val : GoString

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The Go value of the package's error `e`** (`errors.New(...)`, `ErrKeyExists` for `.keyExists`). -/
opaque recipeErr (e : RecipeErr) : GoInterface := GoInterface.nil

/-- Not `nil`, distinct from one another, and none of etcd's errors. -/
def recipeErr_ne.spec : Prop :=
  (∀ e, recipeErr e ≠ GoInterface.nil) ∧ (∀ e e', recipeErr e = recipeErr e' → e = e') ∧
  (∀ e e', recipeErr e ≠ errVal e')

/-- What a single KV call returns for the answer `res`: `nil` for a success, etcd's error for an
error answer. -/
def okOrErr (res : Resp) (err : GoInterface) : Prop :=
  (∃ b, res = .ok b ∧ err = GoInterface.nil) ∨ (∃ e, res = .err e ∧ err = errVal e)

/-- What `putNewKV` returns for its transaction's answer `res`: the header's revision on success,
`ErrKeyExists` when the key existed, etcd's error otherwise (`0` but on success). -/
def putNewRet (res : Resp) (rev : w64) (err : GoInterface) : Prop :=
  (∃ R rs, res = .ok (.txn R true rs) ∧ err = GoInterface.nil ∧ rev = W64 R) ∨
  (txnCmpFailed res ∧ err = recipeErr .keyExists ∧ rev = W64 0) ∨
  (∃ e, res = .err e ∧ err = errVal e ∧ rev = W64 0)

/-- What `deleteRevKey` returns for its transaction's answer `res`. -/
def deleteRevRet (res : Resp) (ok : Bool) (err : GoInterface) : Prop :=
  (txnSucceeded res ∧ ok = true ∧ err = GoInterface.nil) ∨
  (txnCmpFailed res ∧ ok = false ∧ err = GoInterface.nil) ∨
  (∃ e, res = .err e ∧ ok = false ∧ err = errVal e)

end errs

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The caller's permission to look at the cluster's state** (persistent): an atomic update that
leaves it unchanged. Each recipe's reads are made of it. -/
def etcdPeek (γ : Cluster) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ ∀∀ (σ' : State), ⌜σ' = σ⌝ ∗ etcdState γ σ', COMM True }>)

/-- **A `*RemoteKV`** with fields `st` (exclusive). -/
opaque rkOwn (rk : Loc) (γ : Cluster) (who : Principal) (st : RKSt) : IProp GF := iprop(True)

/-- An `*EphemeralKV`: its embedded `RemoteKV`. -/
def ekOwn (ek : Loc) (γ : Cluster) (who : Principal) (st : RKSt) : IProp GF :=
  rkOwn (ek.[go_etcd_io.etcd.client.v3.experimental.recipes.EphemeralKV, go!"RemoteKV"]) γ who st

/-- **A `*Barrier`** on `key`, over the client `c` (persistent). -/
opaque barrierAt (b c : Loc) (γ : Cluster) (who : Principal) (key : GoString) : IProp GF := iprop(True)

/-- **A `*Queue`** under the prefix `kp` (persistent). -/
opaque queueAt (q c : Loc) (γ : Cluster) (who : Principal) (kp : GoString) : IProp GF := iprop(True)

/-- **A `*PriorityQueue`** on `key` (its keys under `key/`; persistent). -/
opaque pqueueAt (q c : Loc) (γ : Cluster) (who : Principal) (key : GoString) : IProp GF := iprop(True)

/-- **A `*DoubleBarrier`** on `key` for `count` processes, over a session with lease `id`
(exclusive); `my`: its `myKey` (`none`: `nil`). -/
opaque dbOwn (b : Loc) (γ : Cluster) (who : Principal) (key : GoString) (count : w64) (id : w64)
  (my : Option RKSt) : IProp GF := iprop(True)

/-- **A `*RWMutex`** on the prefix `pfx` (with its `/`), over a session with lease `id` (exclusive);
`my`: its `myKey`. -/
opaque rwmOwn (m : Loc) (γ : Cluster) (who : Principal) (id : w64) (pfx : GoString)
  (my : Option RKSt) : IProp GF := iprop(True)

/-- **Slot (1d)**: the `*concurrency.Session` `s` of a client of `γ` as `who`, with lease `id`
(persistent). -/
opaque sessionAt (s : Loc) (γ : Cluster) (who : Principal) (id : w64) : IProp GF := iprop(True)

/-- **Slot (1b)**: the consumer of a `WatchChan` on the range `rg` from revision `rev`, having
received the events `seen` (exclusive). -/
opaque watchChanAt (wc : Loc) (γ : Cluster) (rg : KeyRange) (rev : Nat) (seen : List WatchEv) :
  IProp GF := iprop(True)

/-- **Slot (1b, 3h)**: the `*mvccpb.Event` `p` delivered for `e` (persistent, read-only). -/
opaque watchEvOwn (p : Loc) (e : WatchEv) : IProp GF := iprop(True)

/-- **The double barrier's writes** at the state `σ`, `Enter`'s (`leave = false`): a waiter key under
`key/waiters` with the session's lease, created if absent; the delete of a waiter key (its own, past
the `count`-th); the put of `key/ready` at a state whose history had `count` waiters at some
revision. `Leave`'s (`leave = true`): the delete of a waiter key (its own); the delete of `key/ready`
at a state whose history had exactly one waiter at some revision. The guards are what the code
knows when it writes; they constrain a program that uses a key for one round (its history has no
waiter before the round), not one that reuses it. -/
def dbWrite (key : GoString) (count : Int) (id : Int) (leave : Bool) (σ : State) (rq : Req) : Prop :=
  (∃ k, (pfxRange (waitersPfx key)).mem k ∧ rq = .deleteRange (delReq k)) ∨
  (leave = false ∧ ∃ k, uniqueKeyIn (waitersPfx key) k ∧ rq = putNewReq k [] id) ∨
  (leave = false ∧ rq = .put (putReq0 (readyKey key) [] 0) ∧
    ∃ r n, r ≤ σ.kv.rev ∧ storeCount (σ.kv.storeAt r) (pfxRange (waitersPfx key)) n ∧ count ≤ n) ∨
  (leave = true ∧ rq = .deleteRange (delReq (readyKey key)) ∧
    ∃ r, r ≤ σ.kv.rev ∧ storeCount (σ.kv.storeAt r) (pfxRange (waitersPfx key)) 1)

/-- **The caller's permission for the double barrier's writes** (persistent; see the header):
`Enter`'s (`leave = false`) or `Leave`'s (`leave = true`). -/
def dbPerm (γ : Cluster) (who : Principal) (key : GoString) (count : w64) (id : w64) (leave : Bool) :
    IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ ∀∀ (rq : Req) (σ' : State) (res : Resp),
         ⌜dbWrite key (sint.Z count) (sint.Z id) leave σ rq ∧ Step who rq σ σ' res⌝ ∗ etcdState γ σ',
       COMM True }>)

def handles_persistent.spec : Prop :=
  (∀ b c γ who key, Persistent (barrierAt (GF := GF) b c γ who key)) ∧
  (∀ q c γ who kp, Persistent (queueAt (GF := GF) q c γ who kp)) ∧
  (∀ q c γ who key, Persistent (pqueueAt (GF := GF) q c γ who key)) ∧
  (∀ s γ who id, Persistent (sessionAt (GF := GF) s γ who id)) ∧
  (∀ p e, Persistent (watchEvOwn (GF := GF) p e))

/-- **Slot (1b, 3h)**: what a delivered event holds: its type and its `Kv`, read-only. -/
def watchEvOwn_unfold.spec : Prop := ∀ (p : Loc) (e : WatchEv),
  watchEvOwn (GF := GF) p e ⊢
    ∃ kvp : Loc, p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Type"] ↦□ e.typ ∗
      p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Kv"] ↦□ kvp ∗ keyValueOwn kvp DFrac.discard e.kvM

/-- **Slot (1b): receiving from a watch channel.** The channel closed (at any time: the context
canceled, the client closed); or a response whose `Err()` is not `nil` (`closeErr`, a compaction,
a cancelation); or a response with no error whose events `es` extend `seen` within the cluster's
history of the range from `rev` (every event, in order, none skipped: a prefix of `watchHist`). -/
def watchChanAt_recv.spec : Prop := ∀ (wc : Loc) (γ : Cluster) (rg : KeyRange) (rev : Nat)
    (seen : List WatchEv),
  {{ watchChanAt (GF := GF) wc γ rg rev seen }}
    (App (Val (chan.receive go_etcd_io.etcd.client.v3.WatchResponse.ty)) (Val #wc))
  {{ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool), RET (PairV #v #ok);
      ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ watchChanAt wc γ rg rev seen ∗
        ⌜v.closeErr' ≠ GoInterface.nil ∨ v.CompactRevision' ≠ W64 0 ∨ v.Canceled' = true⌝) ∨
      (⌜ok = true ∧ v.closeErr' = GoInterface.nil ∧ v.CompactRevision' = W64 0 ∧
          v.Canceled' = false⌝ ∗
        ∃ (es : List WatchEv) (ps : List Loc) (σ : State),
          v.Events' ↦*□ ps ∗ ([∗list] p; e ∈ ps; es, watchEvOwn p e) ∗ etcdLb γ σ ∗
          ⌜seen ++ es <+: watchHist σ.kv rg rev⌝ ∗ watchChanAt wc γ rg rev (seen ++ es)) }}

/-- **The package's errors are fresh**: no error a gRPC call returns (`callErr`, 2a's slot) is one of
them (they are `errors.New` values the package's initialization allocated). Realized from the
package's `init` (fresh allocations) and the shapes `callErr` admits (rpctypes', grpc's, the
context's error values). -/
def recipeErr_fresh.spec : Prop := ∀ (err : GoInterface) (k : CallErr) (e : RecipeErr),
  callErr (GF := GF) err k ⊢ ⌜err ≠ recipeErr e⌝

/-- **`errors.Is(err, recipeErr e)`** (the retry loops of `newUniqueKV`, `newUniqueEphemeralKV`;
`DoubleBarrier`'s callers): true exactly for the sentinel itself, for an error a KV call returns
(etcd's, or an indefinite one) and for the sentinels. Realized from Perennial's `errors.Is` (a
sentinel's `*errorString` has no `Is` or `Unwrap`; W0's `errorsIs_errVal` the same for etcd's) and
`recipeErr_fresh`, `recipeErr_ne`. -/
def errorsIs_recipeErr.spec : Prop :=
  ∀ (err : GoInterface) (e : RecipeErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      (⌜(∃ e', err = errVal e') ∨ (∃ e', err = recipeErr e')⌝ ∨ indefCall err) }}
    (App (App (Val (@! errors.Is)) (Val #err)) (Val #(recipeErr e)))
  {{ (b : Bool), RET #b; ⌜b = true ↔ err = recipeErr e⌝ }}

/-- **The package's initial globals**: the error variables hold `recipeErr`, read-only. -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ⊢
    globalAddr go_etcd_io.etcd.client.v3.experimental.recipes.ErrKeyExists ↦□ recipeErr .keyExists ∗
    globalAddr go_etcd_io.etcd.client.v3.experimental.recipes.ErrWaitMismatch ↦□ recipeErr .waitMismatch ∗
    globalAddr go_etcd_io.etcd.client.v3.experimental.recipes.ErrTooManyClients ↦□ recipeErr .tooManyClients ∗
    globalAddr go_etcd_io.etcd.client.v3.experimental.recipes.ErrNoWatcher ↦□ recipeErr .noWatcher ∗
    globalAddr go_etcd_io.etcd.client.v3.experimental.recipes.ErrWatchClosed ↦□ recipeErr .watchClosed

end res

end Recipes
end EtcdGrove
end Perennial
