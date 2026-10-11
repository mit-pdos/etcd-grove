/-
The results of `client/v3/experimental/recipes`, restated at top level, with the trust base of
each printed in the build log (`#print axioms`). Every recipes result rests on the client
bundle's premise that a watch channel is never closed (`isEtcdRecipesClient`, see
`InvRecipesClient.lean`, the two findings of unit 0). Each unit's results are in a section of
their own, in unit order (2: the barrier and the queues; 3: the RWMutex and the double barrier),
then the priority queue's order (`pqueue_order`), which composes unit 1b's order of
`newSequentialKV`'s keys with unit 2's least key.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.Link
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesQueue
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesSeq

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

/-! ## Unit 2: the barrier (`barrier.go`), the queue (`queue.go`), the priority queue
(`priority_queue.go`)

Every function of `barrier.go`, `queue.go` and `priority_queue.go` has a `Spec`/`Proof` pair and
a linked result (`Link.lean`, generated).

* **Barrier** (`barrier_hold`, `barrier_release`, `barrier_wait_release`): `Hold`'s `nil` means
  it created the key, `ErrKeyExists` that the key was there; `Release`'s `nil` that the key was
  absent at some revision after the call began; `Wait`'s `nil` that the key was absent at some
  revision at or after its get's: released.
* **Queue** (`queue_Enqueue`, `queue_Dequeue`): `Dequeue`'s `(v, nil)` is an item `it` under the
  prefix with the value `v`, dequeued by this call (`dequeuedAt`) in order (`dequeueOrder`).
* **Dequeued at most once** (`queue_dequeued_once`, `pqueue_dequeued_once`): two dequeues (by
  any dequeuers) of items with the same key and mod revision are impossible: a claim's revision
  is its own (the token `etcdRevToken`, an axiom of the client contract: a committed write is its
  own revision).
* **What is dequeued was enqueued** (`queue_dequeued_was_enqueued`, `..._pqueue`): the item, with
  its value, was under the prefix in etcd's state just before the claim (who put it the recipe
  cannot know).
* **FIFO** (`queue_fifo`): at the revision `r0 < r` of `Dequeue`'s last get, the item was the
  one with the least mod revision under the prefix (the get path), or every item there then was
  claimed by others by `r` and the item was put at or after `r0` (the wait path: the watch
  contract does not say that no event is skipped, so nothing is said of items put between `r0` and
  the event). `queue_fifo_before_claim`: under the history law that a key-value lives unchanged
  from its mod revision while it is present (`EtcdModRevPersist`, not among the model's axioms),
  the get path's item had the least mod revision among the items present just before the claim.
* **Least key** (`pqueue_min_key`): the priority queue's, at the get's revision `r0` (the get
  path), or the wait path's facts. Not at the claim: a key with a higher priority (a smaller key)
  enqueued between the get and the claim is not seen (`notes/STATUS.md`).
-/

/-- **A key-value lives unchanged from its mod revision while it is present** (a law of etcd's
history the model does not assume; stated for `queue_fifo_before_claim`): a key-value of etcd's
state at `a` is in its state at every `b` from its mod revision to `a` (a key not written in
`(m, a]` keeps its record; any write, a lease's expiry too, gives it a new mod revision or deletes
it). -/
def EtcdModRevPersist (GF : BundledGFunctors) (pfx : GoString) : Prop :=
  ∀ (a b : w64) (s s' : List EtcdKv), etcdState (GF := GF) a pfx s ∗ etcdState b pfx s' ⊢
    ⌜∀ v ∈ s, sint.Z v.modRev ≤ sint.Z b → sint.Z b ≤ sint.Z a → v ∈ s'⌝

section unit2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- `NewBarrier(client, key)` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewBarrier.lean`). -/
theorem barrier_NewBarrier : NewBarrier.spec (GF := GF) (hG := hG) := wp_NewBarrier

/-- **`b.Hold()`**: `nil` means the key was created (absent just before) at a revision after the
call began; `ErrKeyExists` that it was present then
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Barrier__Hold.lean`). -/
theorem barrier_hold : Barrier.Hold.spec (GF := GF) (hG := hG) := Barrier.wp_Hold

/-- **`b.Release()`**: `nil` means the key was absent at a revision after the call began
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Barrier__Release.lean`). -/
theorem barrier_release : Barrier.Release.spec (GF := GF) (hG := hG) := Barrier.wp_Release

/-- **`b.Wait()` returns `nil` only once released**: the key was absent at some revision at or
after the one the caller knew etcd had reached
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Barrier__Wait.lean`). -/
theorem barrier_wait_release : Barrier.Wait.spec (GF := GF) (hG := hG) := Barrier.wp_Wait

/-- `NewQueue(client, keyPrefix)` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewQueue.lean`). -/
theorem queue_NewQueue : NewQueue.spec (GF := GF) (hG := hG) := wp_NewQueue

/-- `q.Enqueue(val)` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Queue__Enqueue.lean`). -/
theorem queue_Enqueue : Queue.Enqueue.spec (GF := GF) (hG := hG) := Queue.wp_Enqueue

/-- `q.Dequeue()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Queue__Dequeue.lean`). -/
theorem queue_Dequeue : Queue.Dequeue.spec (GF := GF) (hG := hG) := Queue.wp_Dequeue

/-- `NewPriorityQueue(client, key)`
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewPriorityQueue.lean`). -/
theorem pqueue_NewPriorityQueue : NewPriorityQueue.spec (GF := GF) (hG := hG) :=
  wp_NewPriorityQueue

/-- `q.Enqueue(val, pr)`
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/PriorityQueue__Enqueue.lean`). -/
theorem pqueue_Enqueue : PriorityQueue.Enqueue.spec (GF := GF) (hG := hG) :=
  PriorityQueue.wp_Enqueue

/-- `q.Dequeue()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/PriorityQueue__Dequeue.lean`). -/
theorem pqueue_Dequeue : PriorityQueue.Dequeue.spec (GF := GF) (hG := hG) :=
  PriorityQueue.wp_Dequeue

/-- **Dequeued at most once.** Two dequeues from the queue on `kp` (what `Queue.Dequeue` returns
on `nil`, by this or any other dequeuer) of items with the same key and mod revision are
impossible. -/
theorem queue_dequeued_once (kp : GoString) (it1 it2 : EtcdKv) (r1 r2 : w64)
    (hk : it1.key = it2.key) (hm : it1.modRev = it2.modRev) :
    dequeuedAt (GF := GF) kp kp it1 r1 ∗ dequeuedAt kp kp it2 r2 ⊢ False :=
  dequeuedAt_once kp kp it1 it2 r1 r2 hk hm

/-- **Dequeued at most once**, the priority queue on `key`. -/
theorem pqueue_dequeued_once (key : GoString) (it1 it2 : EtcdKv) (r1 r2 : w64)
    (hk : it1.key = it2.key) (hm : it1.modRev = it2.modRev) :
    dequeuedAt (GF := GF) [] (key ++ go!"/") it1 r1 ∗ dequeuedAt [] (key ++ go!"/") it2 r2 ⊢
      False :=
  dequeuedAt_once [] (key ++ go!"/") it1 it2 r1 r2 hk hm

/-- **What is dequeued was enqueued**: the item a dequeue from the queue on `kp` returns (its value
is `it.value`) was, as a whole, under `kp` in etcd's state just before the claim, and absent at
the claim's revision. -/
theorem queue_dequeued_was_enqueued (kp : GoString) (it : EtcdKv) (r : w64) :
    dequeuedAt (GF := GF) kp kp it r ⊢
      ∃ s : List EtcdKv, □ etcdState (r - W64 1) kp s ∗ ⌜it ∈ s ∧ kp <+: it.key⌝ ∗
        etcdAbsent kp it.key r := by
  unfold dequeuedAt
  iintro ⟨#Hd, -, ⟨%s, #Hs, %Hit⟩, %Hk⟩
  iexists s
  iframe Hs
  isplitr
  · ipureintro; exact ⟨Hit, Hk⟩
  iunfold revKeyDeleted at Hd
  icases Hd with ⟨%s1, %s1', -, #Hs1', %Hp⟩
  unfold etcdAbsent
  iexists s1'
  iframe Hs1'
  ipureintro; exact Hp.2.2

/-- **What is dequeued was enqueued**, the priority queue on `key` (contracts at `""`). -/
theorem pqueue_dequeued_was_enqueued (key : GoString) (it : EtcdKv) (r : w64) :
    dequeuedAt (GF := GF) [] (key ++ go!"/") it r ⊢
      ∃ s : List EtcdKv, □ etcdState (r - W64 1) [] s ∗ ⌜it ∈ s ∧ (key ++ go!"/") <+: it.key⌝ := by
  unfold dequeuedAt
  iintro ⟨-, -, ⟨%s, #Hs, %Hit⟩, %Hk⟩
  iexists s
  iframe Hs
  ipureintro; exact ⟨Hit, Hk⟩

/-- **FIFO**: a dequeue of `it` at `r` from the queue on `kp` happened after a get at `r0 < r`
whose state `s0` had `it` with the least mod revision under `kp` (the get path), or whose items
under `kp` were all claimed by others by `r`, `it` being put at or after `r0` (the wait path). -/
theorem queue_fifo (kp : GoString) (it : EtcdKv) (r : w64) :
    dequeueOrder (GF := GF) kp kp modRevLe it r ⊢
      ∃ (r0 : w64) (s0 : List EtcdKv), □ etcdState r0 kp s0 ∗ ⌜sint.Z r0 < sint.Z r⌝ ∗
        (⌜it ∈ s0 ∧ ∀ w ∈ s0, kp <+: w.key → sint.Z it.modRev ≤ sint.Z w.modRev⌝ ∨
         (⌜sint.Z r0 ≤ sint.Z it.modRev⌝ ∗ □ ∀ w : EtcdKv, ⌜w ∈ s0 ∧ kp <+: w.key⌝ -∗
            ∃ r' : w64, etcdReached r' ∗ revKeyGone kp w.key w.modRev r' ∗
              ⌜sint.Z r0 ≤ sint.Z r' ∧ sint.Z r' ≤ sint.Z r⌝)) := by
  unfold dequeueOrder modRevLe
  iintro H
  iexact H

/-- **FIFO just before the claim, on the get path**, under the history law `EtcdModRevPersist`:
a dequeue from the queue on `kp` that took the get's item claimed the item with the least mod
revision among those under `kp` in etcd's state just before the claim (an item older than it
would have been in the get's state, where `it` was the oldest; a newer one is newer). On the wait
path, the facts of `queue_fifo`. -/
theorem queue_fifo_before_claim (kp : GoString) (it : EtcdKv) (r : w64)
    (hmp : EtcdModRevPersist GF kp) :
    dequeuedAt (GF := GF) kp kp it r ∗ dequeueOrder kp kp modRevLe it r ⊢
      ∃ s : List EtcdKv, □ etcdState (r - W64 1) kp s ∗ ⌜it ∈ s⌝ ∗
        (⌜∀ w ∈ s, kp <+: w.key → sint.Z it.modRev ≤ sint.Z w.modRev⌝ ∨
         ∃ (r0 : w64) (s0 : List EtcdKv), □ etcdState r0 kp s0 ∗
           ⌜sint.Z r0 ≤ sint.Z it.modRev⌝ ∗ □ ∀ w : EtcdKv, ⌜w ∈ s0 ∧ kp <+: w.key⌝ -∗
            ∃ r' : w64, etcdReached r' ∗ revKeyGone kp w.key w.modRev r' ∗
              ⌜sint.Z r0 ≤ sint.Z r' ∧ sint.Z r' ≤ sint.Z r⌝) := by
  iintro ⟨Hdq, #Hord⟩
  unfold dequeuedAt
  icases Hdq with ⟨-, -, ⟨%s, #Hs, %Hit⟩, -⟩
  unfold dequeueOrder
  icases Hord with ⟨%r0, %s0, #Hs0, %Hlt, (%Hget | ⟨%Hput, #Hdr⟩)⟩
  · iexists s
    iframe Hs
    isplitr
    · ipureintro; exact Hit
    ileft
    ihave %Hrv0 := etcdState_revs r0 kp s0 $$ Hs0
    ihave %Hp := hmp (r - W64 1) r0 s s0 $$ [$Hs $Hs0]
    ipureintro
    intro w hw hwk
    have hr1 : sint.Z (r - W64 1) = sint.Z r - 1 := by
      have := (Hrv0 it Hget.1).1
      have := (Hrv0 it Hget.1).2.2.1
      word
    by_cases hle : sint.Z w.modRev ≤ sint.Z r0
    · exact Hget.2 w (Hp w hw hle (by omega)) hwk
    · have := (Hrv0 it Hget.1).2.2.1
      omega
  · iexists s
    isplitr
    · iexact Hs
    isplitr
    · ipureintro; exact Hit
    iright
    iexists r0, s0
    iframe Hs0 Hdr
    ipureintro; exact Hput

/-- **Least key**: a dequeue of `it` at `r` from the priority queue on `key` happened after a get
at `r0 < r` whose state `s0` had `it` with the least key under `key ++ "/"` (the get path), or
whose items under `key ++ "/"` were all claimed by others by `r`, `it` being put at or after
`r0` (the wait path). Not at the claim: see the module docstring. -/
theorem pqueue_min_key (key : GoString) (it : EtcdKv) (r : w64) :
    dequeueOrder (GF := GF) [] (key ++ go!"/") keyLe it r ⊢
      ∃ (r0 : w64) (s0 : List EtcdKv), □ etcdState r0 [] s0 ∗ ⌜sint.Z r0 < sint.Z r⌝ ∗
        (⌜it ∈ s0 ∧ ∀ w ∈ s0, (key ++ go!"/") <+: w.key → go.GoStringLe it.key w.key⌝ ∨
         (⌜sint.Z r0 ≤ sint.Z it.modRev⌝ ∗ □ ∀ w : EtcdKv,
            ⌜w ∈ s0 ∧ (key ++ go!"/") <+: w.key⌝ -∗
            ∃ r' : w64, etcdReached r' ∗ revKeyGone [] w.key w.modRev r' ∗
              ⌜sint.Z r0 ≤ sint.Z r' ∧ sint.Z r' ≤ sint.Z r⌝)) := by
  unfold dequeueOrder keyLe
  iintro H
  iexact H

end unit2

/-! ## Unit 3: the RWMutex (`rwmutex.go`) and the double barrier (`double_barrier.go`)

Every function of `rwmutex.go` and `double_barrier.go` has a `Spec`/`Proof` pair and a linked
result (`Link.lean`, generated).

* **`RLock`/`Lock`** (`rwmutex_RLock`, `rwmutex_Lock`): `nil` means the fresh key in `myKey` holds
  the mutex in its role since the revision `R` of `waitOnLastRev`'s last get (`rwHeldAt`: no
  blocking key with a mod revision below the key's creation at `R`); neither checks its own key
  after the wait, so, as `Mutex`'s, the results are about keys present in a state.
* **`RUnlock`/`Unlock`** (`rwmutex_RUnlock`, `rwmutex_Unlock`, `rwmutex_unlock_released`): `nil`
  means the key is absent at some revision at least the caller's.
* **Exclusion** (`rwmutex_write_exclusion`, `rwmutex_read_write_exclusion`): a writer and any other
  holder with a different create revision, and so a reader and a writer, are never both present
  in etcd's state at a revision at or after both of their `rwHeldAt` revisions, **provided the
  holders' keys are never modified** (`keyUnmodified`: the recipe's get filters by mod revision,
  so a key rewritten by another client, which keeps its create revision, stops blocking; the
  recipe itself only creates and deletes its keys). From the history law
  `etcdState_create_persist` alone, as `Mutex`'s exclusion.
* **`Enter`** (`double_barrier_Enter`, `double_barrier_enter_ready`, `double_barrier_enter_count`):
  `nil` means its direct path saw `count` waiters, or its waiting path saw a write of `key/ready`
  at or after its key's creation (`enterReady`); under the protocol's premise on `key/ready`
  (`readyPutsCounted`: every write of it is preceded by `count` waiters), at some revision etcd
  has reached at `Enter`'s return at least `count` keys with the prefix `key/waiters` were
  present. Needs `count > 0` (`NewDoubleBarrier`).
* **`Leave`** (`double_barrier_Leave`, `double_barrier_leave`): `nil`, with the key `Enter` left
  in `myKey` (its record's `KV` not nil), means that key is absent at some revision at least the
  caller's.
-/

section unit3
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- `NewRWMutex(s, prefix)` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewRWMutex.lean`). -/
theorem rwmutex_NewRWMutex : NewRWMutex.spec (GF := GF) (hG := hG) := wp_NewRWMutex

/-- `rwm.RLock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__RLock.lean`). -/
theorem rwmutex_RLock : RWMutex.RLock.spec (GF := GF) (hG := hG) := RWMutex.wp_RLock

/-- `rwm.Lock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__Lock.lean`). -/
theorem rwmutex_Lock : RWMutex.Lock.spec (GF := GF) (hG := hG) := RWMutex.wp_Lock

/-- `rwm.RUnlock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__RUnlock.lean`). -/
theorem rwmutex_RUnlock : RWMutex.RUnlock.spec (GF := GF) (hG := hG) := RWMutex.wp_RUnlock

/-- `rwm.Unlock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__Unlock.lean`). -/
theorem rwmutex_Unlock : RWMutex.Unlock.spec (GF := GF) (hG := hG) := RWMutex.wp_Unlock

/-- **Unlocking releases**: `RUnlock`/`Unlock` returning `nil` for a key whose record's `KV` is not
nil (what `RLock`/`Lock` leave in `myKey`) means the key is absent at some revision at least
`lo` that etcd has reached. -/
theorem rwmutex_unlock_released (pfx : GoString) (st : RemoteKVSt) (lo : w64)
    (hkv : st.kv ≠ GoInterface.nil) :
    rwUnlockResult (GF := GF) pfx st lo GoInterface.nil ⊢
      ∃ r : w64, etcdReached r ∗ etcdAbsent pfx st.key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝ := by
  unfold rwUnlockResult
  rcases h : st.kv with kv | _
  · simp only
    iintro (%Hne | ⟨-, H⟩)
    · exact absurd rfl Hne
    · iexact H
  · exact absurd h hkv

/-- **Writer exclusion.** A writer `(k1, c1)` holding the RWMutex on `pfx` since `R1` and a holder
`(k2, c2)` in any role since `R2` (what `Lock`/`RLock` return on `nil`), with different create
revisions and keys that are never modified (`keyUnmodified`), are never both present in etcd's
state `s` at a revision `a` at or after `R1` and `R2`. -/
theorem rwmutex_write_exclusion (pfx k1 k2 : GoString) (role : RWRole) (c1 c2 R1 R2 a : w64)
    (s : List EtcdKv) (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    rwHeldAt (GF := GF) pfx .write k1 c1 R1 ∗ rwHeldAt pfx role k2 c2 R2 ∗
      keyUnmodified pfx k1 c1 ∗ keyUnmodified pfx k2 c2 ∗ etcdState a pfx s ⊢
      ⌜¬ (EtcdGrove.concurrency.HasKeyAt k1 c1 s ∧ EtcdGrove.concurrency.HasKeyAt k2 c2 s)⌝ :=
  rwHeldAt_write_exclusion pfx k1 k2 role c1 c2 R1 R2 a s hne h1 h2

/-- **Reader-writer exclusion.** A reader `(k1, c1)` since `R1` and a writer `(k2, c2)` since `R2`,
with different create revisions and unmodified keys, are never both present in etcd's state at a
revision at or after `R1` and `R2`. (Two readers may be.) -/
theorem rwmutex_read_write_exclusion (pfx k1 k2 : GoString) (c1 c2 R1 R2 a : w64)
    (s : List EtcdKv) (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    rwHeldAt (GF := GF) pfx .read k1 c1 R1 ∗ rwHeldAt pfx .write k2 c2 R2 ∗
      keyUnmodified pfx k1 c1 ∗ keyUnmodified pfx k2 c2 ∗ etcdState a pfx s ⊢
      ⌜¬ (EtcdGrove.concurrency.HasKeyAt k1 c1 s ∧ EtcdGrove.concurrency.HasKeyAt k2 c2 s)⌝ :=
  rwHeldAt_read_write_exclusion pfx k1 k2 c1 c2 R1 R2 a s hne h1 h2

/-- `NewDoubleBarrier(s, key, count)`
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewDoubleBarrier.lean`). -/
theorem double_barrier_NewDoubleBarrier : NewDoubleBarrier.spec (GF := GF) (hG := hG) :=
  wp_NewDoubleBarrier

/-- `b.Enter()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__Enter.lean`). -/
theorem double_barrier_Enter : DoubleBarrier.Enter.spec (GF := GF) (hG := hG) :=
  DoubleBarrier.wp_Enter

/-- `b.Leave()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__Leave.lean`). -/
theorem double_barrier_Leave : DoubleBarrier.Leave.spec (GF := GF) (hG := hG) :=
  DoubleBarrier.wp_Leave

/-- **What a successful `Enter` saw** (no premise): `nil` means a fresh key under `key/waiters/`,
and either (the direct path) at least `count` waiters at a revision etcd has reached, or (the
waiting path) a write of `key/ready` at a revision at least the key's creation, which etcd has
reached. -/
theorem double_barrier_enter_ready (b : Loc) (key : GoString) (count id lo : w64) :
    enterResult (GF := GF) b key count id lo GoInterface.nil ⊢
      ∃ st : RemoteKVSt, enterReady (key ++ go!"/") key count st.rev ∗
        ⌜(key ++ go!"/waiters") ++ go!"/" <+: st.key ∧ sint.Z lo ≤ sint.Z st.rev⌝ := by
  unfold enterResult
  iintro (⟨-, %ek, %st, -, -, #H, %Hp⟩ | ⟨Herr, -⟩ | ⟨%Hne, -⟩)
  · iexists st
    iframe H
    ipureintro; exact ⟨Hp.1, Hp.2.1⟩
  · unfold EtcdGrove.concurrency.isPkgErr
    icases Herr with ⟨-, %Hne⟩
    exact absurd rfl Hne
  · exact absurd rfl Hne

/-- **`Enter` returns `nil` only after `count` entrants**: under the protocol's premise on
`key/ready` (`readyPutsCounted`), `Enter` returning `nil` means that at some revision etcd has
reached (so at or before the return) at least `count` keys with the prefix `key/waiters` were
present. -/
theorem double_barrier_enter_count (b : Loc) (key : GoString) (count id lo : w64) :
    enterResult (GF := GF) b key count id lo GoInterface.nil ∗
      readyPutsCounted (key ++ go!"/") key count ⊢
      ∃ R : w64, etcdReached R ∗ waitersSeen (key ++ go!"/") (key ++ go!"/waiters") count R := by
  iintro ⟨H, #Hprem⟩
  ihave ⟨%st, #Hr, -⟩ := double_barrier_enter_ready b key count id lo $$ H
  iapply enterReady_counted (key ++ go!"/") key count st.rev $$ [$Hr $Hprem]

/-- **`Leave` returns `nil` only with the caller's key deleted**: for a key whose record's `KV` is
not nil (what `Enter` leaves in `myKey`), `nil` means the key is absent at some revision at least
`lo` that etcd has reached (deleted by `Leave` itself, or found absent). -/
theorem double_barrier_leave (pfx : GoString) (st : RemoteKVSt) (lo : w64)
    (hkv : st.kv ≠ GoInterface.nil) :
    leaveResult (GF := GF) pfx st lo GoInterface.nil ⊢
      ∃ r : w64, etcdReached r ∗ etcdAbsent pfx st.key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝ := by
  unfold leaveResult
  iintro (⟨-, (H | %H)⟩ | %Hne)
  · iexact H
  · exact absurd H hkv
  · exact absurd rfl Hne

end unit3

/-! ## The priority queue's order (`pqueue_order`): unit 1b's sequential keys, unit 2's least key

`PriorityQueue.Enqueue(val, pr)` puts its item with `newSequentialKV` on the prefix
`key/%05d(pr)` (`pqPrefix key p`), so under unit 1b's premise on the keys of that prefix its key is
`key/%05d(pr)/%016d(n)` (`pqKey key p n`), `n` one past the greatest sequence number of that
priority present at its get (`pqueue_enqueue_order`, from `seqKeyPutAt_order`). `Dequeue`'s get
path takes the least key under `key/` (`pqueue_min_key`); when every key under `key/` has the
shape `pqKey` (`PQKeysWf`: what `Enqueue` writes), the least key is the least priority, then the
least sequence number (`pqueue_order`): fixed-width decimals compare as numbers
(`padZeros_decimalNat_lt`, Perennial's `fmt`), and five digits hold every `uint16`. The premise of
the dequeue implies that of each priority's enqueues, up to the bound (`pqKeysWf_seqKeysWf`).
All at the get's revision only: the priority queue is not linearizable (`notes/STATUS.md`). -/

section pqorder

/-- A strict lexicographic order between two strings of the same length survives any suffixes. -/
theorem goStringLt_append_of_length_eq {a b : GoString} (x y : GoString)
    (h : go.GoStringLt a b) (hl : a.length = b.length) : go.GoStringLt (a ++ x) (b ++ y) := by
  unfold go.GoStringLt at *
  induction h with
  | nil => simp at hl
  | cons _ ih => exact List.Lex.cons (ih (by simpa using hl))
  | rel h => exact List.Lex.rel h

/-- The priority queue's prefix for priority `p`: `key/%05d(p)`. -/
def pqPrefix (key : GoString) (p : Nat) : GoString :=
  key ++ go!"/" ++ _root_.Perennial.fmt.padZeros 5 (_root_.Perennial.fmt.decimalNat p)

/-- The priority queue's key for priority `p` and sequence number `n`: `key/%05d(p)/%016d(n)`. -/
def pqKey (key : GoString) (p n : Nat) : GoString := seqKey (pqPrefix key p) n

/-- **Every key under `key/` is a priority queue's key** (`key/%05d(p)/%016d(n)` with `p < 10^5`,
which holds every `uint16`, and `n < 10^16`): what `Enqueue` writes. -/
def PQKeysWf (key : GoString) (s : List EtcdKv) : Prop :=
  ∀ v ∈ s, (key ++ go!"/") <+: v.key →
    ∃ p n, p < 10 ^ 5 ∧ n < 10 ^ 16 ∧ v.key = pqKey key p n

theorem length_pad5 (p : Nat) (hp : p < 10 ^ 5) :
    (_root_.Perennial.fmt.padZeros 5 (_root_.Perennial.fmt.decimalNat p)).length = 5 := by
  have := _root_.Perennial.fmt.length_decimalNat_le p 5 (by omega) hp
  rw [_root_.Perennial.fmt.length_padZeros]; omega

theorem pad5_inj (p p' : Nat) (hp : p < 10 ^ 5) (hp' : p' < 10 ^ 5)
    (h : _root_.Perennial.fmt.padZeros 5 (_root_.Perennial.fmt.decimalNat p) =
      _root_.Perennial.fmt.padZeros 5 (_root_.Perennial.fmt.decimalNat p')) : p = p' := by
  rcases Nat.lt_trichotomy p p' with hlt | e | hlt
  · have := _root_.Perennial.fmt.padZeros_decimalNat_lt 5 p p' hlt hp'
    rw [h] at this; exact absurd this (goStringLt_irrefl _)
  · exact e
  · have := _root_.Perennial.fmt.padZeros_decimalNat_lt 5 p' p hlt hp
    rw [h] at this; exact absurd this (goStringLt_irrefl _)

/-- **The order of the priority queue's keys**: lexicographic in (priority, sequence number). -/
theorem pqKey_lt (key : GoString) (p1 n1 p2 n2 : Nat) (hp1 : p1 < 10 ^ 5) (hp2 : p2 < 10 ^ 5)
    (hn2 : n2 < 10 ^ 16) (h : p1 < p2 ∨ (p1 = p2 ∧ n1 < n2)) :
    go.GoStringLt (pqKey key p1 n1) (pqKey key p2 n2) := by
  rcases h with h | ⟨rfl, h⟩
  · unfold pqKey seqKey pqPrefix
    simp only [List.append_assoc]
    apply goStringLt_append_left
    apply goStringLt_append_left
    apply goStringLt_append_of_length_eq
    · exact _root_.Perennial.fmt.padZeros_decimalNat_lt 5 p1 p2 h hp2
    · rw [length_pad5 p1 hp1, length_pad5 p2 hp2]
  · exact seqKey_lt _ n1 n2 h hn2

/-- The converse: a key at most another is at most it in (priority, sequence number). -/
theorem pqKey_le (key : GoString) (p1 n1 p2 n2 : Nat) (hp1 : p1 < 10 ^ 5) (hp2 : p2 < 10 ^ 5)
    (hn1 : n1 < 10 ^ 16) (h : go.GoStringLe (pqKey key p1 n1) (pqKey key p2 n2)) :
    p1 < p2 ∨ (p1 = p2 ∧ n1 ≤ n2) := by
  refine Classical.byContradiction fun hc => ?_
  have hlt := pqKey_lt key p2 n2 p1 n1 hp2 hp1 hn1 (by omega)
  rcases h with e | h
  · rw [e] at hlt; exact goStringLt_irrefl _ hlt
  · exact goStringLt_irrefl _ (goStringLt_trans h hlt)

/-- **The dequeue's premise gives each priority's**: if every key under `key/` is a `pqKey`,
every key under `key/%05d(p)` is a sequential key of that prefix (`SeqKeysWf`; the enqueue's
order needs the bound `10^16 - 1`, one less). -/
theorem pqKeysWf_seqKeysWf (key : GoString) (p : Nat) (hp : p < 10 ^ 5) (s : List EtcdKv)
    (h : PQKeysWf key s) : SeqKeysWf (pqPrefix key p) s := by
  intro v hv hpre
  have hk : (key ++ go!"/") <+: v.key :=
    (List.prefix_append _ _).trans (by unfold pqPrefix at hpre; exact hpre)
  obtain ⟨p', n, hp', hn, hv'⟩ := h v hv hk
  refine ⟨n, hn, ?_⟩
  have hpre' : pqPrefix key p' <+: v.key := by
    rw [hv']; unfold pqKey seqKey; rw [List.append_assoc]; exact List.prefix_append _ _
  have hlen : (pqPrefix key p).length = (pqPrefix key p').length := by
    unfold pqPrefix; simp only [List.length_append, length_pad5 p hp, length_pad5 p' hp']
  have he : pqPrefix key p = pqPrefix key p' :=
    (List.prefix_of_prefix_length_le hpre hpre' (by omega)).eq_of_length hlen
  unfold pqPrefix at he
  have := pad5_inj p p' hp hp' (List.append_cancel_left he)
  subst this
  exact hv'

theorem pqPrefix_ne_nil (key : GoString) (p : Nat) : pqPrefix key p ≠ [] := by
  unfold pqPrefix; simp

/-- `Enqueue`'s prefix is `pqPrefix` of its priority. -/
theorem pqPrefix_uint16 (key : GoString) (pr : w16) :
    key ++ go!"/" ++ _root_.Perennial.fmt.padZeros 5 (_root_.Perennial.fmt.decimal (uint.Z pr)) =
      pqPrefix key (uint.Z pr).toNat := by
  unfold pqPrefix
  rw [_root_.Perennial.fmt.decimal_of_nonneg (by word)]

theorem uint16_toNat_lt (pr : w16) : (uint.Z pr).toNat < 10 ^ 5 := by
  have : uint.Z pr < 2 ^ 16 := by word
  omega

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`Enqueue(val, pr)`'s key, in order** (on `pqueue_Enqueue`'s result): under unit 1b's premise
on the keys under the priority's prefix at the get's revision `g` (`SeqKeysBelow (key/%05d(pr))
(10^16 - 1)`), the key is `key/%05d(pr)/%016d(n)` with `n < 10^16`, greater than every key of that
priority present then, and `n` is one past the greatest such key's (`0` if none). -/
theorem pqueue_enqueue_order (key val k : GoString) (pr : w16) (g r : w64) :
    seqKeyPutAt (GF := GF) [] (key ++ go!"/" ++ _root_.Perennial.fmt.padZeros 5
        (_root_.Perennial.fmt.decimal (uint.Z pr))) k val g r ⊢
      ∃ sg : List EtcdKv, □ etcdState g [] sg ∗
        ⌜SeqKeysBelow (pqPrefix key (uint.Z pr).toNat) (10 ^ 16 - 1) sg →
          ∃ n, n < 10 ^ 16 ∧ k = pqKey key (uint.Z pr).toNat n ∧
            (∀ v ∈ sg, pqPrefix key (uint.Z pr).toNat <+: v.key →
              ∃ n' < n, v.key = pqKey key (uint.Z pr).toNat n' ∧ go.GoStringLt v.key k) ∧
            (n = 0 ∨ ∃ v ∈ sg, v.key = pqKey key (uint.Z pr).toNat (n - 1))⌝ := by
  rw [pqPrefix_uint16]
  iintro H
  ihave ⟨%sg, #Hsg, %Ho⟩ := seqKeyPutAt_order [] _ k val g r (pqPrefix_ne_nil _ _) $$ H
  iexists sg
  iframe Hsg
  ipureintro
  intro hwf
  obtain ⟨n, hn, hk, hlt, hgt, hlast⟩ := Ho hwf
  refine ⟨n, hn, hk, ?_, hlast⟩
  intro v hv hpre
  obtain ⟨n', hn', hv'⟩ := hlt v hv hpre
  exact ⟨n', hn', hv', hgt v hv hpre⟩

/-- **The priority queue's order**: a dequeue of `it` at `r` from the priority queue on `key` (on
`pqueue_Dequeue`'s result) happened after a get at `r0 < r` whose state `s0` had `it`, and, if
every key under `key/` in `s0` is a priority queue's key (`PQKeysWf`), `it`'s key is
`key/%05d(p)/%016d(n)` with `(p, n)` the least, lexicographically, among the items under `key/`
in `s0`: the highest priority (the least `p`), then the earliest allocated (the get path); or the
wait path's facts (`pqueue_min_key`): every item under `key/` at `r0` was claimed by others by `r`
and `it` was put at or after `r0`. -/
theorem pqueue_order (key : GoString) (it : EtcdKv) (r : w64) :
    dequeuedAt (GF := GF) [] (key ++ go!"/") it r ∗ dequeueOrder [] (key ++ go!"/") keyLe it r ⊢
      ∃ (r0 : w64) (s0 : List EtcdKv), □ etcdState r0 [] s0 ∗ ⌜sint.Z r0 < sint.Z r⌝ ∗
        (⌜it ∈ s0 ∧ (PQKeysWf key s0 →
            ∃ p n, p < 10 ^ 5 ∧ n < 10 ^ 16 ∧ it.key = pqKey key p n ∧
              ∀ w ∈ s0, (key ++ go!"/") <+: w.key →
                ∃ p' n', w.key = pqKey key p' n' ∧ (p < p' ∨ (p = p' ∧ n ≤ n')))⌝ ∨
         (⌜sint.Z r0 ≤ sint.Z it.modRev⌝ ∗ □ ∀ w : EtcdKv,
            ⌜w ∈ s0 ∧ (key ++ go!"/") <+: w.key⌝ -∗
            ∃ r' : w64, etcdReached r' ∗ revKeyGone [] w.key w.modRev r' ∗
              ⌜sint.Z r0 ≤ sint.Z r' ∧ sint.Z r' ≤ sint.Z r⌝)) := by
  iintro ⟨Hdq, #Hord⟩
  unfold dequeuedAt
  icases Hdq with ⟨-, -, -, %Hk⟩
  unfold dequeueOrder keyLe
  icases Hord with ⟨%r0, %s0, #Hs0, %Hlt, (%Hget | Hwait)⟩
  · iexists r0, s0
    iframe Hs0
    isplitr
    · ipureintro; exact Hlt
    ileft
    ipureintro
    refine ⟨Hget.1, fun hwf => ?_⟩
    obtain ⟨p, n, hp, hn, hit⟩ := hwf it Hget.1 Hk
    refine ⟨p, n, hp, hn, hit, fun w hw hwk => ?_⟩
    obtain ⟨p', n', hp', hn', hw'⟩ := hwf w hw hwk
    have hle := Hget.2 w hw hwk
    rw [hit, hw'] at hle
    exact ⟨p', n', hw', pqKey_le key p n p' n' hp hp' hn hle⟩
  · iexists r0, s0
    iframe Hs0
    isplitr
    · ipureintro; exact Hlt
    iright
    iexact Hwait

end pqorder

end recipes
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.recipes.barrier_NewBarrier
#print axioms Perennial.EtcdGrove.recipes.barrier_hold
#print axioms Perennial.EtcdGrove.recipes.barrier_release
#print axioms Perennial.EtcdGrove.recipes.barrier_wait_release
#print axioms Perennial.EtcdGrove.recipes.queue_NewQueue
#print axioms Perennial.EtcdGrove.recipes.queue_Enqueue
#print axioms Perennial.EtcdGrove.recipes.queue_Dequeue
#print axioms Perennial.EtcdGrove.recipes.pqueue_NewPriorityQueue
#print axioms Perennial.EtcdGrove.recipes.pqueue_Enqueue
#print axioms Perennial.EtcdGrove.recipes.pqueue_Dequeue
#print axioms Perennial.EtcdGrove.recipes.queue_dequeued_once
#print axioms Perennial.EtcdGrove.recipes.pqueue_dequeued_once
#print axioms Perennial.EtcdGrove.recipes.queue_dequeued_was_enqueued
#print axioms Perennial.EtcdGrove.recipes.pqueue_dequeued_was_enqueued
#print axioms Perennial.EtcdGrove.recipes.queue_fifo
#print axioms Perennial.EtcdGrove.recipes.queue_fifo_before_claim
#print axioms Perennial.EtcdGrove.recipes.pqueue_min_key
#print axioms Perennial.EtcdGrove.recipes.rwmutex_NewRWMutex
#print axioms Perennial.EtcdGrove.recipes.rwmutex_RLock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_Lock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_RUnlock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_Unlock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_unlock_released
#print axioms Perennial.EtcdGrove.recipes.rwmutex_write_exclusion
#print axioms Perennial.EtcdGrove.recipes.rwmutex_read_write_exclusion
#print axioms Perennial.EtcdGrove.recipes.double_barrier_NewDoubleBarrier
#print axioms Perennial.EtcdGrove.recipes.double_barrier_Enter
#print axioms Perennial.EtcdGrove.recipes.double_barrier_Leave
#print axioms Perennial.EtcdGrove.recipes.double_barrier_enter_ready
#print axioms Perennial.EtcdGrove.recipes.double_barrier_enter_count
#print axioms Perennial.EtcdGrove.recipes.double_barrier_leave
#print axioms Perennial.EtcdGrove.recipes.pqueue_enqueue_order
#print axioms Perennial.EtcdGrove.recipes.pqueue_order
