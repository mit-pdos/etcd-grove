/-
The results of `client/v3/experimental/recipes` so far (unit 2: the barrier, the queue and the
priority queue), restated at top level, with the trust base of each printed in the build log
(`#print axioms`). Every function of `barrier.go`, `queue.go` and `priority_queue.go` has a
`Spec`/`Proof` pair and a linked result (`Link.lean`, generated). Every result rests on the
recipes' premise that a watch channel is never closed (`isEtcdRecipesClient`, the two findings of
unit 0), and the enqueues on unit 1b's `newUniqueKV`/`newSequentialKV` (`sorry` until then).

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
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.Link
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesQueue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

/-- **A key-value lives unchanged from its mod revision while it is present** (a law of etcd's
history the model does not assume; stated for `queue_fifo_before_claim`): a key-value of etcd's
state at `a` is in its state at every `b` from its mod revision to `a` (a key not written in
`(m, a]` keeps its record; any write, a lease's expiry too, gives it a new mod revision or deletes
it). -/
def EtcdModRevPersist (GF : BundledGFunctors) (pfx : GoString) : Prop :=
  ∀ (a b : w64) (s s' : List EtcdKv), etcdState (GF := GF) a pfx s ∗ etcdState b pfx s' ⊢
    ⌜∀ v ∈ s, sint.Z v.modRev ≤ sint.Z b → sint.Z b ≤ sint.Z a → v ∈ s'⌝

section results
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

end results

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
