/-
`(*PriorityQueue).Dequeue()` (`priority_queue.go`): as `Queue.Dequeue`, with the first key in key order
(`WithFirstKey()`), and the same fallback to the first put after the read.

**Users**: `T/v3_queue_test.go:110` (all items enqueued before: priority order), `:230` (many readers
and writers), `T/v3_closed_watch_test.go:76`. Snippet: `recipes/pqueue.go`.

**Proof sketch**: as `Queue.Dequeue`'s, with `σ0` (`etcdLb γ σ0`, the caller's) and `σg` reached from
it. Claim of the read's key `k` (first in key order at `σg`): at the claim `σ`, a key before `k` in key
order was not there at `σg` with its record, so it was written after `σg.kv.rev ≥ σ0.kv.rev`. Watch
path: as `Queue`'s, every key under the prefix at the claim was written at a revision `≥ m > σg.kv.rev`
(`m > σg.kv.rev` because the one key present at `σg` was changed before the first claim), so every key
before the claimed one, too. One condition covers both: `frontByKey ... σ0.kv.rev`.

**Changes**: old spec (`pqueue_min_key`, `pqueue_order` at the read's revision) gave the order at the
read; now the caller's update fires at the claim, with the order the code supports there: the
claimed item is first in key order among the items present at `σ0`, but an item enqueued during the
call may be ahead of it (`nonissues/recipes-pqueue-dequeue-order.md`: the lost-claim fallback takes
the first put, not the highest priority, so the queue is not linearizable as a priority queue; and
its "FIFO" comment means "least priority value first").

**Margin**: on the fallback path the claimed item is also the least mod revision (FIFO among the later
arrivals), which the spec does not say; errors as `Queue.Dequeue`'s.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.client.v3.experimental.recipes

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`q.Dequeue()`**: the value of the item it deleted, first in key (priority, then sequence) order among the items present when the call started (`σ0`), linearized at the deletion by the caller's update; or an error. -/
def PriorityQueue.Dequeue.spec : Prop :=
  ∀ (q c : Loc) (γ : Cluster) (who : Principal) (key : GoString) (σ0 : State)
    (Q : State → State → GoString → KeyRec → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ pqueueAt q c γ who key ∗ etcdPeek γ ∗ etcdLb γ σ0 ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (kr : KeyRec) (res : Resp),
             ⌜frontByKey (pfxRange (key ++ go!"/")) σ.kv.store σ0.kv.rev k kr ∧
              Step who (deleteRevReq k kr.modRev) σ σ' res ∧ txnSucceeded res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' k kr }> }}
    (App (Val (q @!! go.GoType.PointerType PriorityQueue.ty @!! go!"Dequeue")) (Val #()))
  {{ (v : GoString) (err : GoInterface), RET (PairV #v #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' k kr, Q σ σ' k kr ∗ ⌜v = kr.value⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ v = []⌝ }}

end spec

end Recipes
end EtcdGrove
end Perennial
