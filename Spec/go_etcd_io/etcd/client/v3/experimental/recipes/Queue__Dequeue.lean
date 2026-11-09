/-
`(*Queue).Dequeue()` (`queue.go`): read the item with the least mod revision under the prefix
(`WithFirstRev()`: prefix, sorted by mod revision, limit 1) and claim it (`claimFirstKey`: delete it at
its mod revision); if the claim lost and the read had more items, retry; if the queue was empty or its
one item was claimed by another, watch the prefix from the read's revision for the first put and claim
that, retrying if it was claimed first.

**Users**: `T/v3_queue_test.go:61` (one reader, one writer: FIFO), `:193` (many readers and writers:
every item once), `T/v3_closed_watch_test.go:73,136` (a closed client, a compacted watch: an error,
the fixed `issues/recipes-dequeue-closed-watch.md`). Snippet: `recipes/queue.go`.

**Proof sketch**: the claim is the linearization point. `KV.Get` with an update made of `etcdPeek`
(as `Barrier.Wait`'s) gives `etcdLb γ σg` and the answer at `σg`: at most one key, the least mod
revision `m0` under the prefix (`RangeReq.answers` with the sort and the limit), `more` if others.
`claimFirstKey.spec` with `P σ σ' kv := ∃ kr, frontByRev ... σ.kv.store kv.key kr ∧ kr.modRev =
kv.modRevision ∧ ...` and the caller's update: its premise holds because a key present at `σ` with
mod revision `≤ σg.kv.rev` was present at `σg` with the same record (a pure fact of `Reach σg σ`:
every write gives its keys the new revision as mod revision), so a key below `m0` at `σ` would have
been at `σg`. Lost with `more`: recurse. Otherwise `WaitPrefixEvents.spec` from `σg.kv.rev` for
`[PUT]`: the first put `e` under the prefix at a revision `m ≥ σg.kv.rev`; `deleteRevKey.spec` with an
update built from the caller's (a failed comparison aborts it: recurse): at the claim `σ`, every key
under the prefix has mod revision `≥ m` (one present at `σg` was at most the one the read returned,
which another claim changed; any other was written at a revision `≥ σg.kv.rev`, so `≥ m` as `e` is the
first such put), so `e`'s key is the front. The value is `kv.Value` (the read's, unchanged since:
same mod revision) or `ev.Kv.Value` (1b's `eventOwn_unfold`): the record of the put at revision `m`,
which is the claimed record because a transaction puts a key at most once (`kvStep`'s `putOnce evs`,
W0; review 1f-provability-1, F2), so the one put of the key at `m` is the record whose mod
revision is `m`. Errors: `recipeErrOk`. The facts about `σg`'s store at later states use W0's
`etcdLb_init` (a present key's mod revision is its writing event's revision).

**Changes**: old spec (`dequeuedAt`, `dequeueOrder` at the read's revision, over the recipes' client
invariant) gave the order at the `Get`; now the caller's update fires at the claim, where the item is
the front (`frontByRev`): the queue is linearizable as a FIFO queue by mod revision, whoever else
writes the prefix (the lost-claim path included: `nonissues/recipes-pqueue-dequeue-order.md` left
`Queue`'s case open; it is FIFO).

**Changes (second pass)**: the claimed key's membership in the prefix, its record at the claim and
the returned value are now unconditional (1b's `watchStep` now says, outside the `exactFrom` gate,
that each event is a real event of its revision kept by the watch, so on the watch path the event's
key is under the prefix and its key-value is the record of its mod revision, which the successful
`deleteRevReq` claims: `putOnce`); only the front condition stays gated (the watch path's "first
put after the read" needs exact events). `ReqEveryItemOnce`, `ReqDequeueClosed` no longer assume
the compaction condition.

**Changes (verify-round)**: none to the triple; the snippets that dequeue assumed the compaction condition (A3 F3), since narrowed by the second pass above to the snippets that check the order.

**Margin**: on an error the caller's update is not given back, though only an indefinite error of a
claim may have fired it. The order is by mod revision (`WithFirstRev()`), which is the creation
order of keys never rewritten (an `Enqueue`'s).

**Integration (I1)**: the front condition in the caller's update and the returned value is gated by the compaction condition `exactFrom σ.kv 1` (W0's
`EtcdModel.exactFrom`): 1b's `watchStep` gives a response's events (and a progress's emptiness) only
under it, so the facts this call learns from a watch hold only under it; facts learned from a
`Get` would not need it but are stated under the same condition (a caller cannot tell the paths
apart). The weakest condition the watches need: the queue has no anchor, so the whole history (`1`).
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

/-- **`q.Dequeue()`**: the value of the item it deleted, which was the front of the queue (the least mod revision under the prefix) at the deletion, linearized there by the caller's update; or an error. -/
def Queue.Dequeue.spec : Prop :=
  ∀ (q c : Loc) (γ : Cluster) (who : Principal) (kp : GoString)
    (Q : State → State → GoString → KeyRec → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ queueAt q c γ who kp ∗ etcdPeek γ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (kr : KeyRec) (res : Resp),
             ⌜(pfxRange kp).mem k ∧ σ.kv.store k = some kr ∧
              (EtcdModel.exactFrom σ.kv 1 → frontByRev (pfxRange kp) σ.kv.store k kr) ∧
              Step who (deleteRevReq k kr.modRev) σ σ' res ∧ txnSucceeded res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' k kr }> }}
    (App (Val (q @!! go.GoType.PointerType Queue.ty @!! go!"Dequeue")) (Val #()))
  {{ (v : GoString) (err : GoInterface), RET (PairV #v #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' k kr, Q σ σ' k kr ∗ ⌜v = kr.value⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ v = []⌝ ∗ recipeErrOk err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
