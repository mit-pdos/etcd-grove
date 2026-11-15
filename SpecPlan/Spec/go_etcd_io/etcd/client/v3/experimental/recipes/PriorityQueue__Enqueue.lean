/-
`(*PriorityQueue).Enqueue(val, pr)` (`priority_queue.go`): `newSequentialKV` under `key/<pr, 5 digits>`.

**Users**: `T/v3_queue_test.go:104` (random priorities, then dequeued in priority order), `:226`.
Snippet: `recipes/pqueue.go`.

**Proof sketch**: `fmt.Sprintf("%s%05d", q.key, pr)` (Perennial: `pqPrefix key pr`; a `uint16` has at
most 5 digits, so the key order is the priority order); `isClient_KV`; `newSequentialKV.spec` with
the caller's update unchanged.

**Changes**: old spec over the recipes' client invariant with a sequence certificate; now the caller's
update over the transaction, with its read (`R`, `seqNext`): two items of one priority get distinct
keys in enqueue order (review 1f-completeness-1, C-2).

**Margin**: as `newSequentialKV`'s.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

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

/-- **`q.Enqueue(val, pr)`**: `__<prefix>` and a key `<prefix>/<n>` (the prefix `key/<pr>`) put by one guarded transaction the caller's update linearizes. -/
def PriorityQueue.Enqueue.spec : Prop :=
  ∀ (q c : Loc) (γ : Cluster) (who : Principal) (key val : GoString) (pr : w16)
    (Q : State → State → Nat → Int → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ pqueueAt q c γ who key ∗ etcdPeek γ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (R : Nat) (n : Int) (res : Resp),
             ⌜R ≤ σ.kv.rev ∧ seqNext (σ.kv.storeAt R) (pqPrefix key pr) n ∧
              Step who (seqPutReq (seqBase (pqPrefix key pr)) (seqKey (pqPrefix key pr) n) val (R + 1))
                σ σ' res ∧
              ¬ txnCmpFailed res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' R n res }> }}
    (App (App (Val (q @!! go.GoType.PointerType PriorityQueue.ty @!! go!"Enqueue")) (Val #val)) (Val #pr))
  {{ (err : GoInterface), RET #err;
      (∃ σ σ' R n res, Q σ σ' R n res ∗ ⌜okOrErr res err⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ recipeErrOk err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
