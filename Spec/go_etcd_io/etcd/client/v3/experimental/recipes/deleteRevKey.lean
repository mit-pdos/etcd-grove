/-
`recipe.deleteRevKey(kv, key, rev)` (`client/v3/experimental/recipes/client.go`): delete `key` if its
mod revision is `rev`, in one transaction.

**Users**: `claimFirstKey` (each candidate), `Queue.Dequeue` and `PriorityQueue.Dequeue` (the item a
watch delivered). Snippet: `recipes/queue.go` (through `Dequeue`).

**Proof sketch**: `kvAt_methods` (W0) gives `KV.TxnTriple` at `kv`: `Txn(context.TODO())` (W0's
`TODO.spec` naming `todoCtxVal`, then the entailment `ctxPrin_todo`: `ctxOk`, `ctxPrin who ctx who`; the call's principal is the client's `who`) returns `txnAt iv γ who ctx TxnSt.empty`; `ModRevision(key)`, `Compare(.., "=",
rev)` (W0's `ModRevision.spec`, `Compare.spec`: an `int64`, so `CmpArg.i64`) give the comparison of
`deleteRevReq`; `OpDelete(key)` (W0) its operation; `If`, `Then`, `Commit` (`txnAt_methods`; `Commit` at `lo = 0`, `authLb γ 0` by definition; each builder's post is
`txnAt` of the value it returns, the chained call's receiver) send `deleteRevReq key rev` with the caller's update unchanged (a write: exclusive). `Commit`'s
`txnReply`: on success read `Succeeded` (`txnRespOwn_unfold`); an etcd error is `errVal e`. The
indefinite case is `Commit`'s.

**Changes**: old `deleteRevKey.spec` (specs-ref) took the recipes' client invariant
(`isRecipesKV kv pfx`, the keys under a prefix only the recipes write) and gave a deletion token
(`revKeyDeleted`, `etcdRevToken`); now the caller's atomic update over the cluster's state, in W0's
KV shape, with every answer (the comparison failing, an etcd error) linearized. No prefix, no size
bound (`recipesStrMax`), no revision bound.

**Margin**: none (the transaction's answer is all the code reads).
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

/-- **`deleteRevKey(kv, key, rev)`**: the transaction `deleteRevReq key rev`, linearized by the caller's update; returns `true` iff it deleted the key. -/
def deleteRevKey.spec : Prop :=
  ∀ (kv : GoInterface) (γ : Cluster) (who : Principal) (key : GoString) (rev : w64)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (deleteRevReq key (sint.Z rev)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.deleteRevKey)) (Val #kv))
      (Val #key)) (Val #rev))
  {{ (ok : Bool) (err : GoInterface), RET (PairV #ok #err);
      (∃ σ σ' res, Q σ σ' res ∗ ⌜deleteRevRet res ok err⌝) ∨ (⌜ok = false⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
