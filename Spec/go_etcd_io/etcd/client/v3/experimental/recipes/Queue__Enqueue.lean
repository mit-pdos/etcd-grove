/-
`(*Queue).Enqueue(val)` (`queue.go`): `newUniqueKV(kv, keyPrefix, val)`.

**Users**: `T/v3_queue_test.go:52` (one writer, in order), `:207` (many writers). Snippet:
`recipes/queue.go` (`ReqFIFO`, `ReqEveryItemOnce`).

**Proof sketch**: `isClient_KV`; `newUniqueKV.spec` with the caller's update unchanged; drop the
`RemoteKV`.

**Changes**: old spec over the recipes' client invariant with an enqueue token; now the caller's
update: the item is a new key under the prefix, created by one transaction (its mod revision, the
order `Dequeue` follows, is that transaction's revision).

Changes: verify-round: `ErrKeyExists` is the value its variable holds (`putNewRetAt`), not a Lean constant (A3 F4).

**Margin**: none.
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

/-- **`q.Enqueue(val)`**: a new key `kp/<n>` with `val`, created by one transaction the caller's update linearizes. -/
def Queue.Enqueue.spec : Prop :=
  ∀ (q c : Loc) (γ : Cluster) (who : Principal) (kp val : GoString)
    (Q : State → State → GoString → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ queueAt q c γ who kp ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (res : Resp),
             ⌜uniqueKeyIn kp k ∧ Step who (putNewReq k val 0) σ σ' res ∧ ¬ txnCmpFailed res⌝ ∗
             etcdState γ σ',
           COMM Q σ σ' k res }> }}
    (App (Val (q @!! go.GoType.PointerType Queue.ty @!! go!"Enqueue")) (Val #val))
  {{ (err : GoInterface), RET #err;
      (∃ (σ σ' : State) (k : GoString) (res : Resp) (rev : w64), Q σ σ' k res ∗ putNewRetAt res rev err) ∨ indefCall err }}

end spec

end Recipes
end EtcdGrove
end Perennial
