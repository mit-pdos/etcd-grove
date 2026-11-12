/-
`recipe.claimFirstKey(kv, kvs)` (`client.go`): try `deleteRevKey` on each key-value in order; return
the first one deleted, `nil` if every one was gone (or rewritten), or the first error.

**Users**: `Queue.Dequeue`, `PriorityQueue.Dequeue` (with the one key-value their `Get` returned).
Internal: the spec mirrors the code.

**Proof sketch**: a loop over `kvs` carrying the caller's update. For element `m` (`keyValueOwn`:
its key and mod revision), `deleteRevKey.spec` with an update built from the caller's: open it
(`etcdState γ σ`); `etcdLb_reach` from `etcdLb γ σg` gives `Reach σg σ`; on the transaction's
answer: success: the premise gives `P σ σ' m`, commit the caller's update (`Q σ σ' m`); a failed
comparison or an etcd error (`σ' = σ`: `kvStep`'s error and empty-commit cases, a refusal): abort,
keeping the caller's update for the next element (an etcd error returns it: `err = errVal e`). An
indefinite error loses it (it may fire later). The loop's end: the update back, `nil`.

**Changes**: old spec took the recipes' client invariant and an ordering certificate
(`claimedBefore`); now the caller's update over any relation `P` its successful claims meet.

**Margin**: the claimed element's index is not returned (its pointer is).
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

/-- **`claimFirstKey(kv, kvs)`**: the first of `kvs` deleted at its mod revision (a step the caller's update `P` admits, given the premise), or `nil` with the update back. -/
def claimFirstKey.spec : Prop :=
  ∀ (kv : GoInterface) (γ : Cluster) (who : Principal) (sl : GoSlice) (ps : List Loc)
    (ms : List KeyValueM) (σg : State) (P : State → State → KeyValueM → Prop)
    (Q : State → State → KeyValueM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗ sl ↦*□ ps ∗ ([∗list] p; m ∈ ps; ms, keyValueOwn p DFrac.discard m) ∗
      etcdLb γ σg ∗
      ⌜∀ σ σ' m res, Reach σg σ → m ∈ ms →
        Step who (deleteRevReq m.key (sint.Z m.modRevision)) σ σ' res → txnSucceeded res →
        P σ σ' m⌝ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (m : KeyValueM), ⌜P σ σ' m⌝ ∗ etcdState γ σ', COMM Q σ σ' m }> }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.claimFirstKey)) (Val #kv))
      (Val #sl))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (i : Nat) (m : KeyValueM) (σ σ' : State),
        ⌜ps[i]? = some p ∧ ms[i]? = some m⌝ ∗ Q σ σ' m) ∨
      (⌜p = null ∧ (err = GoInterface.nil ∨ ∃ e, err = errVal e)⌝ ∗
        AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
          <{ ∀∀ (σ' : State) (m : KeyValueM), ⌜P σ σ' m⌝ ∗ etcdState γ σ', COMM Q σ σ' m }>) ∨
      (⌜p = null⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
