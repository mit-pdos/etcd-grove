/-
`recipe.newUniqueKV(kv, prefix, val)` (`key.go`): `putNewKV` of `prefix/<time.Now().UnixNano()>`,
retried with a new time while the key exists.

**Users**: `Queue.Enqueue`. Internal.

**Proof sketch**: a loop carrying the caller's update; each attempt `fmt.Sprintf("%s/%v", prefix,
UnixNano)` (Perennial's `fmt`, `time` specs: the key is `uniqueKeyIn prefix k`), then `putNewKV.spec`
with an update built from the caller's: a failed comparison (`σ' = σ`) aborts it (the key existed:
`ErrKeyExists`, `errors.Is` true, retry); any other answer commits it (`Q σ σ' k res`); an indefinite
error is returned (`errors.Is(err, ErrKeyExists)` is false: `errorsIs_recipeErr`).

**Changes**: old spec over the recipes' client invariant; now the caller's update, the key's shape
stated (`uniqueKeyIn`).

Changes: verify-round: `ErrKeyExists` is the value its variable holds (`putNewRetAt`), not a Lean constant (A3 F4).

**Margin**: the key's suffix is a decimal time, not tied to a clock (the model has none).
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

/-- **`newUniqueKV(kv, prefix, val)`**: a key `prefix/<n>` that did not exist, created with `val` (no lease) by one transaction the caller's update linearizes (attempts on existing keys change nothing). -/
def newUniqueKV.spec : Prop :=
  ∀ (kv : GoInterface) (γ : Cluster) (who : Principal) (pre val : GoString)
    (Q : State → State → GoString → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (res : Resp),
             ⌜uniqueKeyIn pre k ∧ Step who (putNewReq k val 0) σ σ' res ∧ ¬ txnCmpFailed res⌝ ∗
             etcdState γ σ',
           COMM Q σ σ' k res }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueKV)) (Val #kv))
      (Val #pre)) (Val #val))

  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (∃ (σ σ' : State) (k : GoString) (res : Resp) (rev : w64), Q σ σ' k res ∗ putNewRetAt res rev err ∗
        ((⌜err = GoInterface.nil⌝ ∗ rkOwn rk γ who { live := true, key := k, rev := rev, val := val }) ∨
         ⌜err ≠ GoInterface.nil ∧ rk = null⌝)) ∨
      (⌜rk = null⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
