/-
`recipe.newKey(kv, key, leaseID)` (`key.go`): `newKV(kv, key, "", leaseID)`.

**Users**: `Barrier.Hold`. Internal.

**Proof sketch**: `newKV.spec`.

**Changes**: as `newKV`'s.

Changes: verify-round: `ErrKeyExists` is the value its variable holds (`putNewRetAt`), not a Lean constant (A3 F4).

**Margin**: none.
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

/-- **`newKey(kv, key, lease)`**: `newKV` with an empty value. -/
def newKey.spec : Prop :=
  ∀ (kv : GoInterface) (γ : Cluster) (who : Principal) (key : GoString) (lease : w64)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (putNewReq key [] (sint.Z lease)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newKey)) (Val #kv))
      (Val #key)) (Val #lease))

  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (∃ (σ σ' : State) (res : Resp) (rev : w64), Q σ σ' res ∗ putNewRetAt res rev err ∗
        ((⌜err = GoInterface.nil⌝ ∗ rkOwn rk γ who { live := true, key := key, rev := rev, val := [] }) ∨
         ⌜err ≠ GoInterface.nil ∧ rk = null⌝)) ∨
      (⌜rk = null⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
