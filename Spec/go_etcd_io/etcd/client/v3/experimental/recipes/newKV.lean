/-
`recipe.newKV(kv, key, val, leaseID)` (`key.go`): `putNewKV`, and a `RemoteKV` for the created key.

**Users**: `newKey` (`Barrier.Hold`), `newEphemeralKV`. Internal.

**Proof sketch**: `putNewKV.spec` with the caller's update; on success allocate the `RemoteKV`
(`rkOwn`'s realization: its fields, `kv` with `kvAt`).

**Changes**: old spec over the recipes' client invariant (`ownRemoteKV`, `keyCreatedAt`); now the
caller's update, any lease.

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

/-- **`newKV(kv, key, val, lease)`**: `putNewKV`'s transaction, and on success the `RemoteKV` of the key at the revision it was created at. -/
def newKV.spec : Prop :=
  ∀ (kv : GoInterface) (γ : Cluster) (who : Principal) (key val : GoString) (lease : w64)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (putNewReq key val (sint.Z lease)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newKV)) (Val #kv))
      (Val #key)) (Val #val)) (Val #lease))

  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (∃ (σ σ' : State) (res : Resp) (rev : w64), Q σ σ' res ∗ ⌜putNewRet res rev err⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗ rkOwn rk γ who { live := true, key := key, rev := rev, val := val }) ∨
         ⌜err ≠ GoInterface.nil ∧ rk = null⌝)) ∨
      (⌜rk = null⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
