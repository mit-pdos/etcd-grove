/-
`recipe.newEphemeralKV(s, key, val)` (`key.go`): `newKV` with the session's client's `KV` and its lease.

**Users**: `newUniqueEphemeralKV`. Internal.

**Proof sketch**: `s.Client()`, `s.Lease()` (1d's `Session.Client`, `Session.Lease` over `sessionAt`:
`isClient c γ who`, the lease `id`); `isClient_KV` (W0) the `KV` field; `newKV.spec` with the caller's
update; wrap the `RemoteKV` (copied into the `EphemeralKV`: `ekOwn`).

**Changes**: old spec took `concurrency.isSession` and the recipes' client invariant; now `sessionAt`
(1d's slot) and the caller's update.

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

/-- **`newEphemeralKV(s, key, val)`**: `putNewKV` with the session's lease, linearized by the caller's update, and on success the `EphemeralKV`. -/
def newEphemeralKV.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (id : w64) (key val : GoString)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ sessionAt s γ who id ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (putNewReq key val (sint.Z id)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newEphemeralKV)) (Val #s))
      (Val #key)) (Val #val))

  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (∃ (σ σ' : State) (res : Resp) (rev : w64), Q σ σ' res ∗ ⌜putNewRet res rev err⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗ ekOwn rk γ who { live := true, key := key, rev := rev, val := val }) ∨
         ⌜err ≠ GoInterface.nil ∧ rk = null⌝)) ∨
      (⌜rk = null⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
