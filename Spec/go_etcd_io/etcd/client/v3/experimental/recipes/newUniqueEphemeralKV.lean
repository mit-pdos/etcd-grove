/-
`recipe.newUniqueEphemeralKV(s, prefix, val)` (`key.go`): `newEphemeralKV` of `prefix/<UnixNano>`,
retried with a new time while the key exists.

**Users**: `newUniqueEphemeralKey` (`DoubleBarrier.Enter`, `RWMutex.Lock`, `RLock`). Internal.

**Proof sketch**: as `newUniqueKV`'s, with `newEphemeralKV.spec` (the session's lease) for each attempt.

**Changes**: old spec over `concurrency.isSession` and the recipes' client invariant; now 1d's
`isSession s c γ id` with `isClient c γ who`, and the caller's update.

Changes: verify-round: `ErrKeyExists` is the value its variable holds (`putNewRetAt`), not a Lean constant (A3 F4).

**Margin**: as `newUniqueKV`'s.
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

/-- **`newUniqueEphemeralKV(s, prefix, val)`**: a key `prefix/<n>` that did not exist, created with `val` and the session's lease by one transaction the caller's update linearizes. -/
def newUniqueEphemeralKV.spec : Prop :=
  ∀ (s c : Loc) (γ : Cluster) (who : Principal) (id : w64) (pre val : GoString)
    (Q : State → State → GoString → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ Concurrency.isSession s c γ id ∗ isClient c γ who ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (res : Resp),
             ⌜uniqueKeyIn pre k ∧ Step who (putNewReq k val (sint.Z id)) σ σ' res ∧ ¬ txnCmpFailed res⌝ ∗
             etcdState γ σ',
           COMM Q σ σ' k res }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueEphemeralKV)) (Val #s))
      (Val #pre)) (Val #val))

  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (∃ (σ σ' : State) (k : GoString) (res : Resp) (rev : w64), Q σ σ' k res ∗ putNewRetAt res rev err ∗
        ((⌜err = GoInterface.nil⌝ ∗ ekOwn rk γ who { live := true, key := k, rev := rev, val := val }) ∨
         ⌜err ≠ GoInterface.nil ∧ rk = null⌝)) ∨
      (⌜rk = null⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
