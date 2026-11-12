/-
`(*RemoteKV).Delete()` (`key.go`): delete the key (if not deleted already through this object), and
mark the object deleted (`kv = nil`).

**Users**: `RWMutex.Unlock`, `RUnlock`; `DoubleBarrier.Enter` (too many clients), `Leave` (promoted
through `myKey`). Snippet: `recipes/rwmutex.go`.

**Proof sketch**: live: `kvAt_methods`' `KV.DeleteTriple` at the field's `kv` with `TODO()` and no
option (`OpDelete(key)`: `delReq key`), the caller's update unchanged; then store `nil`. Deleted: return
`nil`; the update is dropped.

**Changes**: old spec over the recipes' client invariant; now the caller's update in W0's shape.

**Margin**: on an object already deleted, nothing is sent and the caller's update is dropped (the code
would allow giving it back).
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

/-- **`rk.Delete()`**: a live object deletes its key (`Delete(key)`, linearized by the caller's update) and becomes deleted; a deleted one returns `nil`. -/
def RemoteKV.Delete.spec : Prop :=
  ∀ (rk : Loc) (γ : Cluster) (who : Principal) (st : RKSt) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ rkOwn rk γ who st ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq st.key)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Delete")) (Val #()))
  {{ (err : GoInterface), RET #err; rkOwn rk γ who { st with live := false } ∗
      if st.live then (∃ σ σ' res, Q σ σ' res ∗ ⌜okOrErr res err⌝) ∨ indefCall err
      else ⌜err = GoInterface.nil⌝ }}

end spec

end Recipes
end EtcdGrove
end Perennial
