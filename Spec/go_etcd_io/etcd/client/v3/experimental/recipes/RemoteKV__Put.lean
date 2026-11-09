/-
`(*RemoteKV).Put(val)` (`key.go`): put `val` at the key (no lease; the object's value field is not
updated).

**Users**: none in the package or its callers (exported). Kept (it had a spec).

**Proof sketch**: `kvAt_methods`' `KV.PutTriple` at the field's `kv` (live: not `nil`) with `TODO()`
and no option (`putReq0 key val 0`), the caller's update unchanged.

**Changes**: old spec over the recipes' client invariant; now the caller's update.

**Premise**: the object is live: a deleted one's `kv` is `nil`, and the call panics (a nil
interface's method).

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

/-- **`rk.Put(val)`** on a live object: `Put(key, val)`, linearized by the caller's update. -/
def RemoteKV.Put.spec : Prop :=
  ∀ (rk : Loc) (γ : Cluster) (who : Principal) (st : RKSt) (val : GoString)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ rkOwn rk γ who st ∗ ⌜st.live = true⌝ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.put (putReq0 st.key val 0)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Put")) (Val #val))
  {{ (err : GoInterface), RET #err; rkOwn rk γ who st ∗
      ((∃ σ σ' res, Q σ σ' res ∗ ⌜okOrErr res err⌝) ∨ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
