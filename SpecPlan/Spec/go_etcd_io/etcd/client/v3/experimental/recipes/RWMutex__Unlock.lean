/-
`(*RWMutex).Unlock()` (`rwmutex.go`): `myKey.Delete()`.

**Users**: `T/v3_lock_test.go:350`. Snippet: `recipes/rwmutex.go`.

**Proof sketch**: `RemoteKV.Delete.spec` on `myKey`'s embedded `RemoteKV` (`ekOwn`, the promoted
method) with the caller's update unchanged.

**Changes**: old spec over the recipes' client invariant; now the caller's update over the delete.

**Premise**: `myKey` set (`some`): `nil` panics (a nil dereference in the promoted call).

**Margin**: as `RemoteKV.Delete`'s.
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

/-- **`m.Unlock()`**: the delete of the held key, linearized by the caller's update (nothing if it was deleted already). -/
def RWMutex.Unlock.spec : Prop :=
  ∀ (m : Loc) (γ : Cluster) (who : Principal) (id : w64) (pfx : GoString) (st : RKSt)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ rwmOwn m γ who id pfx (some st) ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq st.key)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (Val (m @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #()))
  {{ (err : GoInterface), RET #err; rwmOwn m γ who id pfx (some { st with live := false }) ∗
      if st.live then (∃ σ σ' res, Q σ σ' res ∗ ⌜okOrErr res err⌝) ∨ indefCall err
      else ⌜err = GoInterface.nil⌝ }}

end spec

end Recipes
end EtcdGrove
end Perennial
