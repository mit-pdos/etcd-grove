/-
`(*Barrier).Release()` (`barrier.go`): delete the barrier key.

**Users**: `T/v3_barrier_test.go:75`. Snippet: `recipes/barrier.go` (`ReqWaitAfterRelease`).

**Proof sketch**: `isClient_KV`; `KV.DeleteTriple` (`kvAt_methods`) with `b.ctx` and no option.

**Changes**: old spec over the recipes' client invariant; now the caller's update.

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

/-- **`b.Release()`**: `Delete(key)`, linearized by the caller's update. -/
def Barrier.Release.spec : Prop :=
  ∀ (b c : Loc) (γ : Cluster) (who : Principal) (key : GoString)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ barrierAt b c γ who key ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq key)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (Val (b @!! go.GoType.PointerType Barrier.ty @!! go!"Release")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (∃ σ σ' res, Q σ σ' res ∗ ⌜okOrErr res err⌝) ∨ indefCall err }}

end spec

end Recipes
end EtcdGrove
end Perennial
