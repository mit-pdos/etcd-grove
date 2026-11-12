/-
`(*Barrier).Hold()` (`barrier.go`): create the barrier key (no lease) if absent.

**Users**: `T/v3_barrier_test.go:44` (holds), `:45` (a second hold errs), `T/v3_closed_watch_test.go:176`.
Snippet: `recipes/barrier.go` (`ReqHoldTwice`, `ReqWaitAfterRelease`).

**Proof sketch**: `isClient_KV` (W0) the client's `KV` field; `newKey.spec` with lease `NoLease` (`0`)
and the caller's update unchanged.

**Changes**: old spec over the recipes' client invariant, with a `held` token; now the caller's
update over the transaction, every answer linearized (`ErrKeyExists`: the key existed).

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

/-- **`b.Hold()`**: the transaction `putNewReq key "" 0`, linearized by the caller's update: `nil` if it created the key, `ErrKeyExists` if the key existed. -/
def Barrier.Hold.spec : Prop :=
  ∀ (b c : Loc) (γ : Cluster) (who : Principal) (key : GoString)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ barrierAt b c γ who key ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (putNewReq key [] 0) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (Val (b @!! go.GoType.PointerType Barrier.ty @!! go!"Hold")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (∃ (σ σ' : State) (res : Resp) (rev : w64), Q σ σ' res ∗ putNewRetAt res rev err) ∨ indefCall err }}

end spec

end Recipes
end EtcdGrove
end Perennial
