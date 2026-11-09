/-
`(*RemoteKV).Value()` (`key.go`): the value it was created with.

**Users**: none in the package or its callers (exported). Kept (it had a spec).

**Proof sketch**: load the field.

**Changes**: unchanged.

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

/-- **`rk.Value()`**: the value it was created with. -/
def RemoteKV.Value.spec : Prop :=
  ∀ (rk : Loc) (γ : Cluster) (who : Principal) (st : RKSt),
  {{ rkOwn (GF := GF) rk γ who st }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Value")) (Val #()))
  {{ RET #st.val; rkOwn rk γ who st }}

end spec

end Recipes
end EtcdGrove
end Perennial
