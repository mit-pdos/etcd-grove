/-
`(*RemoteKV).Revision()` (`key.go`): the revision the key was created at.

**Users**: `DoubleBarrier.Enter`, `RWMutex.waitOnLastRev` (through `myKey`, promoted). Internal getter.

**Proof sketch**: load the field.

**Changes**: unchanged.

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

/-- **`rk.Revision()`**: the creation revision. -/
def RemoteKV.Revision.spec : Prop :=
  ∀ (rk : Loc) (γ : Cluster) (who : Principal) (st : RKSt),
  {{ rkOwn (GF := GF) rk γ who st }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Revision")) (Val #()))
  {{ RET #st.rev; rkOwn rk γ who st }}

end spec

end Recipes
end EtcdGrove
end Perennial
