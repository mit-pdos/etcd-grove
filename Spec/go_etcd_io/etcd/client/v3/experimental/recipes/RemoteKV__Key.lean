/-
`(*RemoteKV).Key()` (`key.go`): the key field.

**Users**: `DoubleBarrier.Leave` (through `myKey`, promoted). Internal getter.

**Proof sketch**: `rkOwn`'s realization: load the field.

**Changes**: unchanged (over `rkOwn`, which now names the cluster).

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

/-- **`rk.Key()`**: the key. -/
def RemoteKV.Key.spec : Prop :=
  ∀ (rk : Loc) (γ : Cluster) (who : Principal) (st : RKSt),
  {{ rkOwn (GF := GF) rk γ who st }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Key")) (Val #()))
  {{ RET #st.key; rkOwn rk γ who st }}

end spec

end Recipes
end EtcdGrove
end Perennial
