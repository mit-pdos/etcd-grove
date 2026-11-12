/-
`(*applierV3backend).Apply(r, shouldApplyV3, applyFunc)` (`backend.go:46-48`): `applyFunc(r, shouldApplyV3)`.

**Users.** `authApplierV3.Apply` (through the quota applier's promoted `Apply`).

**Proof sketch.** The function value's triple.

**Changes** from `specs-ref`'s file of the same name: unchanged in shape.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **Calls `applyFunc`** with the caller's contract. -/
def applierV3backend.Apply.spec : Prop :=
  ∀ (p r : Loc) (v3 : Bool) (af : GoFunc) (A : IProp GF) (B : Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ A ∗
      ({{ A }} (App (App (Val #af) (Val #r)) (Val #v3)) {{ (ar : Loc), RET #ar; B ar }}) }}
    (App (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"Apply")) (Val #r)) (Val #v3)) (Val #af))
  {{ (ar : Loc), RET #ar; B ar }}

end spec

end Apply
end EtcdGrove
end Perennial
