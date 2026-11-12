/-
`rpctypes.EtcdError.Code()` (`error.go:248`).

Users: clients inspecting an etcd error's code (Kubernetes' `interpretWatchError` through
`status`-like checks; none of the verified callers).

Proof sketch: returns the field.

Changes: from `specs-ref/.../rpctypes/EtcdError__Code.lean`: unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rpctypes

open Iris Iris.BI EtcdModel ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `e.Code()`: the `code` field. -/
def EtcdError.Code.spec : Prop :=
  ∀ (ee : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes }}
    (App (Val (ee @!! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty @!! go!"Code")) (Val #()))
  {{ RET #ee.code'; True }}

end spec

end Rpctypes
end EtcdGrove
end Perennial
