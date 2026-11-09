/-
`rpctypes.EtcdError.Error()` (`error.go:252`).

Users: every caller printing or comparing an etcd error's message (`errors.Is` does not call it;
`ErrorDesc` of an `EtcdError` does), the server's `togRPCError` fallback is not reached by one.

Proof sketch: returns the field. (`errVal_errMsg`, a law of the package, is this spec at
`errVal e`.)

Changes: from `specs-ref/.../rpctypes/EtcdError__Error.lean`: unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Api

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

/-- `e.Error()`: the `desc` field. -/
def EtcdError.Error.spec : Prop :=
  ∀ (ee : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes }}
    (App (Val (ee @!! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty @!! go!"Error")) (Val #()))
  {{ RET #ee.desc'; True }}

end spec

end Rpctypes
end EtcdGrove
end Perennial
