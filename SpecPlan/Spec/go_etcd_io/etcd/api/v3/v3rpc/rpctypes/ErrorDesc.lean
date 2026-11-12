/-
`rpctypes.ErrorDesc(err)` (`api/v3rpc/rpctypes/error.go:274`).

Users: `rpctypes.Error` (this package), the client's `isSafeRetryMutableRPC` (1c), the package's
`errStringToError` initializer.

Proof sketch: `status.FromError(err)` (its spec over `errView`); `ok`: `s.Message()` (`msg`); not
`ok`: `err.Error()` (`errMsg_call`: `msg`).

Changes: from `specs-ref/.../rpctypes/ErrorDesc.lean`: over `errView` (the result was
`errDesc err`).

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

/-- `rpctypes.ErrorDesc(err)`: the message of the error's status view. -/
def ErrorDesc.spec : Prop :=
  ∀ (err : GoInterface) (c : w32) (msg : GoString) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ∗ Grpc.errView err c msg ok }}
    (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc)) (Val #err))
  {{ RET #msg; True }}

end spec

end Rpctypes
end EtcdGrove
end Perennial
