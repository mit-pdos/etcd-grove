/-
`errors.Is(err, target)` for an error grpc's `status` accepts and a target that is an
`rpctypes.EtcdError` value or a pointer error (unit P3a: the retry interceptor's
`shouldRefreshToken` compares `rpctypes.Error(err)` with `ErrUserEmpty`, `ErrInvalidAuthToken`,
`ErrAuthOldRevision`, `EtcdError` values, and `isSafeRetry` compares the error with
`ErrGRPCNotSupportedForLearner`, a `*status.Error`): the trust boundary. Perennial's
`errors.wp_Is` needs a nil or pointer target and the error tree of `err` with its `Is` methods'
specs; an `EtcdError` target is a struct (comparable: Go's `Is` compares `err == target`, which
does not panic for a comparable target).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` with `err` an error grpc's `status` accepts (`statusErrOk`: a leaf
error whose `Is` method, if any, returns) and `target` an `rpctypes.EtcdError` value or a pointer
error, returns some boolean. -/
abbrev errors.IsStatusErr.spec : Prop :=
  ∀ (err target : GoInterface),
  ((∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      target = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) ∨
    ∃ tii, target = GoInterface.ok tii ∧ _root_.Perennial.errors.IsPointerError tii) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ statusErrOk err }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
