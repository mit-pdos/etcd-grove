/-
`errors.Is(err, target)` for an error grpc's `status` accepts and a target that is an
`rpctypes.EtcdError` value or a pointer error (unit P3a: the retry interceptor's
`shouldRefreshToken` compares `rpctypes.Error(err)` with `ErrUserEmpty`, `ErrInvalidAuthToken`,
`ErrAuthOldRevision`, `EtcdError` values, and `isSafeRetry` compares the error with
`ErrGRPCNotSupportedForLearner`, a `*status.Error`): the trust boundary. Perennial's
`errors.wp_Is` needs a nil or pointer target and the error tree of `err` with its `Is` methods'
specs; an `EtcdError` target is a struct (comparable: Go's `Is` compares `err == target`, which
does not panic for a comparable target).

(2026-10-21, D29) `true` only if the two errors have the same description (`errDesc`). True of Go:
for a leaf error (`statusErrOk`: no `Unwrap`), `Is` is `err == target` or `err.Is(target)`; equal
errors have equal descriptions; `*status.Error`'s `Is` compares the two statuses (`proto.Equal`),
messages included; `EtcdError` has no `Is` (`==` compares `code` and `desc`).
(incomingof Part B, approved by the user 2026-11-17 via etcd-grove-03) For an `EtcdError` target, `true`
of an error without an `Is(error) bool` method only if it is an `EtcdError`: Go's `is` (go1.27.3
`src/errors/wrap.go`) on a leaf error answers `err == target` (interface equality compares the dynamic
types first) or `err.Is(target)`; an error with an `Is` method may answer `true` at another type
(`examples/axiomcx/incomingof` `TestIsEtcdTarget`, `incomingof-real` `TestRealTypes`). A fact of types,
the same in every run. What rules a context error out (`ctxErrShape`).
(errdesc stage 2b, 2026-11-21) The descriptions are the per-run relations `descIs err m` and
`descIs target m'` of the precondition, when the caller fixes them (`dm = some (m, m')`, `isDescs`; until
then the pure `errDesc`), and `true` means `err = target`
(Go's `==` shortcut, go1.27.3 `src/errors/wrap.go:54-57`, which reads no description: with no agreement
law, two `descIs` of one value say nothing of each other) or `m = m'` (`err.Is(target)`: grpc's
`*status.Error.Is` compares the two statuses, messages included, `internal/status/status.go:222-228`;
`grpcErrMethodsOk`'s `Is` clause). For an `EtcdError` target the value pin (`descIs_etcdError_eq`) turns
the first into the second.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` with `err` an error grpc's `status` accepts (`statusErrOk`: a leaf
error whose `Is` method, if any, returns) and `target` an `rpctypes.EtcdError` value, a pointer
error or (2026-10-18, item 1, the client lease: `canceledByCaller` compares with
`context.DeadlineExceeded`) `deadlineExceededError{}` (Go's `Is` compares `err == target` first, which
for this comparable target compares the dynamic types, then the values of an equal type, a field-less
struct), returns some boolean. (ctx-leaf-fix, 2026-11-25) The last case was "a non-nil `SafeMapKey`",
which since Perennial's P8c only `nil` and pointers are (so it added nothing to the pointer case):
`notes/axiom-review/ctx-readerrs-vacuity.md`. -/
abbrev errors.IsStatusErr.spec : Prop :=
  ∀ (err target : GoInterface) (dm : _root_.Option (GoString × GoString)),
  ((∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      target = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) ∨
    (∃ tii, target = GoInterface.ok tii ∧ _root_.Perennial.errors.IsPointerError tii) ∨
    target = interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
      #(zero_val _root_.Perennial.context.deadlineExceededError)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ statusErrOk err ∗ isDescs err target dm }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b; ⌜b = true → (∀ m m', dm = some (m, m') → err = target ∨ m = m') ∧
      ((∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
          target = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) →
        ∀ e : GoInterfaceOk, err = GoInterface.ok e →
          methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) →
          e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)⌝ }}

end spec

end EtcdGrove
end Perennial
