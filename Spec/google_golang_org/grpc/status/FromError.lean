/-
`status.FromError(err)` (grpc-go, assumed: `status/status.go`).

Users: the client's `ContextError`, `isSafeRetryMutableRPC`, `isSafeRetryImmutableRPC`,
`isHaltErr`, `isUnavailableErr` (W0, 1b, 1c), `rpctypes.ErrorDesc`/`Error` (this batch),
`v3rpc.isClientCtxErr` (this batch), leasing's `acquire` (1e).

Why true: `FromError(nil)` is `(nil, true)`; for an error with a `GRPCStatus()` (a status error, or
one wrapping one: `errors.As`) it returns that status and `true`; for any other error, a new
`Unknown` status with `err.Error()` as its message and `false`. It reads the error only (the
`GRPCStatus()` of grpc's own type returns its stored status; `Error()` per `errMsg`, stable).

Changes: from `specs-ref/Spec/google_golang_org/grpc/status/FromError.lean`: the code and message
as the arguments of `errView` (was the opaque functions `statusCode err`, `errDesc err` of an error
value, which needed a stable-`Error()` side condition, `errorMsgIs`; here `errMsg` is that
condition, persistent).

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `status.FromError(err)` of an error seen as (`code`, `msg`, `ok`): a status with them, and
`ok`. -/
def FromError.spec : Prop :=
  ∀ (err : GoInterface) (code : w32) (msg : GoString) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ errView err code msg ok }}
    (App (Val (@! google_golang_org.grpc.status.FromError)) (Val #err))
  {{ (s : Loc) (b : Bool), RET (PairV #s #b); ⌜b = ok⌝ ∗ statusAt s code msg }}

end spec

end Grpc
end EtcdGrove
end Perennial
