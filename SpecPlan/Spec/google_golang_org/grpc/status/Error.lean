/-
`status.Error(c, msg)` (grpc-go, assumed: `status/status.go`).

Users: rpctypes' `ErrGRPC*` initializers (this batch, `init.spec`), the client's
`WatchResponse.Err` (1b), `v3rpc.togRPCError`'s fallback (`status.Error(codes.Unknown,
err.Error())`).

Why true: `Error(c, msg)` is `New(c, msg).Err()`: `nil` for `OK`, else a fresh `*status.Error`
holding the status, whose `GRPCStatus()` returns it.

Changes: from `specs-ref/Spec/google_golang_org/grpc/status/Error.lean`: `statusErr` (was
`statusErrOk` and `errDesc err = msg`).

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

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

/-- `status.Error(c, msg)` for a code other than `OK`: a status error with them. -/
def Error.spec : Prop :=
  ∀ (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ ⌜c ≠ cOK⌝ }}
    (App (App (Val (@! google_golang_org.grpc.status.Error)) (Val #c)) (Val #msg))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ statusErr err c msg }}

end spec

end Grpc
end EtcdGrove
end Perennial
