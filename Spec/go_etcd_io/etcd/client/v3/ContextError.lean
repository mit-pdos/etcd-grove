/-
`clientv3.ContextError(ctx, err)` (`client/v3/client.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil errCellOk)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `ContextError(ctx, err)` of a client error: `nil` for `nil`; otherwise a non-nil client error
(`rpctypes.Error(err)`, or, for a gRPC `DeadlineExceeded`/`Canceled` when the context is done,
the context's error). The error is one grpc's `status` accepts (`statusErrOk`, unit P3a:
`rpctypes.Error` and `status.FromError` call its `Error()` and `GRPCStatus()`), and so is the
result; and (D37) the result is no caller's `errors.New` value (`errCellOk`) if `err` is none; and
(k8s 7e-1) a non-nil result keeps `err`'s description (`rpctypes.Error`'s) or is the context's error
(`ctxErrClient`'s, of a context error's shape and message, `ctxErrIs`; incomingof Part B,
`examples/axiomcx/incomingof-real` `TestContextErrorRaw`); and (incomingof Part B (3), 2026-11-18) a
context error (whose `Error()` stably returns `m` at the call, a parameter as `status.FromError.spec`'s)
comes back as a context error, or with a context message as its description (`rpctypes.Error` maps a
message that is a key of `errStringToError`; none is, `TestContextErrorTwice`). -/
abbrev ContextError.spec : Prop :=
  ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (err : GoInterface) (m : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ctxErrClient ci cd ∗
      ⌜err ≠ GoInterface.nil → clientErr err⌝ ∗ statusErrOk err ∗
      (∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ → go_etcd_io.etcd.cache.v3.errorMsgIs e m) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.ContextError)) (Val #(GoInterface.ok ci)))
      (Val #err))
  {{ (err' : GoInterface), RET #err';
      ⌜(err = GoInterface.nil → err' = GoInterface.nil) ∧
        (err ≠ GoInterface.nil → err' ≠ GoInterface.nil ∧ clientErr err')⌝ ∗ statusErrOk err' ∗
      -- (2026-10-23, D37) no caller's `errors.New` value if `err` is none (the context's error never)
      □ (errCellOk err -∗ errCellOk err') ∗
      -- (k8s 7e-1, 2026-11-10; incomingof Part B, 2026-11-17/18) the description kept, or the context's
      -- error, returned as it is (`ctxErrClient`'s: Go's context message and a context error's shape)
      (⌜err = GoInterface.nil ∨
          go_etcd_io.etcd.cache.v3.errDesc err' = go_etcd_io.etcd.cache.v3.errDesc err⌝ ∨
        go_etcd_io.etcd.cache.v3.ctxErrIs err') ∗
      -- (incomingof Part B, (3), 2026-11-18) a context error (message `m` at the call) comes back as a
      -- context error, or with a context message as its description
      (⌜¬ ∃ e : GoInterfaceOk, err = GoInterface.ok e ∧ go_etcd_io.etcd.cache.v3.ctxErrMsg m ∧
          go_etcd_io.etcd.cache.v3.ctxErrShape e⌝ ∨
        go_etcd_io.etcd.cache.v3.ctxErrIs err' ∨ ⌜go_etcd_io.etcd.cache.v3.ctxErrMsg (go_etcd_io.etcd.cache.v3.errDesc err')⌝) }}

end spec

end EtcdGrove
end Perennial
