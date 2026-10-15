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
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `ContextError(ctx, err)` of a client error: `nil` for `nil`; otherwise a non-nil client error
(`rpctypes.Error(err)`, or, for a gRPC `DeadlineExceeded`/`Canceled` when the context is done,
the context's error). The error is one grpc's `status` accepts (`statusErrOk`, unit P3a:
`rpctypes.Error` and `status.FromError` call its `Error()` and `GRPCStatus()`), and so is the
result. -/
abbrev ContextError.spec : Prop :=
  ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ctxErrClient ci cd ∗
      ⌜err ≠ GoInterface.nil → clientErr err⌝ ∗ statusErrOk err }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.ContextError)) (Val #(GoInterface.ok ci)))
      (Val #err))
  {{ (err' : GoInterface), RET #err';
      ⌜(err = GoInterface.nil → err' = GoInterface.nil) ∧
        (err ≠ GoInterface.nil → err' ≠ GoInterface.nil ∧ clientErr err')⌝ ∗ statusErrOk err' }}

end spec

end EtcdGrove
end Perennial
