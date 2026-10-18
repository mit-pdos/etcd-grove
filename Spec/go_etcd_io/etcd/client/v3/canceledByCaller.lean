/-
`clientv3.canceledByCaller(stopCtx, err)` (`client/v3/client.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `canceledByCaller(stopCtx, err)`, for a context whose `Err()` returns client errors
(`ctxErrClient`) and an error grpc's `status` accepts: some boolean (`stopCtx.Err()` and
`errors.Is` against `context.Canceled` and `context.DeadlineExceeded`, which `context`'s facts
give: `ContextReadErrs`). -/
abbrev canceledByCaller.spec : Prop :=
  ∀ (sc : GoInterfaceOk) (scd : context.ContextDesc (IProp GF)) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ctxErrClient sc scd ∗
      go_etcd_io.etcd.cache.v3.statusErrOk err }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.canceledByCaller)) (Val #(GoInterface.ok sc)))
      (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
