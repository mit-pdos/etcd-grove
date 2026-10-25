/-
`(*Client).connectionPoolClosedError()` (`client/v3/channel_pool.go:83`, PR #21765): returns
`c.ctx.Err()` if non-nil, and `status.Error(codes.Canceled, "etcdclient: client connection is closing")`
otherwise.

As proved below, whenever `c.ctx` is already `Done` (`st = .Done`, which always holds after
`c.Close()` because `c.Close()` calls `c.cancel()` before setting `c.channels = nil`), `c.ctx.Err()`
is non-nil, so `connectionPoolClosedError()` always takes the early `return err` branch and the
`status.Error(codes.Canceled, ...)` fallback is unreachable dead code for closed clients.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Spec.google_golang_org.grpc.status.Error

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open go_etcd_io.etcd.cache.v3 (statusErrOk errCellOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

abbrev Client.connectionPoolClosedError.spec : Prop :=
  ∀ (cl : Loc) (dq : DFrac) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (st : Broadcast),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦{dq} GoInterface.ok ci ∗
      ctxErrClient ci cd ∗
      (match st with
       | .Done => context.ContextClosed cd.Done_gn
       | _ => iprop(True)) }}
    (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty)
      go!"connectionPoolClosedError" #cl)) (Val #()))
  {{ (err : GoInterface), RET #err;
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦{dq} GoInterface.ok ci ∗
      ⌜err ≠ GoInterface.nil ∧ (st = .Done → clientErr err)⌝ ∗ statusErrOk err ∗
      (match st with
       | .Done => errCellOk err
       | _ => iprop(True)) }}

end spec

end EtcdGrove
end Perennial
