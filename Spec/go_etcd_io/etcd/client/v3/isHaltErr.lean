/-
`clientv3.isHaltErr(ctx, err)` (`client/v3/client.go`; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `isHaltErr(ctx, err)` for a context and an error grpc's `status` accepts: `true` if the
context is done or the error's status code is neither `Unavailable` (`14`) nor `Internal`
(`13`); so when it returns `false`, `err` is `nil` or has one of those codes. -/
abbrev isHaltErr.spec : Prop :=
  ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ context.isContext ci cd ∗
      statusErrOk err }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.isHaltErr)) (Val #(GoInterface.ok ci))) (Val #err))
  {{ (b : Bool), RET #b;
      ⌜b = false → (err = GoInterface.nil ∨ statusCode err = W32 14 ∨ statusCode err = W32 13)⌝ }}

end spec

end EtcdGrove
end Perennial
