/-
`(*clientv3.blockLogger).recordWait(d)` (`client/v3/block_logger.go`; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `l.recordWait(d)` keeps the logger's `A x` (its `logFunc`'s). -/
abbrev blockLogger.recordWait.spec : Prop :=
  ∀ (α : Type) (A : α → IProp GF) (x : α) (bl : Loc) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isBlockLogger bl A ∗ A x }}
    (App (Val (bl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.blockLogger.ty @!! go!"recordWait"))
      (Val #d))
  {{ RET #(); A x }}

end spec

end EtcdGrove
end Perennial
