/-
`(*clientv3.valCtx).Done()` (`client/v3/watch.go`; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `vc.Done()`: the package's `valCtxCh` (never closed). -/
abbrev valCtx.Done.spec : Prop :=
  ∀ (vc : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientWatchVars }}
    (App (Val (vc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.valCtx.ty @!! go!"Done"))
      (Val #()))
  {{ (ch : GoChan), RET #ch; globalAddr go_etcd_io.etcd.client.v3.valCtxCh ↦□ ch }}

end spec

end EtcdGrove
end Perennial
