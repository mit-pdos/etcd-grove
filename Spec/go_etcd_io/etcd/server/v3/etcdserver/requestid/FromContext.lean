/-
`requestid.FromContext` (`requestid.go`: returns the `uint64` stored at `requestIDKey{}` in `ctx`,
or `0` if `ctx.Value(requestIDKey{}) == nil`, PR etcd#21401).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.requestid.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.requestid.Assumptions]

/-- `requestid.FromContext(ctx)`:
1. When `ctx` carries the request ID `o` (`ctxReqIDIs ctx o`), returns `o.getD (W64 0)`.
2. On any `mvcc.txnCtx ctx cd`, returns some `id : w64`. -/
abbrev requestid.FromContext.spec : Prop :=
  (∀ (ctx : GoInterfaceOk) (o : Option w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.requestid ∗
        requestid.ctxReqIDIs ctx o }}
      (App (Val (@! requestid.FromContext)) (Val #(GoInterface.ok ctx)))
    {{ (id : w64), RET #id; ⌜id = o.getD (W64 0)⌝ }}) ∧
  (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.requestid ∗
        mvcc.txnCtx ctx cd }}
      (App (Val (@! requestid.FromContext)) (Val #(GoInterface.ok ctx)))
    {{ (id : w64), RET #id; True }})

end spec

end EtcdGrove
end Perennial
