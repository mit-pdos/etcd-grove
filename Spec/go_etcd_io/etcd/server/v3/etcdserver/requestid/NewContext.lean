/-
`requestid.NewContext` (`requestid.go`: `context.WithValue(ctx, requestIDKey{}, requestID)`,
PR etcd#21401).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.requestid.Defs
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.requestid.Assumptions]

/-- `requestid.NewContext(ctx, id)`: returns a `valueCtx` over `ctx` carrying `some id` at
`requestIDKey{}`, preserving `ctx`'s deadline, `Done`, trace, and values at other named keys. -/
abbrev requestid.NewContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.requestid }}
    (App (App (Val (@! requestid.NewContext)) (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (c : GoInterface), RET #c; ⌜c ≠ GoInterface.nil⌝ ∗
      ∃ (c' : GoInterfaceOk) (vs : GMap GoInterface GoInterface), ⌜c = GoInterface.ok c'⌝ ∗
        □ (∀ cd : context.ContextDesc (IProp GF), mvcc.txnCtx ctx cd -∗
          mvcc.txnCtx c' { cd with Values := vs }) ∗
        □ (∀ cd : context.ContextDesc (IProp GF), context.isContext ctx cd -∗
          context.isContext c' { cd with Values := vs }) ∗
        □ (∀ o : Option Loc, traceutil.ctxTraceIs ctx o -∗ traceutil.ctxTraceIs c' o) ∗
        requestid.ctxReqIDIs c' (some id) ∗
        □ (∀ (n : GoString) (x : val) (Φ : val → IProp GF),
          ⌜n ≠ go!"go.etcd.io/etcd/server/v3/etcdserver/requestid.requestIDKey"⌝ -∗
          WP (App (Val #(methods ctx.ty go!"Value" ctx.v))
            (Val #(interface.mkOk (go.GoType.Named n []) x))) {{ Φ }} -∗
          WP (App (Val #(methods c'.ty go!"Value" c'.v))
            (Val #(interface.mkOk (go.GoType.Named n []) x))) {{ Φ }}) }}

end spec

end EtcdGrove
end Perennial
