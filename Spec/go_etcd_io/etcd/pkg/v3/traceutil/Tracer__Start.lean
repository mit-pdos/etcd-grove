/-
`traceutil.Tracer.Start`: the trust boundary (`pkg/v3/traceutil.Tracer` is an otel `trace.Tracer` (names-only)). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `traceutil.Tracer.Start(ctx, name, opts...)` on the tracer the package variable holds: a
context like `ctx` (the same deadline and `Done`, other values: otel's `ContextWithSpan` is a
`context.WithValue`) and a span (`trace.isSpan`). -/
abbrev traceutil.Tracer.Start.spec : Prop :=
  ∀ (tr ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString)
    (opts : GoSlice),
  {{ globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr ∗
      mvcc.txnCtx ctx cd }}
    (App (App (App (Val #(methods tr.ty go!"Start" tr.v)) (Val #(GoInterface.ok ctx))) (Val #name))
      (Val #opts))
  {{ (ctx' : GoInterfaceOk) (sp : GoInterface), RET (PairV #(GoInterface.ok ctx') #sp);
      (∃ vs : GMap GoInterface GoInterface, mvcc.txnCtx ctx' { cd with Values := vs }) ∗
      trace.isSpan sp }}

end spec

end EtcdGrove
end Perennial
