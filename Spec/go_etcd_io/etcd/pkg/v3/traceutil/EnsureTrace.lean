/-
`traceutil.EnsureTrace` (`trace.go`: `ctx` itself if it carries a trace that is not empty, else
`context.WithValue(ctx, TraceKey{}, newTrace(...))`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14): the trace owned (`ownTrace`,
`notes/decisions.md`, "Traces on the request path").

The returned context is described by the input's descriptor with other values: `WithValue`
derives a context with the parent's deadline and `Done` channel. The input is a `txnCtx`
(2026-10-12): an `isContext`, or a context whose `Done()` is `nil` (`context.TODO()`'s, at which
the apply package calls the txn package); the output is the same kind.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Perennial.Proof.context
public import Proof.google_golang_org.grpc.metadata.Incoming
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Proof.context.LibKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- `EnsureTrace(ctx, lg, op, fields...)`, `ctx` carrying the trace `o` (owned by the caller, empty
or not as `e`), the fields owned: a context like `ctx` (an `isContext` of `ctx` stays one),
carrying the trace `t` returned, owned, not empty: the caller's if not empty, else a new one; and
(2026-10-28, the auth plan's E3zb) `ctx`'s incoming gRPC metadata (`metadata.incomingOf`: `ctx`
itself, or a `context.WithValue` of it); and (R8, 2026-11-07) `ctx`'s span fact
(`trace.spanCtxOk`: `WithValue` at `TraceKey{}`, not otel's key, delegates otel's key to `ctx`).
(Premise fixes 6) The logger nil or a zap logger: a new trace keeps it (`ownTrace`). -/
abbrev traceutil.EnsureTrace.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (o : Option Loc) (e : Bool)
    (lg : Loc) (op : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx o ∗
      traceutil.ownTraceOpt o e ∗ traceutil.ownFields fields ∗ zapLoggerOrNil lg }}
    (App (App (App (App (Val (@! traceutil.EnsureTrace)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #op)) (Val #fields))
  {{ (ctx' : GoInterfaceOk) (t : Loc), RET (PairV #(GoInterface.ok ctx') #t);
      ⌜t ≠ null ∧ ∀ t0, o = some t0 → e = false → t = t0⌝ ∗ traceutil.ownTrace t false ∗
      traceutil.ctxTraceIs ctx' (some t) ∗
      ⌜metadata.incomingOf (GoInterface.ok ctx') = metadata.incomingOf (GoInterface.ok ctx)⌝ ∗
      ∃ vs : GMap GoInterface GoInterface,
        mvcc.txnCtx ctx' { cd with Values := vs } ∗
        (context.isContext ctx cd -∗ context.isContext ctx' { cd with Values := vs }) ∗
        □ (trace.spanCtxOk ctx -∗ trace.spanCtxOk ctx') ∗
        □ (context.libCtxOk ctx -∗ context.libCtxOk ctx') }}

end spec

end EtcdGrove
end Perennial
