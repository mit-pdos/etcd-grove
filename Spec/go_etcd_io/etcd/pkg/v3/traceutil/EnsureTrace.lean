/-
`traceutil.EnsureTrace`: the trust boundary (`pkg/v3/traceutil` is names-only). Lean-first.

`EnsureTrace(ctx, lg, op, fields...)` returns `ctx` itself if it carries a trace (`Get(ctx)` not
empty), else `context.WithValue(ctx, TraceKey{}, trace)` for a new trace; and the trace, not
nil (a new one, or the one `ctx` carries). The returned context is described by the input's
descriptor with other values: `WithValue` derives a context with the parent's deadline and
`Done` channel (its `Deadline`/`Done`/`Err` delegate to the parent) and one more value. Which
values is left open (`vs`): nothing here reads a context's values but `traceutil.Get`, whose
trace is opaque. (Perennial has no model of `context.WithValue`.)

The input is a `txnCtx` (2026-10-12): an `isContext`, or a context whose `Done()` is `nil`
(`doneNil`: `context.TODO()`'s, at which the apply package calls the txn package); the output is
the same kind: the derived context's `Done` is its parent's, `nil` or the described channel.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `EnsureTrace(ctx, lg, op, fields...)`: a context like `ctx` (the same deadline and `Done`
channel, other values) and a trace, not nil; an `isContext` of `ctx` stays one of the result
(2026-10-12, the request path's unit 3b: `EnsureTrace` returns `ctx` or
`context.WithValue(ctx, …)`, as `Tracer.Start`'s spec; the server's writing `Txn` passes the
result to `raftRequest`). -/
abbrev traceutil.EnsureTrace.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (op : GoString)
    (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
      mvcc.txnCtx ctx cd }}
    (App (App (App (App (Val (@! traceutil.EnsureTrace)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #op)) (Val #fields))
  {{ (ctx' : GoInterfaceOk) (t : Loc), RET (PairV #(GoInterface.ok ctx') #t);
      ⌜t ≠ null⌝ ∗ ∃ vs : GMap GoInterface GoInterface,
        mvcc.txnCtx ctx' { cd with Values := vs } ∗
        (context.isContext ctx cd -∗ context.isContext ctx' { cd with Values := vs }) }}

end spec

end EtcdGrove
end Perennial
