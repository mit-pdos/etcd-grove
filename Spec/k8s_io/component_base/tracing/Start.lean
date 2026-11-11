/-
`tracing.Start(ctx, name, attrs...)` (`k8s.io/component-base/tracing`, names-only): a span, and
a context derived from `ctx` (OpenTelemetry's `ContextWithSpan`, a value context: its `Done` and
`Err` are the parent's), so a context the client accepts (`ctxOk`, `ctxErrClient` at the parent's
description) gives one too. Tracing is otherwise a no-op for the store's results. The trust boundary: an axiom, `Proof/k8s_io/component_base/tracing/Start.lean`. Lean-first (no Rocq
counterpart).

A context whose `Done()` is `nil` gives one too (k8s 7e-2, blocker B2, decided by etcd-grove-81:
`ctxNeverDone`): OpenTelemetry's `Tracer.Start` (the noop tracer's and the SDK's) and
`utiltrace.ContextWithTrace` return `context.WithValue` contexts, whose `Done` is the parent's;
checked at the pin by `examples/k8s7e2attack`'s `TestTracingStartDoneNil` (from
`context.Background()`, noop tracer) and `TestTracingStartDoneNilSDK` (an SDK tracer provider's span
in the context).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Calls
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.component_base.tracing.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev tracing.Start.spec : Prop :=
  ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString) (attrs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing ∗ ctxOk ci cd ∗
      ctxErrClient ci cd }}
    (App (App (App (Val (@! k8s_io.component_base.tracing.Start)) (Val #(GoInterface.ok ci)))
      (Val #name)) (Val #attrs))
  {{ (ci' : GoInterfaceOk) (sp : Loc), RET (PairV #(GoInterface.ok ci') #sp);
      ⌜sp ≠ null⌝ ∗ ctxOk ci' cd ∗ ctxErrClient ci' cd ∗
      □ (ctxNeverDone (GoInterface.ok ci) -∗ ctxNeverDone (GoInterface.ok ci')) }}

end spec

end EtcdGrove
end Perennial
