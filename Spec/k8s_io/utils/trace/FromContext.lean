/-
`trace.FromContext(ctx)` (`k8s.io/utils/trace`, `be93311217bd` `trace/trace.go:309-314`): the value
of `ctx` at `ContextTraceKey{}` if it is a `*Trace`, else `nil`. Lean-first (prove-metrics3,
2026-11-21: for component-base's `tracing.SpanFromContext`, proved over the real code).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys

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
variable [package_sem : k8s_io.utils.trace.Assumptions]

/-- **`trace.FromContext(ctx)`**, of a context whose value at `ContextTraceKey{}` is not a `*Trace`
or one `utiltrace` made (`utiltrace.traceRes`), returns `nil` or such a trace. -/
abbrev trace.FromContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.trace ∗
      context.valueAt ctx utiltrace.traceKeyAny utiltrace.traceRes }}
    (App (Val (@! k8s_io.utils.trace.FromContext)) (Val #(GoInterface.ok ctx)))
  {{ (t : Loc), RET #t; ⌜t = null ∨
      utiltrace.builtTrace (interface.mkOk (go.GoType.PointerType k8s_io.utils.trace.Trace.ty) #t)⌝ }}

end spec

end EtcdGrove
end Perennial
