/-
**What a context answers at Kubernetes' own keys** (premise-fixes-7, part A, 2026-11-11; the
Scope's A.2). Lean-first. The k8s counterpart of `Proof/context/LibKeys.lean`, in a file of its own
so that grpc's vocabulary does not import k8s.

* `audit.auditKeyAny`: the apiserver audit package's `auditKey` (`const auditKey key = iota`), read
  by `audit.AuditContextFrom` (`ctx.Value(auditKey).(*AuditContext)`): any value is accepted (the
  assertion fails on another type; an `*AuditContext` only the audit package can store, and a nil
  one is tested), so the fact is that `Value` returns.
* `utiltrace.traceKeyAny`: `k8s.io/utils/trace`'s `ContextTraceKey{}`, read by `utiltrace.FromContext`
  (`ctx.Value(ContextTraceKey{}).(*Trace)`): not a `*Trace`, or one `utiltrace` made (`builtTrace`).
* `rtrace.traceKeyAny`: `runtime/trace`'s `traceContextKey{}`, read by `trace.NewTask(ctx, ...)`'s
  `fromContext` (`ctx.Value(traceContextKey{}).(*Task)`, then the task's `id`; go1.27.3
  `runtime/trace/annotation.go:39, 65`), which the otel SDK calls on every span it starts while Go's
  execution tracer is on (`recordingSpan.runtimeTrace`, sdk/trace v1.47.0 `span.go:844-849`): not a
  `*Task`, or a non-nil one (`rtrace.taskRes`; a nil one panics). (The context sweep's fixes,
  2026-11-13, decided by etcd-grove-81, `notes/ctx-sweep-fixes.md`: without it a context whose
  `Value` panics there refuted `tracing.Start.spec`, `examples/premisefix/k8sctx`'s
  `TestStartRuntimeTraceKeyPanics`.)
* `flowcontrol.initSignalKeyAny`: the apiserver flowcontrol package's
  `priorityAndFairnessInitializationSignalKey` (`priorityAndFairnessKeyType(0)`), read by
  `utilflowcontrol.WatchInitialized(ctx)` (`apf_context.go:42-53`: `ctx.Value(key).(InitializationSignal)`,
  then `Signal()` on a non-nil one), which the etcd3 store's `Watch` calls on the caller's goroutine
  (`watcher.go:158`): nil, or not an `InitializationSignal` (`flowcontrol.initSignalRes`), so that
  `WatchInitialized` calls nothing. (k8s 7f-5, T5-b, decided by etcd-grove-81, Q3: the narrow choice,
  what the driver and the cacher's reflector pass; APF's own `*initializationSignal`, which
  kube-apiserver's APF filter stores for a watch request that bypasses the cache, is not admitted.
  Without it a context panicking at that key, or holding a foreign signal whose `Signal` panics, met
  `k8sCtxOk` and made `Watch` panic: `examples/premisefix/watcherctx`'s
  `TestWatchInitializedKeyPanics`, `TestWatchInitializedForeignSignal`.)
* `k8sctx.k8sCtxOk ctx`: the four facts and `context.libCtxOk ctx` (otel's span key among them).

Producers: the same as `libCtxOk`'s (`k8sCtxOk_of_nil`, `k8sCtxOk_background`, `k8sCtxOk_todo`,
`k8sCtxOk_bgFrom`).
-/
module

public import Proof.context.LibKeys
public import GeneratedProof.k8s_io.utils.trace
public import GeneratedProof.runtime.trace
public import Code.k8s_io.apiserver.pkg.audit
public import Code.k8s_io.apiserver.pkg.util.flowcontrol

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- (opaque; TRUSTED) **A `*Trace` `k8s.io/utils/trace` made**: the value
`utiltrace.ContextWithTrace` stores under `ContextTraceKey{}`, a non-nil `*Trace` returned by
`utiltrace.New` or `(*Trace).Nest` (k8s utils `be93311217bd` `trace/trace.go`; k8s
`component-base/tracing` `Start` stores `utiltrace.FromContext(ctx).Nest(...)`, never nil: `Nest`
of a nil `*Trace` returns `New`'s). Its methods (`Step`, `LogIfLong`, `Nest`) return. -/
opaque utiltrace.builtTrace [GooseExts] : GoInterface → Prop

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The apiserver audit package's `auditKey` as `ctx.Value` takes it. -/
abbrev audit.auditKeyAny : GoInterface :=
  interface.mkOk k8s_io.apiserver.pkg.audit.key.ty k8s_io.apiserver.pkg.audit.auditKey

/-- `k8s.io/utils/trace`'s `ContextTraceKey{}` as `ctx.Value` takes it. -/
abbrev utiltrace.traceKeyAny : GoInterface :=
  interface.mkOk k8s_io.utils.trace.ContextTraceKey.ty #(zero_val k8s_io.utils.trace.ContextTraceKey)

/-- What `utiltrace.FromContext`'s callers accept: not a `*Trace`, or one `utiltrace` made. -/
def utiltrace.traceRes (v : GoInterface) : Prop :=
  (∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
      vi.ty ≠ go.GoType.PointerType k8s_io.utils.trace.Trace.ty) ∨
    utiltrace.builtTrace v

/-- `runtime/trace`'s `traceContextKey{}` as `ctx.Value` takes it. -/
abbrev rtrace.traceKeyAny : GoInterface :=
  interface.mkOk _root_.Perennial.runtime.trace.traceContextKey.ty
    #(zero_val _root_.Perennial.runtime.trace.traceContextKey)

/-- What `runtime/trace.NewTask` accepts of its parent context's task: not a `*Task`, or a non-nil
one (`fromContext(ctx).id` dereferences it; a `*Task` outside the package is `&Task{}` or one
`NewTask` returned, whose `id` it reads and nothing else). -/
def rtrace.taskRes (v : GoInterface) : Prop :=
  ∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
    vi.ty = go.GoType.PointerType _root_.Perennial.runtime.trace.Task.ty → vi.v ≠ #null

/-- The apiserver flowcontrol package's `priorityAndFairnessInitializationSignalKey` as `ctx.Value`
takes it (`Convert priorityAndFairnessKeyType go.any`). -/
abbrev flowcontrol.initSignalKeyAny : GoInterface :=
  interface.mkOk k8s_io.apiserver.pkg.util.flowcontrol.priorityAndFairnessKeyType.ty
    k8s_io.apiserver.pkg.util.flowcontrol.priorityAndFairnessInitializationSignalKey

/-- (k8s 7f-5, T5-b) What `utilflowcontrol.WatchInitialized` accepts at its key, so that it calls
nothing: nil, or a value whose dynamic type is not in `InitializationSignal`'s type set (the
assertion `.(InitializationSignal)` fails; Perennial's `typeSetContains`, as `TypeAssert2` decides). -/
def flowcontrol.initSignalRes (v : GoInterface) : Prop :=
  v = GoInterface.nil ∨ ∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
    go.typeSetContains vi.ty k8s_io.apiserver.pkg.util.flowcontrol.InitializationSignal.ty = false

/-- **A context's Kubernetes values are well formed** (persistent): its audit key answers, its
`utiltrace` trace is one `utiltrace` made, its `runtime/trace` task is not a nil `*Task`, its APF
initialization signal is nil or not a signal (k8s 7f-5, T5-b), and its libraries' values are
(`libCtxOk`). -/
def k8sctx.k8sCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(context.valueAt ctx audit.auditKeyAny (fun _ => True) ∗
    context.valueAt ctx utiltrace.traceKeyAny utiltrace.traceRes ∗
    context.valueAt ctx rtrace.traceKeyAny rtrace.taskRes ∗
    context.valueAt ctx flowcontrol.initSignalKeyAny (flowcontrol.initSignalRes (sem := sem)) ∗
    context.libCtxOk ctx)

instance k8sctx.k8sCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (k8sctx.k8sCtxOk (GF := GF) ctx) := by
  unfold k8sctx.k8sCtxOk; infer_instance

/-- **What `tracing.SpanFromContext(ctx)` needs** (persistent): `ctx` is not nil, its span is
otel's and its `utiltrace` trace `utiltrace`'s. -/
def k8sctx.spanCtx (ctx : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜ctx = GoInterface.ok ci⌝ ∗ trace.spanValOk ci ∗
    context.valueAt ci utiltrace.traceKeyAny utiltrace.traceRes)

instance k8sctx.spanCtx_persistent (ctx : GoInterface) :
    Persistent (k8sctx.spanCtx (GF := GF) ctx) := by
  unfold k8sctx.spanCtx; infer_instance

/-- The four keys. -/
abbrev k8sctx.k8sKeys : List GoInterface :=
  [audit.auditKeyAny, utiltrace.traceKeyAny, rtrace.traceKeyAny, flowcontrol.initSignalKeyAny]

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem k8sctx.libCtxOk_of_k8sCtxOk (ctx : GoInterfaceOk) :
    k8sctx.k8sCtxOk (GF := GF) ctx ⊢ context.libCtxOk ctx := by
  iintro #H
  unfold k8sctx.k8sCtxOk
  icases H with ⟨-, -, -, -, #H⟩
  iexact H

theorem k8sctx.spanCtx_of_k8sCtxOk (ctx : GoInterfaceOk) :
    k8sctx.k8sCtxOk (GF := GF) ctx ⊢ k8sctx.spanCtx (GoInterface.ok ctx) := by
  iintro #H
  unfold k8sctx.k8sCtxOk context.libCtxOk
  icases H with ⟨-, #Ht, -, -, -, -, -, #Hs⟩
  unfold k8sctx.spanCtx
  iexists ctx
  iframe #
  ipureintro; rfl

theorem k8sctx.spanValOkNil_of_spanCtx (ctx : GoInterface) :
    k8sctx.spanCtx (GF := GF) ctx ⊢ trace.spanValOkNil ctx := by
  iintro #H
  unfold k8sctx.spanCtx trace.spanValOkNil
  icases H with ⟨%ci, %Hci, #Hs, -⟩
  iright
  iexists ci
  iframe #
  ipureintro; exact Hci

/-- A context answering `nil` at each key. -/
theorem k8sctx.k8sCtxOk_of_nil (ctx : GoInterfaceOk) :
    (□ ∀ k : GoInterface, ⌜k ∈ k8sctx.k8sKeys ∨ k ∈ context.libKeys⌝ -∗
      context.valueAt (GF := GF) ctx k (· = GoInterface.nil)) ⊢ k8sctx.k8sCtxOk ctx := by
  iintro #H
  unfold k8sctx.k8sCtxOk
  isplitl []
  · iapply context.valueAt_mono _ _ (· = GoInterface.nil)
    · intro _ _; trivial
    iapply H; ipureintro; simp
  isplitl []
  · iapply context.valueAt_mono _ _ (· = GoInterface.nil)
    · intro v hv; subst hv; left; intro vi h; cases h
    iapply H; ipureintro; simp
  isplitl []
  · iapply context.valueAt_mono _ _ (· = GoInterface.nil)
    · intro v hv vi h; subst hv; cases h
    iapply H; ipureintro; simp
  isplitl []
  · iapply context.valueAt_mono _ _ (· = GoInterface.nil)
    · intro v hv; left; exact hv
    iapply H; ipureintro; simp
  iapply context.libCtxOk_of_nil
  imodintro
  iintro %k %hk
  iapply H; ipureintro; right; exact hk

variable [package_sem : _root_.Perennial.context.Assumptions]

theorem k8sctx.k8sKeys_notIntPtr (k : GoInterface) (hk : k ∈ k8sctx.k8sKeys ∨ k ∈ context.libKeys) :
    _root_.Perennial.context.notIntPtrKey k := by
  rcases hk with hk | hk
  · intro ki h
    simp only [k8sctx.k8sKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp only [GoInterface.ok.injEq] at h <;> subst h
    · unfold k8s_io.apiserver.pkg.audit.key.ty; simp
    · unfold k8s_io.utils.trace.ContextTraceKey.ty; simp
    · unfold _root_.Perennial.runtime.trace.traceContextKey.ty; simp
    · unfold k8s_io.apiserver.pkg.util.flowcontrol.priorityAndFairnessKeyType.ty; simp
  · exact context.libKeys_notIntPtr k hk

theorem k8sctx.k8sCtxOk_of_ctxValueNil (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      (□ ∀ k : GoInterface, ⌜_root_.Perennial.context.notIntPtrKey k⌝ -∗
        _root_.Perennial.context.ctxValue ctx k (· = GoInterface.nil)) ⊢
      k8sctx.k8sCtxOk ctx := by
  iintro ⟨#Hpkg, #H⟩
  iapply k8sctx.k8sCtxOk_of_nil
  imodintro
  iintro %k %hk
  iapply context.valueAt_of_ctxValue
  iframe #
  iapply H
  ipureintro; exact k8sctx.k8sKeys_notIntPtr k hk

theorem k8sctx.k8sCtxOk_background :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      k8sctx.k8sCtxOk _root_.Perennial.context.backgroundCtxVal := by
  iintro #Hpkg
  iapply k8sctx.k8sCtxOk_of_ctxValueNil
  iframe #
  imodintro
  iintro %k -
  iapply _root_.Perennial.context.ctxValue_background

theorem k8sctx.k8sCtxOk_todo :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      k8sctx.k8sCtxOk _root_.Perennial.context.todoCtxVal := by
  iintro #Hpkg
  iapply k8sctx.k8sCtxOk_of_ctxValueNil
  iframe #
  imodintro
  iintro %k -
  iapply _root_.Perennial.context.ctxValue_todo

theorem k8sctx.k8sCtxOk_bgFrom (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxValueFrom _root_.Perennial.context.backgroundCtxVal ctx ⊢
      k8sctx.k8sCtxOk ctx := by
  iintro ⟨#Hpkg, #Hf⟩
  iapply k8sctx.k8sCtxOk_of_ctxValueNil
  iframe #
  imodintro
  iintro %k %hk
  unfold _root_.Perennial.context.ctxValueFrom
  iapply Hf
  · ipureintro; exact hk
  iapply _root_.Perennial.context.ctxValue_background

end laws

end EtcdGrove
end Perennial
