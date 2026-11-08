/-
**The span a derived context carries** (2026-11-06, the fix of
`notes/axiom-review/otel-spanfromcontext-todo.md`): `trace.spanCtxOk` of `context.Background()`, of
a `*cancelCtx` child of it (`WithCancel(Background())`), and of a `context.WithValue` child, at a key
other than otel's, of a context that has it (from `context.WithValue`'s delegation to its parent).
The run contexts gRPC makes have it (`grpcRunCtx`, `spanCtxOk_of_runCtx`), and so do the contexts
`traceutil.Tracer.Start` returns (its spec). A `WithCancel`, `WithTimeout` or `WithDeadline` child
of a general parent is not covered: Perennial's specs of them do not say that the child's `Value`
at another key is its parent's (the pending law of `notes/perennial-changes.md`, as for
`traceutil.ctxTraceIs`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Perennial.Proof.context.Results
public import Spec.context.WithValue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_opentelemetry_io.otel

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- **A context whose `Value(currentSpanKey)` returns `nil` has a span-key fact.** -/
theorem trace.spanCtxOk_of_nil (ctx : GoInterfaceOk) :
    □ ({{ True }} (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #trace.spanKeyVal))
      {{ RET #GoInterface.nil; True }}) ⊢ trace.spanCtxOk (GF := GF) ctx := by
  iintro #H
  iunfold trace.spanCtxOk
  iexists (fun v => v = GoInterface.nil)
  isplitr
  · imodintro
    iintro %v %hv
    ileft; ipureintro; exact hv
  imodintro
  iintro %Φ
  imodintro
  iintro - HΦ
  iapply H
  · itrivial
  inext
  iintro -
  iapply HΦ
  ipureintro; rfl

/-- **`context.Background()` has no span**: its `Value` (promoted from `emptyCtx`) returns `nil`. -/
theorem trace.spanCtxOk_background :
    ⊢ trace.spanCtxOk (GF := GF) _root_.Perennial.context.backgroundCtxVal := by
  iapply trace.spanCtxOk_of_nil
  imodintro
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

/-- **A `*cancelCtx` child of `context.Background()` has no span** (`WithCancel(Background())`):
its `Value(currentSpanKey)` is not `&cancelCtxKey`, so `cancelCtx.Value` asks its parent
(`value(c.Context, key)`), `Background()`, whose `Value` returns `nil`. From the parent field, as
`traceutil.ctxTraceIs_cancelCtx_background`. -/
theorem trace.spanCtxOk_cancelCtx_background (c : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxField c ↦□
        (interface.ok _root_.Perennial.context.backgroundCtxVal : GoInterface) ⊢
      trace.spanCtxOk (GF := GF)
        (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c) := by
  iintro ⟨#Hpkg, #Hf⟩
  iapply trace.spanCtxOk_of_nil
  imodintro
  wp_start
  wp_auto
  wp_func_call
  wp_auto
  ihave Hinv : iprop(c_ptr ↦ (GoInterface.ok _root_.Perennial.context.backgroundCtxVal) ∗
      key_ptr ↦ trace.spanKeyVal) $$ [c key]
  · iframe
  wp_for Hinv
  icases Hinv with ⟨c, key⟩
  wp_auto
  wp_for_post
  iapply HΦ
  itrivial

/-- **A `valueCtx` child at a key other than otel's has its parent's span** (`context.WithValue`):
`valueCtx.Value(currentSpanKey)` compares the key with its own, of another type (unequal), and asks
its parent. From `context.WithValue`'s delegation clause (its last conjunct, for the pure property
of `spanCtxOk`'s result). -/
theorem trace.spanCtxOk_valueCtx (parent key c' : GoInterfaceOk) (v : GoInterface)
    (hkey : key.ty ≠ trace.traceContextKeyType.ty) :
    (□ (∀ (k : GoInterface) (R : GoInterface → Prop),
          ⌜k = GoInterface.ok key ∨ ∀ k' : GoInterfaceOk, k = GoInterface.ok k' → k'.ty ≠ key.ty⌝ -∗
          ⌜k = GoInterface.ok key → R v⌝ -∗
          (⌜k ≠ GoInterface.ok key⌝ -∗
            {{ True }} (App (Val #(methods parent.ty go!"Value" parent.v)) (Val #k))
            {{ (w : GoInterface), RET #w; ⌜R w⌝ }}) -∗
          {{ True }} (App (Val #(methods c'.ty go!"Value" c'.v)) (Val #k))
          {{ (w : GoInterface), RET #w; ⌜R w⌝ }})) ∗
      trace.spanCtxOk (GF := GF) parent ⊢ trace.spanCtxOk (GF := GF) c' := by
  iintro ⟨#Hd, #Hp⟩
  iunfold trace.spanCtxOk at Hp
  icases Hp with ⟨%R, #HR, #Hv⟩
  iunfold trace.spanCtxOk
  iexists R
  isplitr
  · iexact HR
  imodintro
  have hne : trace.spanKeyVal ≠ GoInterface.ok key := by
    intro h
    simp only [trace.spanKeyVal, interface.mkOk, GoInterface.ok.injEq] at h
    exact hkey (by rw [← h])
  iapply Hd
  · ipureintro
    right
    intro k' hk'
    simp only [trace.spanKeyVal, interface.mkOk, GoInterface.ok.injEq] at hk'
    rw [← hk']
    exact fun h => hkey h.symm
  · ipureintro
    intro h; exact absurd h hne
  · iintro -
    iexact Hv

/-- **`context.WithValue`'s keys are not otel's span key**: the five key types its spec admits
(`Spec/context/WithValue.lean`) are etcd's, not `traceContextKeyType`. -/
theorem trace.withValueKey_ne_span (key : GoInterfaceOk)
    (h : key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty ∨
        key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty ∨
        key.ty = go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty ∨
        key = ⟨go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty,
          #(zero_val go_etcd_io.etcd.pkg.v3.traceutil.TraceKey)⟩ ∨
        key.ty = go_etcd_io.etcd.client.v3.keepAliveCtxKey.ty) :
    key.ty ≠ trace.traceContextKeyType.ty := by
  have hn : ∀ n : GoString, n ≠ go!"go.opentelemetry.io/otel/trace.traceContextKeyType" →
      go.GoType.Named n [] ≠ trace.traceContextKeyType.ty := by
    intro n hn h
    simp only [trace.traceContextKeyType.ty, go.GoType.Named.injEq] at h
    exact hn h.1
  rcases h with h | h | h | h | h
  · rw [h]; simp only [go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty]
    exact hn _ (by decide)
  · rw [h]; simp only [go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty]
    exact hn _ (by decide)
  · rw [h]; simp only [go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty]
    exact hn _ (by decide)
  · subst h; simp only [go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty]
    exact hn _ (by decide)
  · rw [h]; unfold go_etcd_io.etcd.client.v3.keepAliveCtxKey.ty
    exact hn _ (by decide)

end lemmas

end EtcdGrove
end Perennial
