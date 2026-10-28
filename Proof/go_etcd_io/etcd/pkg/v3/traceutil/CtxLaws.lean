/-
**The trace a derived context carries** (M2's freeze repair, 2026-10-28, `notes/m2-plan.md`): the
auto-compactor's context, `WithCancel(Background())`, carries no trace, which `EtcdServer.Compact`'s
`traceutil.EnsureTrace` needs. A module of its own: it imports Perennial's context proofs, which
`Defs.lean`'s importers need not rebuild for. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Perennial.Proof.context.Results
public import Spec.context.WithCancelBackground

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- **A `*cancelCtx` child of `context.Background()` carries no trace** (M2's freeze repair,
`notes/m2-plan.md`): its `Value(TraceKey{})` is not `&cancelCtxKey`, so `cancelCtx.Value` asks its
parent (`value(c.Context, key)`), `Background()`, whose `Value` returns `nil`. From the parent field
(`ctxField c ↦□ Background()`, which Perennial's `WithCancel` spec does not export: this lemma
unfolds Perennial's context code, pending the law that a derived context's `Value` delegates to its
parent, `notes/perennial-changes.md`). -/
theorem traceutil.ctxTraceIs_cancelCtx_background (c : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxField c ↦□ (interface.ok _root_.Perennial.context.backgroundCtxVal : GoInterface) ⊢
      traceutil.ctxTraceIs (GF := GF)
        (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c) none := by
  iintro ⟨#Hpkg, #Hf⟩
  iunfold traceutil.ctxTraceIs
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_auto
  wp_func_call
  wp_auto
  ihave Hinv : iprop(c_ptr ↦ (GoInterface.ok _root_.Perennial.context.backgroundCtxVal) ∗
      key_ptr ↦ traceutil.traceKeyVal) $$ [c key]
  · iframe
  wp_for Hinv
  icases Hinv with ⟨c, key⟩
  wp_auto
  wp_for_post
  iapply HΦ
  ipureintro; left; rfl

/-- **`WithCancel(Background())`, carrying no trace** (M2's freeze repair): `context.WithCancelBackground`'s
statement (`Spec/context/WithCancelBackground.lean`) and `traceutil.ctxTraceIs ctx' none`, proved from
Perennial's `WithCancel` (`wp_WithCancel_gen`, whose post gives the new context's parent field) and
`ctxTraceIs_cancelCtx_background`; the auto-compactor's constructors use it in place of the
trust-boundary axiom `context.WithCancelBackground.wp_proof`. -/
theorem traceutil.wp_WithCancelBackground_noTrace :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (Val (@! _root_.Perennial.context.WithCancel))
        (Val #(GoInterface.ok _root_.Perennial.context.backgroundCtxVal)))
    {{ (ctx' : GoInterfaceOk) (γ' : _root_.Perennial.context.ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        _root_.Perennial.context.cancelSpec cancel γ' iprop(True) ∗
        _root_.Perennial.context.isContext ctx'
          { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } ∗
        traceutil.ctxTraceIs ctx' none }} := by
  iintro %Φ #Hpkg HΦ
  ihave #Hcci := _root_.Perennial.context.isClosedchanInit_of_init $$ Hpkg
  iapply _root_.Perennial.context.wp_WithCancel_gen
      _root_.Perennial.context.backgroundCtxVal iprop(True) iprop(True)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, -, Hf, -⟩ HΦ
        iapply _root_.Perennial.context.wp_propagateCancel_background c $$ [$Hpkg $Hf] HΦ)
  · iframe #
    isplitl []
    · itrivial
    unfold _root_.Perennial.context.isParentCtx; ileft; ipureintro; rfl
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := _root_.Perennial.context.deadlineSpec_background (GF := GF)
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitl []
  · iexact Hcancel
  isplitl []
  · iapply _root_.Perennial.context.isContext_cancelCtx c γ iprop(True)
      _root_.Perennial.context.backgroundCtxVal _ rfl rfl
    iframe #
  · iapply traceutil.ctxTraceIs_cancelCtx_background c
    iframe #

end lemmas

end EtcdGrove
end Perennial
