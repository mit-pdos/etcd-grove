/-
**`WithCancel(Background())` with `Err() = Canceled` after `cancel()`** (`Spec/context/WithCancelBackground.lean`,
`spec_canceled`), proved from Perennial's `context.wp_WithCancel_Background_canceled` (mit-pdos/perennial#705:
`cancelCtxInv` records the errors a context's `err` may take, and a child of `Background()` may take only
`Canceled`'s value, which its own `cancel()` stores). An interim axiom until that change (2026-11-25;
`notes/perennial-changes.md`, "`context.WithCancel`'s `cancel` does not say `Err()` returns `Canceled`").
What gRPC's robustness driver's `ctx-canceled` section needs (grpc's `toRPCErr` maps `context.Canceled`
to `codes.Canceled`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.WithCancelBackground

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- See the file header: Perennial's `context.wp_WithCancel_Background_canceled`, its cancel function's
triple split into `cancelSpec` (with `ContextClosed`) and the one leaving `errIsCanceled`, and the new
context's `Context` field restated as `context.bgCancelChild`. -/
theorem context.WithCancelBackground.wp_proof_canceled :
    context.WithCancelBackground.spec_canceled (GF := GF) (hG := hG) := by
  iintro %Φ #Hpkg HΦ
  iapply _root_.Perennial.context.wp_WithCancel_Background_canceled $$ Hpkg
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hctx, #Hcc, #Hf⟩
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)
  isplitl []
  · unfold _root_.Perennial.context.cancelSpec
    imodintro
    iintro %Φ' - HΦ'
    iapply Hcancel
    inext
    iintro #Hcl -
    iapply HΦ' $$ Hcl
  isplitl []
  · iexact Hctx
  isplitl []
  · iunfold context.bgCancelChild
    iexists c
    iframe #
    ipureintro; rfl
  isplitl []
  · iexact Hcc
  imodintro
  iintro %Φ' HΦ'
  iapply Hcancel
  inext
  iintro - #He
  iapply HΦ'
  iunfold _root_.Perennial.context.errIsCanceled at He
  icases He with ⟨%e, #Hce, #Herr⟩
  unfold context.errIsCanceled
  iexists e
  iframe #

end proof

end EtcdGrove
end Perennial
