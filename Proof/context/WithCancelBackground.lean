/-
Proof of `Spec/context/WithCancelBackground.lean` (rafthttp stage 4d; a trust-boundary axiom until
k8s 7f-4 Addendum T-i, 2026-11-13, which proves it from Perennial's `wp_WithCancel_gen`, as
`traceutil.wp_WithCancelBackground_noTrace` does, to give `context.bgCancelChild`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.context.WithCancelBackground
public import Perennial.Proof.context.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- Go's `WithCancel(Background())`: a `*cancelCtx` whose parent is never done (`propagateCancel`
returns at once), cancelled only by its `cancel`, whose parent field is `Background()`
(`context.bgCancelChild`). Proved from Perennial's `wp_WithCancel_gen` (k8s 7f-4, Addendum T-i;
an axiom before). -/
theorem context.WithCancelBackground.wp_proof : context.WithCancelBackground.spec (GF := GF) (hG := hG) := by
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
  · iunfold context.bgCancelChild
    iexists c
    iframe #
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
