/-
`context.WithCancel(context.Background())` with its cancel function not `nil`: Perennial's
`context.wp_WithCancel_Background`, which does not state it (the function is the closure
`func() { c.cancel(true, Canceled, nil) }`), restated with `⌜cancel ≠ func.nil⌝`. `fifo.Schedule`
needs it: it panics when `f.cancel` is `nil`, which before `Stop` is the context's cancel function.
A local copy of Perennial's `wp_WithCancel_gen_of` and `wp_WithCancel_Background_of` with that one
fact added; the general fix, the fact in Perennial's spec, is `notes/perennial-changes.md`'s.
-/
module

public import Perennial.Proof.context.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schedule

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open _root_.Perennial.context

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- `wp_WithCancel_gen_of` (Perennial), with the cancel function not `nil`. -/
theorem wp_WithCancel_gen_nn (parent : GoInterfaceOk) (P Pre : IProp GF)
    (Hprop : ∀ (c : Loc) (γ : ContextNames),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
          ctxField c ↦ (interface.nil : GoInterface) ∗ Pre }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok parent)))
          (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
      {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit ∗ Pre ∗
        isParentCtx parent }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok parent)))
    {{ (c : Loc) (γ : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) #cancel);
        ⌜cancel ≠ func.nil⌝ ∗ cancelSpec cancel γ P ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) }} := by
  wp_start as ⟨#Hcci, Hpre, #Hpar⟩
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, _⟩
  wp_auto
  iapply wp_fupd
  wp_apply wp_withCancel parent P Pre Hprop $$ [$Hcci $Hpre] as %c %γ ⟨#Hc, #Hf⟩
  ipersist c
  imodintro
  iapply HΦ
  iframe #
  isplitr
  · ipureintro; simp [func.nil]
  unfold cancelSpec
  imodintro
  iintro %Φ' #Hp HΦ'
  wp_auto
  wp_apply cancelCtx.wp_cancel c γ P true canceled GoInterface.nil hcanceled $$ [$Hc]
    as #Hclosed
  · iframe #
    simp only [↓reduceIte]
    iexists parent
    iframe #
  iapply HΦ' $$ Hclosed

/-- `context.wp_WithCancel_Background` (Perennial), with the cancel function not `nil`. -/
theorem wp_WithCancel_Background_nn (PDone' : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok backgroundCtxVal)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        ⌜cancel ≠ func.nil⌝ ∗ cancelSpec cancel γ' PDone' ∗
        isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } }} := by
  have isContext_cancelCtx := isContext_cancelCtx_of (GF := GF) (hG := hG)
      cancelCtx.wp_Done cancelCtx.wp_Err cancelCtx.wp_Value sync.atomic.Value.wp_Load
  have wp_propagateCancel_background :=
    wp_propagateCancel_background_of (GF := GF) (hG := hG) cancelCtx.wp_propagateCancel
  iintro %Φ ⟨#Hpkg, #Hcci⟩ HΦ
  iapply wp_WithCancel_gen_nn backgroundCtxVal PDone' iprop(True)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, -, Hf, -⟩ HΦ
        iapply wp_propagateCancel_background c $$ [$Hpkg $Hf] HΦ)
  · iframe #
    isplitl []
    · itrivial
    unfold isParentCtx; ileft; ipureintro; rfl
  inext
  iintro %c %γ %cancel ⟨%Hnn, #Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_background (GF := GF)
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitr
  · ipureintro; exact Hnn
  isplitl []
  · iexact Hcancel
  · iapply isContext_cancelCtx c γ PDone' backgroundCtxVal _ rfl rfl
    iframe #

end proof

end schedule
end EtcdGrove
end Perennial
