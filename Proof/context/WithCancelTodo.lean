/-
Proof of `Spec/context/WithCancelTodo.lean`: Perennial's `context.wp_WithCancel_TODO_of`
(mit-pdos/perennial#670) at `PDone' = True`, `closedchan`'s fact from `context`'s initialization
(`isClosedchanInit_of_init`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.WithCancelTodo
public import Perennial.Proof.context.WithCancelGen

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

theorem context.WithCancelTodo.wp_proof
    (wp_withCancel : _root_.Perennial.context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : _root_.Perennial.context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel :
      _root_.Perennial.context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : _root_.Perennial.context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : _root_.Perennial.context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : _root_.Perennial.context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : _root_.Perennial.sync.atomic.Value.Load.spec (GF := GF) (hG := hG)) :
    context.WithCancelTodo.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Hcci := _root_.Perennial.context.isClosedchanInit_of_init $$ Hpkg
  wp_apply (_root_.Perennial.context.wp_WithCancel_TODO_of wp_withCancel wp_cancelCtx_cancel
      wp_propagateCancel wp_cancelCtx_Done wp_cancelCtx_Err wp_cancelCtx_Value wp_VLoad
      iprop(True)) $$ [$Hpkg $Hcci] as %ctx' %γ' %cancel ⟨Hcancel, Hc, -, Hf⟩
  iapply HΦ
  unfold _root_.Perennial.context.cancelSpec
  iframe

end proof

end EtcdGrove
end Perennial
