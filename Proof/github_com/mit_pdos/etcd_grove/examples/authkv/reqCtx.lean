/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/reqCtx.lean`: the timeout context
(`client.wp_WithTimeout_bg`), and for the bad principal its token appended (C3); the appended
context's `Err()` returns client errors as every `isContext`'s does (`ctxErrClientAllW_of`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.reqCtx
public import Spec.google_golang_org.grpc.metadata.AppendToOutgoingContext
public import Proof.google_golang_org.grpc.metadata.OutgoingNoValues

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem reqCtx.wp_proof
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Append : metadata.AppendToOutgoingContext.spec (GF := GF) (hG := hG)) :
    reqCtx.spec (GF := GF) (hG := hG) := by
  intro _ _ _ CRE CEC who hAs
  wp_start
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %cd %cancel ⟨#Hcancel, #Hok, #Hce, #Hctx, %Hv⟩
  ihave %Hnone := metadata.outgoingOf_noValues cctx cd $$ Hctx
  (try wp_auto)
  wp_if_destruct
  · -- the bad principal: its token appended
    ihave #Pmd : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata $$ []
    · iPkgInit
    wp_apply wp_slice_literal (V := GoString) [go!"token", badToken]
    isplitr
    · ipureintro; rfl
    iintro %ksl ⟨Hksl, -⟩
    simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
      show max (max (2 : Int) 0) 0 = 2 from rfl]
    (try wp_auto)
    wp_apply wp_Append cctx cd _ (DFrac.own 1) go!"token" badToken (by unfold metadata.lowerKey; decide) $$ [Hksl]
      as %c' ⟨%ci, %vs, %Hc', #Hctx', %Hmd, -⟩
    · iframe; iexact Hctx
    (try wp_auto)
    ihave #Hall := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
    iunfold client.ctxErrClientAllW at Hall
    iapply HΦ
    isplitr; · iexact Hcancel
    iexists ci, { cd with Values := vs }, GoInterface.ok cctx
    isplitr; · ipureintro; exact Hc'
    isplitr; · iapply ctxOk_of_isContext; iexact Hctx'
    isplitr; · iapply Hall; iexact Hctx'
    ipureintro
    exact ⟨Hnone Hv, Hmd⟩
  · (try wp_auto)
    iapply HΦ
    iframe #
    iexists GoInterface.ok cctx
    isplitr; · ipureintro; rfl
    ipureintro
    refine ⟨Hnone Hv, ?_⟩
    simp only [Hif, ↓reduceIte]

end proof

end authkv
end EtcdGrove
end Perennial
