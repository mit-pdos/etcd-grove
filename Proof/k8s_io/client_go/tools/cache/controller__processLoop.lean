/-
Proof of `Spec/k8s_io/client_go/tools/cache/controller__processLoop.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.controller__processLoop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

set_option hygiene false in
/-- The loop, from any of the three ways the prefix sets `useBatchProcess` to `false`: the
single-delta path. -/
local macro "loop_tac" : tactic => `(tactic| (
    ihave HL : iprop(∃ bq : GoInterface, batchQueue_ptr ↦ bq ∗ I ∗ useBatchProcess_ptr ↦ false)
      $$ [HI useBatchProcess batchQueue]
    · iexists _; iframe
    wp_for HL
    icases HL with ⟨Hbq, HI, Hub⟩
    ihave #Hctx2 := Hctx
    iunfold context.isContext at Hctx2
    iunfold context.isContextDef at Hctx2
    iNamed Hctx2
    wp_apply HDone as %dch %γd #Hdone
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
      iprop((True -∗ Φ #()) ∗ c_ptr ↦ c ∗ ctx_ptr ↦ GoInterface.ok ctx ∗ batchQueue_ptr ↦ bq ∗
        I ∗ useBatchProcess_ptr ↦ false)
      $$ [] [HΦ c ctx Hbq HI Hub] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro ⟨HΦ, c, ctx, Hbq, HI, Hub⟩
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
      isplit
      · iintro ⟨-, #Hcl⟩
        (try wp_auto)
        wp_for_post
        iapply HΦ
        all_goals (try itrivial)
      · iframe
    · iframe
    · iintro ⟨HΦ, c, ctx, Hbq, HI, Hub⟩ -
      (try wp_auto)
      rw [method_unfold (t := go.GoType.PointerType Config.ty) (m := go!"Pop")]
      (try wp_auto)
      ihave Hpd := Hstep $$ HI
      icases Hpd with ⟨Hpop, Hdn⟩
      wp_apply (wp_Pop f γ OK pf (fun d b => Ψ [d] b) (fun d e => Ψ' [d] e) (popDone I))
        $$ [Hpop Hdn] as %v Hv
      · iframe
        isplitl []
        · iexact Hf
        · iexact Hpok
      iunfold popDone at Hv
      icases Hv with ⟨%x, %e, %Hv, HI⟩
      subst Hv
      (try wp_auto)
      cases e with
      | nil =>
        (try wp_auto)
        wp_for_post
        iframe
        iexists _
        iframe
      | ok ei =>
        (try wp_auto)
        wp_bind (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #(GoInterface.ok ei))) (Val #e1))
        iunfold errIsOk at Herr
        iapply Herr
        · itrivial
        inext
        iintro %b -
        cases b
        · (try wp_auto)
          wp_for_post
          iframe
          iexists _
          iframe
        · (try wp_auto)
          wp_for_post
          iapply HΦ
          all_goals (try itrivial)))

theorem controller.processLoop.wp_proof (wp_Pop : RealFIFO.Pop.spec (GF := GF) (hG := hG))
    (wp_PopBatch : RealFIFO.PopBatch.spec (GF := GF) (hG := hG)) :
    controller.processLoop.spec (GF := GF) (hG := hG) := by
  intro c ctx cs f γ OK pf pbf Ψ Ψ' I
  wp_start as ⟨#Hctx, #Hq, #Hp, #Hpb, #Hf, #Hpok, #Hpbok, #Hgate, #Herr, HI, #Hstep, #Hbstep⟩
  (try wp_auto)
  ihave #Hm : (k8s_io.apiserver.pkg.storage.cacher.k8sCacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hm with ⟨%e1, %e2, #He1, #He2⟩
  cases hts : go.typeSetContains RealFIFO.ty.PointerType QueueWithBatch.ty
  all_goals (try wp_auto)
  rotate_left
  by_cases hpb : pbf = func.nil
  · simp only [hpb, decide_true, Bool.not_true]
    (try wp_auto)
    loop_tac
  simp only [hpb, decide_false, Bool.not_false]
  (try wp_auto)
  iunfold gateOk at Hgate
  wp_bind (App (Val (@! k8s_io.client_go.features.FeatureGates)) (Val #()))
  iapply Hgate
  · itrivial
  inext
  iintro %g ⟨%gi, %Hg, #Hen⟩
  subst Hg
  (try wp_auto)
  wp_bind (App (Val #(methods gi.ty go!"Enabled" gi.v))
    (Val k8s_io.client_go.features.InOrderInformersBatchProcess))
  iapply Hen
  · itrivial
  inext
  iintro %gb -
  (try wp_auto)
  cases gb
  · (try wp_auto)
    loop_tac
  · (try wp_auto)
    -- the batch path (`Main`'s): `PopBatch(ProcessBatch, Process)`
    ihave HL : iprop(I ∗ useBatchProcess_ptr ↦ true ∗
        batchQueue_ptr ↦ interface.mkOk RealFIFO.ty.PointerType #f) $$ [HI useBatchProcess batchQueue]
    · iframe
    wp_for HL
    icases HL with ⟨HI, Hub, Hbq⟩
    ihave #Hctx2 := Hctx
    iunfold context.isContext at Hctx2
    iunfold context.isContextDef at Hctx2
    iNamed Hctx2
    wp_apply HDone as %dch %γd #Hdone
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
      iprop((True -∗ Φ #()) ∗ c_ptr ↦ c ∗ ctx_ptr ↦ GoInterface.ok ctx ∗
        batchQueue_ptr ↦ interface.mkOk RealFIFO.ty.PointerType #f ∗ I ∗ useBatchProcess_ptr ↦ true)
      $$ [] [HΦ c ctx Hbq HI Hub] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro ⟨HΦ, c, ctx, Hbq, HI, Hub⟩
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
      isplit
      · iintro ⟨-, #Hcl⟩
        (try wp_auto)
        wp_for_post
        iapply HΦ
        all_goals (try itrivial)
      · iframe
    · iframe
    · iintro ⟨HΦ, c, ctx, Hbq, HI, Hub⟩ -
      (try wp_auto)
      ihave Hpd := Hbstep $$ HI
      icases Hpd with ⟨Hpop, Hdn⟩
      wp_apply (wp_PopBatch f γ OK pbf pf Ψ Ψ' (popBatchDone I)) $$ [Hpop Hdn] as %v Hv
      · iframe
        isplitl []
        · iexact Hf
        isplitl []
        · iexact Hpok
        · iexact Hpbok
      iunfold popBatchDone at Hv
      icases Hv with ⟨%e, %Hv, HI⟩
      subst Hv
      (try wp_auto)
      cases e with
      | nil =>
        (try wp_auto)
        wp_for_post
        iframe
        simp only [named]
        iframe
      | ok ei =>
        (try wp_auto)
        wp_bind (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #(GoInterface.ok ei))) (Val #e1))
        iunfold errIsOk at Herr
        iapply Herr
        · itrivial
        inext
        iintro %b -
        cases b
        · (try wp_auto)
          wp_for_post
          iframe
          simp only [named]
          iframe
        · (try wp_auto)
          wp_for_post
          iapply HΦ
          all_goals (try itrivial)
  all_goals loop_tac

end proof

end cache
end EtcdGrove
end Perennial
