/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Overwrite.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the participant's store (`GetStoreMetadata`, `HandleOverwrite`), internal specs over the
opened `partiOwn` (`partiOwn_open`).
-/
module

public import Dsverify.Proof.gryff.H1.Defs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5

theorem GryffParticipant.wp_GetStoreMetadata_int (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (smR owR : Loc) (sm : GMap w64 Loc) (tag : model.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiFix pa ip k smR owR ∗ smR ↦$ sm ∗ storeRep sm tag }}
      (App (Val (pa @!! go.GoType.PointerType src.gryffcommon.GryffParticipant.ty @!!
        go!"GetStoreMetadata")) (Val #(W64 0)))
    {{ (md : Loc), RET #md; ∃ (tp : Loc) (gt : src.gryffproto.Tag), ⌜tagOf gt = tag⌝ ∗
        tp ↦□ gt ∗ md ↦ (src.gryffcommon.StoreMetadata.mk tp) ∗ smR ↦$ sm ∗
        (md ↦ (src.gryffcommon.StoreMetadata.mk tp) -∗ storeRep sm tag ∗ mdAlive sm md) ∗
        (∀ (tp' : Loc) (gt' : src.gryffproto.Tag), md ↦ (src.gryffcommon.StoreMetadata.mk tp') -∗
          tp' ↦□ gt' -∗ storeRep (sm.insert (W64 0) md) (tagOf gt')) ∗
        ⌜sm.lookup (W64 0) = none ∨ sm.lookup (W64 0) = some md⌝ }} := by
  wp_start as ⟨#Hfix, Hsm, Hst⟩
  unfold partiFix storeRep mdAlive
  icases Hfix with ⟨#Hid, #Hip, #Hnc, #Hstp, #Howp⟩
  icases Hst with ⟨%Hsm0, Hm⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hsm as Hsm
  cases hm : sm !! W64 0 with
  | none =>
    dsimp only
    ipure Hm
    wp_pures
    wp_alloc tp as Htp
    ipersist Htp
    wp_auto
    iapply HΦ
    iexists tp, ⟨W32 0, W32 0, W32 0⟩
    isplitl []
    · ipureintro; simp [tagOf, Hm, model.tag0]
    iframe Htp «$r0» Hsm
    isplitl []
    · iintro Hmd
      isplitl []
      · ipureintro; exact ⟨Hsm0, Hm⟩
      iright; iexists tp, ⟨W32 0, W32 0, W32 0⟩
      iframe Hmd Htp
    isplitl []
    · iintro %tp' %gt' Hmd #Htp'
      rw [GMap.lookup_insert_eq]
      isplitl []
      · ipureintro; intro kk hkk
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)]; exact Hsm0 kk hkk
      iexists tp', gt'
      iframe Hmd Htp'
      ipureintro; rfl
    ipureintro; left; rfl
  | some md =>
    dsimp only
    icases Hm with ⟨%tp, %gt, Hmd, #Htp, %Htag⟩
    rw [show decide ((some md).isSome = true) = true from rfl]
    wp_auto
    iapply HΦ
    iexists tp, gt
    iframe Htp Hmd Hsm
    isplitl []
    · ipureintro; exact Htag
    isplitl []
    · iintro Hmd
      isplitl [Hmd]
      · isplitl []
        · ipureintro; exact Hsm0
        iexists tp, gt
        iframe Hmd Htp
        ipureintro; exact Htag
      ileft; ipureintro; rfl
    isplitl []
    · iintro %tp' %gt' Hmd #Htp'
      rw [GMap.lookup_insert_eq]
      isplitl []
      · ipureintro; intro kk hkk
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)]; exact Hsm0 kk hkk
      iexists tp', gt'
      iframe Hmd Htp'
      ipureintro; rfl
    ipureintro; right; rfl


attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffParticipant.wp_HandleOverwrite_int (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (smR owR : Loc) (sm : GMap w64 Loc) (V : w64 → IProp GF) (vt : model.ValTag)
    (v : w64) (tp : Loc) (gt : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiFix pa ip k smR owR ∗ smR ↦$ sm ∗ storeRep sm vt.t ∗ ipartiOk ip V ∗ V vt.v ∗
        tp ↦□ gt }}
      (App (App (App (Val (pa @!! go.GoType.PointerType src.gryffcommon.GryffParticipant.ty @!!
        go!"HandleOverwrite")) (Val #(W64 0))) (Val #v)) (Val #tp))
    {{ RET #(); ∃ sm' : GMap w64 Loc, smR ↦$ sm' ∗ storeRep sm' (ovw vt v (tagOf gt)).t ∗
        V (ovw vt v (tagOf gt)).v ∗
        ⌜∀ x, sm.lookup (W64 0) = some x → sm'.lookup (W64 0) = some x⌝ }} := by
  wp_start as ⟨#Hfix, Hsm, Hst, #Hip, HV, #Htp⟩
  icases (ipartiOk_open ip V).1 $$ Hip with ⟨#HGet, #HSet, #HPr, #HStats, -, -⟩
  iclear Hip
  icases (partiFix_open pa ip k smR owR).1 $$ Hfix with ⟨#Hid, #Hipf, #Hnc, #Hstp, #Howp⟩
  wp_auto
  wp_apply GryffParticipant.wp_GetStoreMetadata_int $$ [$Hfix $Hsm $Hst]
    as %md ⟨%tp0, %gt0, %Htag0, #Htp0, Hmd, Hsm, Hback, Hins, %Hmd0⟩
  icases storeMeta_acc _ _ $$ Hmd with ⟨HmdT, HmdB⟩
  wp_apply Tag.wp_LessThan $$ [$Htp0] as -
  simp only [specT]
  cases hlt : (tagOf gt0).lt (tagOf gt)
  · wp_auto
    wp_apply HGet $$ %(vt.v) [$HV] as %ret ⟨%Hret, HV⟩
    wp_printf HPr
    wp_apply wp_map_len $$ Hsm as Hsm
    wp_apply HStats as %_ ⟨%st, %Hst, Hstats⟩
    subst Hst
    wp_apply StatsMap.Max.wp' $$ [$Hstats] as %_ -
    · stats_key
    iapply HΦ
    have hov : ovw vt v (tagOf gt) = vt := by
      simp only [ovw, ← Htag0, hlt, Bool.false_eq_true, if_false]
    rw [hov]
    iexists _
    iframe Hsm HV
    isplitl [Hback HmdB HmdT]
    · icases Hback $$ [HmdB HmdT] with ⟨H, -⟩
      · iapply HmdB $$ HmdT
      iexact H
    ipureintro; intro x hx; exact hx
  · wp_auto
    wp_apply HGet $$ %(vt.v) [$HV] as %ret ⟨%Hret, HV⟩
    wp_printf HPr
    wp_apply HSet $$ %(vt.v) %v [$HV] as %_ ⟨%_, HV⟩
    wp_apply wp_mapInsert $$ Hsm as Hsm
    wp_apply wp_map_len $$ Hsm as Hsm
    wp_apply HStats as %_ ⟨%st, %Hst, Hstats⟩
    subst Hst
    wp_apply StatsMap.Max.wp' $$ [$Hstats] as %_ -
    · stats_key
    iapply HΦ
    have hov : ovw vt v (tagOf gt) = ⟨v, tagOf gt⟩ := by
      simp only [ovw, ← Htag0, hlt, if_true]
    rw [hov]
    iexists _
    iframe Hsm HV
    isplitl [Hins HmdB HmdT]
    · iapply Hins $$ [HmdB HmdT] Htp
      iapply HmdB $$ HmdT
    ipureintro; intro x hx
    rw [GMap.lookup_insert_eq]
    rcases Hmd0 with h | h <;> rw [h] at hx
    · cases hx
    · exact hx
    done


end

end Perennial.gryff.replica2
