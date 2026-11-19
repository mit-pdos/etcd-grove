module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialModel
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toPorcupineModel
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.orderByLinearization
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewReplay
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__Validate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewWatchValidator
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__ValidateWatch
public import Spec.github_com.anishathalye.porcupine.CheckOperationsVerbose
public import Spec.github_com.anishathalye.porcupine.LinearizationInfo__PartialLinearizations
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealGlue
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchEvents

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_correctness
open github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output mstore)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem realCheck.wp_proof
    (wp_realRequest : realRequest.spec (GF := GF) (hG := hG))
    (wp_realEvents : realEvents.spec (GF := GF) (hG := hG))
    (wp_watchOptions : watchOptions.spec (GF := GF) (hG := hG))
    (wp_initialModel : initialModel.spec (GF := GF) (hG := hG))
    (wp_toPorcupineModel : toPorcupineModel.spec (GF := GF) (hG := hG))
    (wp_orderByLinearization : orderByLinearization.spec (GF := GF) (hG := hG))
    (wp_CheckOperationsVerbose : porcupine.CheckOperationsVerbose.spec (GF := GF) (hG := hG))
    (wp_PartialLinearizations :
      porcupine.LinearizationInfo.PartialLinearizations.spec (GF := GF) (hG := hG))
    (wp_NewReplay : k8s_correctness.NewReplay.spec (GF := GF) (hG := hG))
    (wp_Validate : k8s_correctness.Replay.Validate.spec (GF := GF) (hG := hG))
    (wp_NewWatchValidator : k8s_correctness.NewWatchValidator.spec (GF := GF) (hG := hG))
    (wp_ValidateWatch : k8s_correctness.WatchValidator.ValidateWatch.spec (GF := GF) (hG := hG)) :
    realCheck.spec (GF := GF) (hG := hG) := by
  intro s0 g0 sl lops dur hlin hhist hok hrun0 hn
  wp_start as ⟨#Hcc, #Hs0, Hsl, #Hio⟩
  ihave ⟨%vs, %Hvs, #Hvr⟩ := gOks_collect (sem := sem) (package_sem := package_sem) g0 lops hok $$ Hio
  ihave %Hl := ownSlice_len $$ Hsl
  wp_auto
  ihave HI : (∃ (j : w64) (opv : github_com.anishathalye.porcupine.Operation) (osl psl wsl : GoSlice)
      (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
      (ps : List github_com.anishathalye.porcupine.Operation)
      (ws : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchOperation),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ opv ∗ "operations" ∷ operations_ptr ↦ osl ∗
      "pOps" ∷ pOps_ptr ↦ psl ∗ "watches" ∷ watches_ptr ↦ wsl ∗ "Hsl" ∷ sl ↦* lops ∗
      "Hos" ∷ osl ↦* os ∗
      "Hosc" ∷ ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation osl (DFrac.own 1) ∗
      "Hps" ∷ psl ↦* ps ∗
      "Hpsc" ∷ ownSliceCap github_com.anishathalye.porcupine.Operation psl (DFrac.own 1) ∗
      "Hws" ∷ wsl ↦* ws ∗
      "Hwsc" ∷ ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchOperation wsl
        (DFrac.own 1) ∗
      "#Hor" ∷ ([∗list] c;u ∈ os;Uj lops vs (sint.nat j), opRep c u.val ∗ reqPin c.Request' u.val.1) ∗
      "#Hwr" ∷ ([∗list] w ∈ ws, wRep vs w) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        github_com.anishathalye.porcupine.histOf ps =
          boxH (Lof os (Uj lops vs (sint.nat j))) (Uj lops vs (sint.nat j))⌝ : IProp GF)
    $$ [i op operations pOps watches Hsl]
  · iexists W64 0, _, slice.nil, slice.nil, slice.nil, [], [], []
    simp only [show sint.nat (W64 0) = 0 from rfl, Uj, List.take_zero, fmapH, List.filterMap_nil]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
    list_elem lops (sint.nat j) as o
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) lops _ o Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Ho_lookup
    obtain ⟨v, hv⟩ : ∃ v, vs[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hvs.1]; exact (List.getElem?_eq_some_iff.1 Ho_lookup).1)⟩
    have hg := Hvs.2 _ o v Ho_lookup hv
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := Hb'.1; have := Hb'.2; have := Hl.2; word
    have hUs := Uj_succ lops vs (sint.nat j) o v Ho_lookup hv
    ihave #Hv := BigSepL.bigSepL_lookup (Φ := fun _ v => gRep (GF := GF) v) hv $$ Hvr
    iunfold gRep at Hv
    simp only [hg.1]
    wp_auto
    (try simp only [hg.2.1])
    (try wp_auto)
    wp_if_destruct
    · -- a watch
      have h5 : v.1.Kind' = W64 5 := Hif
      cases hs : v.1.Skip'
      · simp only [Bool.not_false]
        wp_auto
        wp_apply wp_watchOptions as %p Hp
        imod sendInitOwn_persist p (sieOfL v.1) $$ Hp with #Hsie
        icases Hv with ⟨-, (%hc | #Hev)⟩
        · exfalso; rcases hc with hc | hc
          · exact hc h5
          · simp_all
        (try wp_auto)
        wp_apply wp_realEvents v.1 v.2.1.Raw'.Events' v.2.2.2 $$ [$Hev] as %rsl #Hrs
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %wsl1 ⟨Hwsl1, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hws $Hwsc $Hwsl1] as %wsl' ⟨Hws, Hwsc, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, o, osl, psl, wsl', os, ps, _
        rw [hj1, hUs, if_pos h5, List.append_nil]
        iframe
        isplitl
        · iexact Hor
        isplitl
        · iapply BigSepL.bigSepL_snoc.2
          isplitl
          · iexact Hwr
          · iunfold wRep
            iexists sint.nat j, v
            isplitr
            · ipureintro; exact ⟨hv, h5, hs, rfl⟩
            isplitl
            · iunfold wreqRep
              iexists p
              isplitr
              · ipureintro; rfl
              · iexact Hsie
            · iexact Hrs
        ipureintro
        exact ⟨by word, by word, Hj.2.2⟩
      · simp only [Bool.not_true]
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, o, osl, psl, wsl, os, ps, ws
        rw [hj1, hUs, if_pos h5, List.append_nil]
        iframe
        isplitl
        · iexact Hor
        isplitl
        · iexact Hwr
        ipureintro
        exact ⟨by word, by word, Hj.2.2⟩
    · -- a unary operation
      have h5 : v.1.Kind' ≠ W64 5 := by simpa using Hif
      obtain ⟨-, hstep⟩ := (gOk_facts _ o v hg).2 h5
      icases Hv with ⟨(%h5' | #Hresp), -⟩
      · exact absurd h5' h5
      wp_apply wp_realRequest v.1 hstep.1.1 as %rq ⟨#Hrq, #Hpin⟩
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl1 ⟨Hosl1, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hos $Hosc $Hosl1] as %osl' ⟨Hos, Hosc, -⟩
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %psl1 ⟨Hpsl1, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hps $Hpsc $Hpsl1] as %psl' ⟨Hps, Hpsc, -⟩
      (try wp_auto)
      ihave %Holen := BigSepL2.bigSepL2_length $$ Hor
      wp_for_post
      iframe
      iexists j + W64 1, o, osl', psl', wsl, _, _, ws
      rw [hj1, hUs, if_neg h5]
      iframe
      isplitl
      · iapply BigSepL2.bigSepL2_snoc.2
        isplitl
        · iexact Hor
        · iunfold opRep
          isplitl
          · isplitl
            · iexact Hrq
            · dsimp only; iunfold rawResp at Hresp; iexact Hresp
          · iexact Hpin
      isplitl
      · iexact Hwr
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [boxH_Lof_snoc _ _ _ _ Holen, github_com.anishathalye.porcupine.histOf, List.map_append, ← Hj.2.2]
      rfl
  · -- the loop's end
    have hjl : sint.nat j = lops.length := by
      have := Hj.2.1; have := Hl.1; have := Hl.2
      have : ¬ sint.Z j < sint.Z sl.len := by first | exact Hif | exact dec_false Hif
      word
    rw [hjl, Uj_full lops vs Hvs.1] at Hj
    rw [hjl, Uj_full lops vs Hvs.1]
    ihave %Holen := BigSepL2.bigSepL2_length $$ Hor
    obtain ⟨⟨π2, hπ2⟩, hfit, hstepU, hrep⟩ :=
      realCheck_pure (sem := sem) (package_sem := package_sem) g0 lops vs Hvs hlin hrun0 hn
    obtain ⟨hhps, hpsl⟩ := histOk_ps lops vs Hvs.1 hhist os ps Holen Hj.2.2
    ihave %hag := stepAgree_of (sem := sem) (package_sem := package_sem) os _ hstepU $$ Hor
    wp_apply wp_initialModel s0 g0.st (storeKeys_nodup g0.st hrun0.1.1) $$ [$Hs0] as %mp Hm
    · solve_pkg_init
    ihave Hmf := modelOwn_freeze (GF := GF) mp (absR g0.st) $$ Hm
    imod Hmf with #Hm
    (try wp_auto)
    have hLlen := Lof_length os _ Holen
    have hLval : ∀ (k : Nat) (e : github_com.anishathalye.porcupine.OpV × (Input × RResp))
        (u : Op (Input × RResp)), (Lof os (fmapH unaryOf (histR lops vs)))[k]? = some e →
        (fmapH unaryOf (histR lops vs))[k]? = some u → e.2 = u.val := by
      intro k e u he hu
      obtain ⟨c, u', -, hu', rfl⟩ := Lof_getElem? os _ k e he
      rw [hu] at hu'; cases hu'; rfl
    ihave %Hpsl := ownSlice_len $$ Hps
    wp_if_destruct
    · -- some unary operations: porcupine
      wp_apply wp_toPorcupineModel mp (absR g0.st) (Lof os (fmapH unaryOf (histR lops vs))) hfit $$ [$Hm] as %m #Hmodel
      ihave #Hio2 := realMS_opsIoOk (sem := sem) (package_sem := package_sem) (absR g0.st) os _ ps Hj.2.2
        hstepU $$ Hor
      wp_apply wp_CheckOperationsVerbose _ (realMS (Lof os (fmapH unaryOf (histR lops vs))) (absR g0.st)) m
        psl ps (DFrac.own 1) dur $$ [$Hps] as %r %info ⟨%Hr, Hinfo⟩
      · iframe #; ipureintro; exact hhps
      have hlinM : Linearizable (realM (Lof os (fmapH unaryOf (histR lops vs))) (absR g0.st))
          (github_com.anishathalye.porcupine.histOf ps) := by
        rw [Hj.2.2]; exact ⟨π2, (realM_lin_iff _ _ _ hag hLlen hLval π2).1 hπ2⟩
      rcases Hr with ⟨rfl, -⟩ | ⟨rfl, hnL⟩ | ⟨rfl, hd⟩
      · -- Ok
        ihave #Hli := Hinfo $$ %rfl
        wp_if_destruct
        rotate_left
        · exact absurd rfl Hif
        sorry
      · exact absurd hlinM hnL
      · -- Unknown: porcupine's verdict
        wp_if_destruct
        · exact absurd Hif (by decide)
        · (try wp_auto)
          iapply HΦ; ipureintro
          exact ⟨by decide, fun h => by omega⟩
    · sorry

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
