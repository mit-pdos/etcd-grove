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
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchEventsLemmas

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

/-- **The checker operations at a linearization's indices** are the driver's operations along it
(`orderByLinearization`'s result against `vals`). -/
theorem opReps_pick (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) : ∀ xs : List w64,
    ([∗list] c;u ∈ os;U, opRep (GF := GF) c u.val ∗ reqPin c.Request' u.val.1) ⊢
      [∗list] c;op ∈ xs.filterMap (fun x => os[(sint.Z x).toNat]?);
        vals U (xs.map fun x => (sint.Z x).toNat), opRep (GF := GF) c op
  | [] => by
    iintro -
    simp only [List.filterMap_nil, List.map_nil, vals]
    iapply BigSepL2.bigSepL2_nil.2
    itrivial
  | x :: xs => by
    iintro #H
    ihave %hlen := BigSepL2.bigSepL2_length $$ H
    ihave #Hr := opReps_pick os U xs $$ H
    simp only [List.filterMap_cons, List.map_cons, vals]
    cases h1 : os[(sint.Z x).toNat]? with
    | none =>
      have h2 : U[(sint.Z x).toNat]? = none := by
        rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
      simp only [h2, Option.map_none]
      iexact Hr
    | some c =>
      obtain ⟨u, h2⟩ : ∃ u, U[(sint.Z x).toNat]? = some u := by
        have : (sint.Z x).toNat < U.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 h1).1
        exact ⟨_, List.getElem?_eq_getElem this⟩
      simp only [h2, Option.map_some]
      ihave #Hab := BigSepL2.bigSepL2_lookup (Φ := fun _ c u => iprop(opRep (GF := GF) c u.val ∗
        reqPin c.Request' u.val.1)) h1 h2 $$ H
      icases Hab with ⟨#Hab, -⟩
      iapply BigSepL2.bigSepL2_cons.2
      isplitl
      · iexact Hab
      · iexact Hr

/-- A linearization's values are at most the history's operations. -/
theorem vals_length_lin {σ α : Type} {M : SeqModel σ α} {h : List (Op α)} {π : List Nat}
    (hl : IsLinearization M h π) : (vals h π).length ≤ h.length := by
  obtain ⟨hnd, hmem, -, -⟩ := hl
  have h1 : (vals h π).length ≤ π.length := List.length_filterMap_le _ _
  have hsub : π ⊆ List.range h.length := fun k hk => List.mem_range.2 ((hmem k).1 hk).1
  have h2 := (List.subperm_of_subset hnd hsub).length_le
  rw [List.length_range] at h2
  omega

/-- The unary operations are at most the history's. -/
theorem fmapH_histR_length (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp) :
    (fmapH unaryOf (histR lops vs)).length ≤ lops.length := by
  unfold fmapH histR
  exact Nat.le_trans (List.length_filterMap_le _ _) (by rw [List.length_zipWith]; exact Nat.min_le_left _ _)

set_option hygiene false in
/-- `realCheck` after its porcupine block (`linearizedOps ↦ lo`, `Hlo : lo ↦*□ os2`, `Hrep2`: `os2` against
`vals U lin2`, `hlin2 : IsLinearization (realS init) U lin2`): `NewReplay`, the `Validate` loop,
`NewWatchValidator`, the `ValidateWatch` loop, `Ok`. -/
local macro "rc_tail" os2:term:max lin2:term:max : tactic => `(tactic| (
  obtain ⟨R, hR, hval, hw⟩ := hrep $lin2 hlin2
  have hpre := replayPre_of (absR g0.st)
    (vals (fmapH unaryOf (histR lops vs)) $lin2) hfit (by
      have h1 := vals_length_lin hlin2
      have h2 := fmapH_histR_length lops vs
      have h3 := hhist.1
      omega) (fun op hop => by
    obtain ⟨u, hu, rfl⟩ := mem_vals _ _ op hop
    exact hstepU _ (List.mem_map_of_mem hu))
  wp_apply wp_NewReplay mp (absR g0.st) lo _ _ R hpre hR $$ [Hm Hlo Hrep2] as %rp %err ⟨%herr, #Hrp⟩
  · iframe Hm Hlo Hrep2
  subst herr
  wp_auto
  ihave %Hlol := ownSlice_len $$ Hlo
  ihave %Hr2l := BigSepL2.bigSepL2_length $$ Hrep2
  ihave HV : (∃ (j : w64) (opv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ opv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z lo.len⌝ : IProp GF) $$ [i op]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word⟩
  wp_for HV
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z lo.len := ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
    list_elem $os2 (sint.nat j) as c
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index lo (sint.Z j) _ DFrac.discard c Hj.1 $$ [Hlo]
    · iframe Hlo; ipureintro; exact Hc_lookup
    iintro -
    obtain ⟨op, hop⟩ : ∃ op, (vals (fmapH unaryOf (histR lops vs)) $lin2)[sint.nat j]? = some op := by
      have := (List.getElem?_eq_some_iff.1 Hc_lookup).1
      exact ⟨_, List.getElem?_eq_getElem (by rw [← Hr2l]; exact this)⟩
    ihave #Hcop := BigSepL2.bigSepL2_lookup (Φ := fun _ c op => opRep (GF := GF) c op) Hc_lookup hop $$ Hrep2
    iunfold opRep at Hcop
    icases Hcop with ⟨#Hrq, #Hrs⟩
    have hmem := List.mem_of_getElem? hop
    have hst : k8s_correctness.stepIn op.1 op.2 := by
      obtain ⟨u, hu, rfl⟩ := mem_vals _ _ op hmem
      exact hstepU _ (List.mem_map_of_mem hu)
    wp_auto
    wp_apply wp_Validate rp R c.Request' c.Response' op.1 op.2 hst.1 (hval op hmem).2 hst.2.2.1
      (hval op hmem).1 $$ [Hrp Hrq Hrs] as %err %herr
    · iframe Hrp Hrq Hrs
    subst herr
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, c
    iframe
    ipureintro
    have := Hb'.2; have := Hlol.2
    refine ⟨by word, by word⟩
  · -- the loop's end
    wp_apply wp_NewWatchValidator rp
    ihave %Hwsl := ownSlice_len $$ Hws
    ihave HW : (∃ (j : w64) (wv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchOperation),
        "i" ∷ i_ptr ↦ j ∗ "w" ∷ w_ptr ↦ wv ∗ "validator" ∷ validator_ptr ↦ validatorV rp ∗
        "Hws" ∷ wsl ↦* ws ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z wsl.len⌝ : IProp GF) $$ [i w validator Hws]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word⟩
    wp_for HW
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z wsl.len := ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
      list_elem ws (sint.nat j) as w
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index wsl (sint.Z j) ws _ w Hj.1 $$ [Hws] as Hws
      · iframe; ipureintro; exact Hw_lookup
      ihave #Hw := BigSepL.bigSepL_lookup (Φ := fun _ w => wRep (GF := GF) vs w) Hw_lookup $$ Hwr
      iunfold wRep at Hw
      icases Hw with ⟨%k, %v, %hkv, #Hwq, #Hev⟩
      obtain ⟨hwin, hwv⟩ := hw k v hkv.1 hkv.2.1 hkv.2.2.1
      have hresp : w.Response' = ⟨w.Response'.Events', GoInterface.nil⟩ := by
        rw [← hkv.2.2.2]
      rw [hresp]
      wp_method_call
      wp_auto
      wp_apply wp_ValidateWatch rp R v.1 w.Request' w.Response'.Events' _ hwin hwv $$ [Hrp Hwq Hev]
        as %err %herr
      · iframe Hrp Hwq Hev
      subst herr
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, w
      iframe
      ipureintro
      have := Hb'.2; have := Hwsl.2
      refine ⟨by word, by word⟩
    · iapply HΦ
      ipureintro
      exact ⟨by decide, fun _ => rfl⟩))

set_option maxHeartbeats 1000000 in
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
  intro s0 g0 sl lops dur hlin hhist hok hrun0 hn hitems
  have hszI : GMap.size (absR g0.st).items ≤ g0.st.items.length := by
    have := size_ofList_le (g0.st.items.map fun it => (storeKeyL it.key', it.obj'))
    rw [List.length_map] at this
    exact this
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
    wp_apply wp_initialModel s0 g0.st (storeKeys_nodup g0.st hrun0.1.1) (by omega) $$ [$Hs0] as %mp Hm
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
      have hpos : sint.Z (W64 0) < sint.Z psl.len := by first | exact Hif | exact dec_true Hif
      wp_apply wp_toPorcupineModel mp (absR g0.st) (Lof os (fmapH unaryOf (histR lops vs))) hfit
        (by omega) $$ [$Hm] as %m #Hmodel
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
        iunfold github_com.anishathalye.porcupine.linInfoOk at Hli
        icases Hli with ⟨%psls, #Hpsls, %hpsls, #Hpl⟩
        obtain ⟨psl0, rfl⟩ : ∃ psl0, psls = [psl0] := by
          match psls, hpsls with
          | [a], _ => exact ⟨a, rfl⟩
        ihave #Hp0 := BigSepL.bigSepL_lookup (Φ := fun i psl => github_com.anishathalye.porcupine.partLins
          (realM (Lof os (fmapH unaryOf (histR lops vs))) (absR g0.st))
          ([github_com.anishathalye.porcupine.histOf ps].getD i []) psl) (i := 0) rfl $$ Hpl
        iunfold github_com.anishathalye.porcupine.partLins at Hp0
        icases Hp0 with ⟨%lsls, #Hlsls, %hlsls, #Hll⟩
        have hpne : github_com.anishathalye.porcupine.histOf ps ≠ [] := by
          intro h
          have := congrArg List.length h
          simp only [github_com.anishathalye.porcupine.histOf, List.length_map, List.length_nil] at this
          have := Hpsl.1; have := hpos
          word
        obtain ⟨lsl0, rfl⟩ : ∃ lsl0, lsls = [lsl0] := by
          match lsls, hlsls hpne with
          | [a], _ => exact ⟨a, rfl⟩
        ihave #Hl0 := BigSepL.bigSepL_lookup (Φ := fun _ lsl => github_com.anishathalye.porcupine.linSlice
          (realM (Lof os (fmapH unaryOf (histR lops vs))) (absR g0.st))
          ([github_com.anishathalye.porcupine.histOf ps].getD 0 []) lsl) (l := [lsl0]) (i := 0) (x := lsl0) rfl $$ Hll
        iunfold github_com.anishathalye.porcupine.linSlice at Hl0
        icases Hl0 with ⟨%xs, #Hxs, %hxs⟩
        wp_apply wp_PartialLinearizations info_ptr $$ [$info]
        iintro info
        ihave %Hpl0 := ownSlice_len $$ Hpsls
        ihave %Hll0 := ownSlice_len $$ Hlsls
        ihave %Hxl := ownSlice_len $$ Hxs
        simp only [List.length_singleton] at Hpl0 Hll0
        have hl1 : info.partialLinearizations'.len = W64 1 := by have := Hpl0.1; have := Hpl0.2; word
        have hl2 : psl0.len = W64 1 := by have := Hll0.1; have := Hll0.2; word
        wp_auto
        rw [hl1]
        simp only [decide_true]
        wp_auto
        have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z info.partialLinearizations'.len := by
          rw [hl1]; decide
        simp only [hb0, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index info.partialLinearizations' (sint.Z (W64 0)) [psl0] DFrac.discard psl0
          (by decide) $$ [$Hpsls]
        · ipureintro; rfl
        iintro -
        wp_auto
        rw [hl2]
        simp only [decide_true, Bool.not_true]
        wp_auto
        (try simp only [hb0, _root_.and_self, ↓reduceIte, true_and, show sint.Z (W64 0) < sint.Z info.partialLinearizations'.len from hb0.2])
        wp_apply wp_load_slice_index info.partialLinearizations' (sint.Z (W64 0)) [psl0] DFrac.discard psl0
          (by decide) $$ [$Hpsls]
        · ipureintro; rfl
        iintro -
        (try wp_auto)
        have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z psl0.len := by rw [hl2]; decide
        (try simp only [hb1, _root_.and_self, ↓reduceIte, true_and, show sint.Z (W64 0) < sint.Z psl0.len from hb1.2])
        wp_apply wp_load_slice_index psl0 (sint.Z (W64 0)) [lsl0] DFrac.discard lsl0
          (by decide) $$ [$Hlsls]
        · ipureintro; rfl
        iintro -
        (try wp_auto)
        have hxs2 := hxs.2
        simp only [List.getD_cons_zero] at hxs2
        rw [Hj.2.2] at hxs2
        have hlin2 := (realM_lin_iff _ _ _ hag hLlen hLval _).2 hxs2
        have hrange : ∀ x ∈ xs, 0 ≤ sint.Z x ∧ (sint.Z x).toNat < os.length := by
          intro x hx
          refine ⟨hxs.1 x hx, ?_⟩
          have := (hlin2.2.1 (sint.Z x).toNat).1 (List.mem_map_of_mem hx)
          rw [Holen]; exact this.1
        wp_apply wp_orderByLinearization osl lsl0 os xs (DFrac.own 1) DFrac.discard hrange $$ [$Hos $Hxs]
          as %lo ⟨Hlo, Hos, -⟩
        imod ownSlice_persist _ _ _ $$ Hlo with #Hlo
        ihave #Hrep2 := opReps_pick os _ xs $$ Hor
        (try wp_auto)
        rc_tail (xs.filterMap fun x => os[(sint.Z x).toNat]?) (xs.map fun x => (sint.Z x).toNat)
      · exact absurd hlinM hnL
      · -- Unknown: porcupine's verdict
        wp_if_destruct
        · exact absurd Hif (by decide)
        · (try wp_auto)
          iapply HΦ; ipureintro
          exact ⟨by decide, fun h => by omega⟩
    · -- no unary operation: nothing to order
      have hU0 : (fmapH unaryOf (histR lops vs)).length = 0 := by
        have : ¬ sint.Z (W64 0) < sint.Z psl.len := by first | exact Hif | exact dec_false Hif
        have := Hpsl.1; have := Hpsl.2
        rw [← hpsl]; word
      have hU : fmapH unaryOf (histR lops vs) = [] := List.eq_nil_of_length_eq_zero hU0
      have hos : os = [] := List.eq_nil_of_length_eq_zero (by rw [Holen, hU0])
      have hlin2 := hπ2
      imod ownSlice_persist _ _ _ $$ Hos with #Hlo
      ihave #Hrep2 : [∗list] c;op ∈ os;vals (fmapH unaryOf (histR lops vs)) π2, opRep (GF := GF) c op $$ []
      · rw [hos, hU]
        have h0 : ∀ l : List Nat, l.filterMap (fun _ => (none : Option (Input × RResp))) = [] := by
          intro l; induction l <;> simp_all [List.filterMap_cons]
        simp only [vals, List.getElem?_nil, Option.map_none, h0]
        iapply BigSepL2.bigSepL2_nil.2
        itrivial
      obtain ⟨lo, hlo⟩ : ∃ lo, lo = osl := ⟨_, rfl⟩
      subst hlo
      clear hU0 hU hos
      (try wp_auto)
      rc_tail os π2

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
