/- Lean-first (no Rocq counterpart). Proof of
`PorcupineDag/Spec/github_com/anishathalye/porcupine/chains__computeFirstUnk.lean`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__computeFirstUnk
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.Consistency__Check
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ComputeFirstUnkLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option maxHeartbeats 4000000 in
theorem chains.computeFirstUnk.wp_proof
    (wp_Check : Consistency.Check.spec (GF := GF) (hG := hG)) :
    chains.computeFirstUnk.spec (GF := GF) (hG := hG) := by
  intro ch cl h cs st c cons hok hwf hshape hfu hheads hc0 hcl hprev
  wp_start as ⟨Hch, #Hlin⟩
  iunfold chainsOwnCl at Hch
  icases Hch with ⟨%chV, Hch, %Hclq, Hrep⟩
  subst Hclq
  iunfold chainsRepr at Hrep
  icases Hrep with ⟨%cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  obtain ⟨cvc, hcvc⟩ : ∃ cv, cvs[sint.nat c]? = some cv :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  ihave %Hcllen := ownSlice_len $$ Hcl
  icases (ownSlice_halves chV.clients' cvs).1 $$ Hcl with ⟨HclA, HclB⟩
  icases ownSlice_elem_acc (sint.Z c) cvc chV.clients' _ cvs hc0 hcvc $$ HclA with ⟨Hcvc, HclA⟩
  icases (BigSepL.bigSepL_delete_cond (PROP := IProp GF) (Φ := fun k cv => clientOwn h cs st k cv) hcvc).1 $$ Hcls with ⟨Hc, Hrest⟩
  iunfold clientOwn at Hc
  icases Hc with ⟨%Hcvcf, %cosc, Hcosc, %Hcoc, Hfus⟩
  ihave %Hcoslen := ownSlice_len $$ Hcosc
  have hbc : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z chV.clients'.len := ⟨hc0, by have := Hcllen.1; have := Hcvs.1; word⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hch with ⟨Hch, %Hchnn⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hcvc with ⟨Hcvc, %Hcvcnn⟩
  iStructNamedSuffix Hch "_ch"
  iStructNamedSuffix Hcvc "_cc"
  wp_auto
  simp only [hbc, and_self, ↓reduceIte]
  wp_auto
  simp only [hbc, and_self, ↓reduceIte]
  wp_auto
  have hcn : (sint.Z c).toNat = sint.nat c := rfl
  have hcZ : ((sint.nat c : Nat) : Int) = sint.Z c := Int.toNat_of_nonneg hc0
  have hchlen : cosc.length = (chain cs (sint.nat c)).length := Hcoc.1
  have hlenZ : (((chain cs (sint.nat c)).length : Nat) : Int) = sint.Z cvc.cltOps'.len := by
    rw [← hchlen, Hcoslen.1]; exact Int.toNat_of_nonneg Hcoslen.2
  have hhdZ : sint.Z cvc.head' = ((st.head (sint.nat c) : Nat) : Int) := Hcvcf.2.1
  wp_if_destruct
  · -- the head is past the chain: nothing changes
    ihave Hch := typedPointsto_combine _ chV _ Hchnn $$ [clients_ch numOps_ch frontier_ch __ch]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    ihave Hcvc := typedPointsto_combine _ cvc _ Hcvcnn $$ [id_cc cltOps_cc head_cc nDeps_cc __cc]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    rw [hcn]
    iapply HΦ
    iexists st
    isplitl
    · iapply (chains_restore ch chV h cs st st cvs (sint.nat c) cvc hcvc Hcvs (fun _ _ _ => rfl))
      rw [hcZ]
      iframe
      unfold clientOwn
      iframe
      ipureintro; exact ⟨Hcvcf, Hcoc⟩
    ipureintro
    refine ⟨rfl, rfl, rfl, hshape, hfu, fun c' k => ?_⟩
    have hn : ¬ (c' = sint.nat c ∧ k = st.head c' ∧ k < (chain cs c').length) := by
      rintro ⟨rfl, rfl, hk⟩; omega
    simp [hn]
  · have hhl : st.head (sint.nat c) < (chain cs (sint.nat c)).length := by omega
    have hhdn : (sint.Z cvc.head').toNat = st.head (sint.nat c) := by omega
    obtain ⟨co, oc, hco, hoc, hcc, hrc, hvc⟩ := coOk_get Hcoc hhl
    have hbh : 0 ≤ sint.Z cvc.head' ∧ sint.Z cvc.head' < sint.Z cvc.cltOps'.len := by omega
    simp only [hbc, and_self, ↓reduceIte]
    wp_auto
    simp only [hbc, and_self, ↓reduceIte]
    rw [← hhdn] at hco
    icases ownSlice_elem_acc (sint.Z cvc.head') co cvc.cltOps' _ cosc hbh.1 hco $$ Hcosc
      with ⟨Hco, Hcosc⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hco with ⟨Hco, %Hconn⟩
    iStructNamedSuffix Hco "_co"
    wp_auto
    simp only [hbh, and_self, ↓reduceIte]
    wp_auto
    ihave Hco := typedPointsto_combine _ co _ Hconn $$ [Op_co globalId_co id_co firstUnk_co visited_co __co]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    ihave Hcosc := Hcosc $$ %co Hco
    rw [list_set_lookup_self _ _ _ hco]
    cases hcov : co.visited'
    case true =>
      -- already visited: nothing changes
      wp_auto
      ihave Hch := typedPointsto_combine _ chV _ Hchnn $$ [clients_ch numOps_ch frontier_ch __ch]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      ihave Hcvc := typedPointsto_combine _ cvc _ Hcvcnn $$ [id_cc cltOps_cc head_cc nDeps_cc __cc]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      rw [hcn]
      iapply HΦ
      iexists st
      isplitl
      · iapply (chains_restore ch chV h cs st st cvs (sint.nat c) cvc hcvc Hcvs (fun _ _ _ => rfl))
        rw [hcZ]
        iframe
        unfold clientOwn
        iframe
        ipureintro; exact ⟨Hcvcf, Hcoc⟩
      ipureintro
      refine ⟨rfl, rfl, rfl, hshape, hfu, fun c' k => ?_⟩
      by_cases hn : c' = sint.nat c ∧ k = st.head c' ∧ k < (chain cs c').length
      · obtain ⟨rfl, rfl, -⟩ := hn
        have : st.visAt (sint.nat c) (st.head (sint.nat c)) = true := by
          rw [← hcov, hvc]; rfl
        simp [this]
      · simp [hn]
    wp_auto
    idx_auto [hbc, hbh]
    have hco' : cosc[st.head (sint.nat c)]? = some co := by rw [← hhdn]; exact hco
    icases (BigSepL.bigSepL_delete_cond (PROP := IProp GF)
      (Φ := fun k co => co.firstUnk' ↦* st.fuAt (sint.nat c) k) hco').1 $$ Hfus with ⟨Hfl, Hfurest⟩
    have hfl0 : (st.fuAt (sint.nat c) (st.head (sint.nat c))).length = cs.length :=
      (hshape.2.2.2.2 _ _ hhl).2.2
    ihave IH : iprop(∃ (dv : w64) (fl : List w64),
        "d" ∷ d_ptr ↦ dv ∗ "Hfl" ∷ co.firstUnk' ↦* fl ∗
        "%Hd" ∷ ⌜0 ≤ sint.Z dv ∧ sint.Z dv ≤ cs.length ∧ fl.length = cs.length ∧
          ∀ d', d' < sint.nat dv → d' < cs.length → d' ≠ sint.nat c →
            sint.Z (fl.getD d' 0) = FUe h cs (sint.nat c) d' (st.head (sint.nat c))⌝) $$ [d Hfl]
    · iexists W64 0, st.fuAt (sint.nat c) (st.head (sint.nat c))
      iframe
      ipureintro
      refine ⟨by word, by word, hfl0, fun d' hd' => absurd hd' (by word)⟩
    wp_for IH
    have hclZ : sint.Z chV.clients'.len = (cs.length : Int) := by
      rw [← Hcvs.1, Hcllen.1]; exact (Int.toNat_of_nonneg Hcllen.2).symm
    wp_if_destruct
    · have hdl : sint.nat dv < cs.length := by word
      wp_if_destruct
      · -- `d = c`: skipped
        wp_for_post
        iframe
        iexists dv + W64 1, fl
        iframe
        ipureintro
        refine ⟨by word, by word, Hd.2.2.1, fun d' hd' hd'l hd'c => ?_⟩
        have : d' ≠ sint.nat dv := by intro h'; subst h'; exact hd'c (by rw [Hif])
        exact Hd.2.2.2 d' (by word) hd'l hd'c
      · have hdc : sint.nat dv ≠ sint.nat c := by intro h'; apply Hif; word
        idx_auto [hbc]
        obtain ⟨start, hstart⟩ : ∃ s : Nat, s = if 0 < st.head (sint.nat c) then
            FUe h cs (sint.nat c) (sint.nat dv) (st.head (sint.nat c) - 1) else 0 := ⟨_, rfl⟩
        wp_join iprop(∃ fu0 : w64, "firstUnk" ∷ firstUnk_ptr ↦ fu0 ∗
            "%Hfu0" ∷ ⌜sint.Z fu0 = start⌝ ∗
            "Hcosc" ∷ cvc.cltOps' ↦* cosc ∗
            "Hfurest" ∷ ([∗list] k ↦ y ∈ cosc, if k = st.head (sint.nat c) then emp else
              y.firstUnk' ↦* st.fuAt (sint.nat c) k) ∗
            "head_cc" ∷ (sliceIndexRef client (sint.Z c) chV.clients').[client, go!"head"]
              ↦{DFrac.own (1 : Qp).half} cvc.head' ∗
            "cltOps_cc" ∷ (sliceIndexRef client (sint.Z c) chV.clients').[client, go!"cltOps"]
              ↦{DFrac.own (1 : Qp).half} cvc.cltOps' ∗
            "clients_ch" ∷ ch.[chains, go!"clients"] ↦ chV.clients' ∗
            "ch" ∷ ch_ptr ↦ ch ∗ "c" ∷ c_ptr ↦ c ∗ "d" ∷ d_ptr ↦ dv)
          with [firstUnk Hcosc Hfurest head_cc cltOps_cc clients_ch ch c d] as HR
        · -- a previous operation: its bound
          have hpos : 0 < st.head (sint.nat c) := by word
          have hd1 : st.head (sint.nat c) - 1 < (chain cs (sint.nat c)).length := by omega
          have hbm : 0 ≤ sint.Z (cvc.head' - W64 1) ∧
              sint.Z (cvc.head' - W64 1) < sint.Z cvc.cltOps'.len := by word
          have hm1n : (sint.Z (cvc.head' - W64 1)).toNat = st.head (sint.nat c) - 1 := by word
          obtain ⟨co1, hco1⟩ : ∃ co1, cosc[st.head (sint.nat c) - 1]? = some co1 :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hco1' : cosc[(sint.Z (cvc.head' - W64 1)).toNat]? = some co1 := by rw [hm1n]; exact hco1
          idx_auto [hbc, hbm]
          icases ownSlice_elem_acc (sint.Z (cvc.head' - W64 1)) co1 cvc.cltOps' _ cosc hbm.1 hco1'
            $$ Hcosc with ⟨Hco1, Hcosc⟩
          icases typedPointsto_not_null_dup _ _ _ $$ Hco1 with ⟨Hco1, %Hco1nn⟩
          iStructNamedSuffix Hco1 "_c1"
          wp_auto
          ihave Hco1 := typedPointsto_combine _ co1 _ Hco1nn $$
            [Op_c1 globalId_c1 id_c1 firstUnk_c1 visited_c1 __c1]
          · simp only [TypedPointsto.typedPointstoDef]; iframe
          ihave Hcosc := Hcosc $$ %co1 Hco1
          rw [list_set_lookup_self _ _ _ hco1']
          icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
            (Φ := fun k (y : clientOperation) => if k = st.head (sint.nat c) then emp else
              y.firstUnk' ↦* st.fuAt (sint.nat c) k) hco1).1 $$ Hfurest with ⟨Hf1, Hfurest⟩
          icases (ite_emp_neg (GF := GF) (show ¬ (st.head (sint.nat c) - 1 = st.head (sint.nat c))
            by omega)).1 $$ Hf1 with Hf1
          ihave %Hf1len := ownSlice_len $$ Hf1
          have hfu1 : (st.fuAt (sint.nat c) (st.head (sint.nat c) - 1)).length = cs.length :=
            (hshape.2.2.2.2 _ _ hd1).2.2
          have hbd : 0 ≤ sint.Z dv ∧ sint.Z dv < sint.Z co1.firstUnk'.len := by
            refine ⟨Hd.1, ?_⟩; have := Hf1len.1; have := Hf1len.2; word
          have hx : (st.fuAt (sint.nat c) (st.head (sint.nat c) - 1))[(sint.Z dv).toNat]? =
              some ((st.fuAt (sint.nat c) (st.head (sint.nat c) - 1)).getD (sint.nat dv) 0) := by
            rw [List.getD_eq_getElem?_getD, show (sint.Z dv).toNat = sint.nat dv from rfl,
              List.getElem?_eq_getElem (by omega)]; rfl
          simp only [hbd, and_self, ↓reduceIte]
          wp_apply (wp_load_slice_index co1.firstUnk' (sint.Z dv) _ _ _ Hd.1) $$ [Hf1] as Hf1
          · iframe Hf1; ipureintro; exact hx
          wp_join_done
          ihave Hf1 := (ite_emp_neg (GF := GF) (show ¬ (st.head (sint.nat c) - 1 = st.head (sint.nat c))
            by omega)).2 $$ Hf1
          ihave Hfurest := Hfurest $$ %co1 Hf1
          rw [list_set_lookup_self _ _ _ hco1]
          iexists _
          iframe
          ipureintro
          have hv1 : st.visAt (sint.nat c) (st.head (sint.nat c) - 1) = true := hprev hpos hhl
          rw [hfu _ _ hv1 _ hdl hdc, hstart, ite_eq_left hpos]
        · have hz : ¬ 0 < st.head (sint.nat c) := by word
          iexists W64 0
          iframe
          ipureintro
          rw [hstart, ite_eq_right hz]; rfl
        iNamed HR
        obtain ⟨cvd, hcvd⟩ : ∃ cv, cvs[sint.nat dv]? = some cv :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hbd : 0 ≤ sint.Z dv ∧ sint.Z dv < sint.Z chV.clients'.len := ⟨Hd.1, by word⟩
        icases ownSlice_elem_acc (sint.Z dv) cvd chV.clients' _ cvs Hd.1 hcvd $$ HclB
          with ⟨Hcvd, HclB⟩
        icases typedPointsto_not_null_dup _ _ _ $$ Hcvd with ⟨Hcvd, %Hcvdnn⟩
        iStructNamedSuffix Hcvd "_cd"
        icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
          (Φ := fun k y => if k = sint.nat c then emp else clientOwn h cs st k y) hcvd).1 $$ Hrest
          with ⟨Hcd, Hrest⟩
        icases (ite_emp_neg (GF := GF) hdc).1 $$ Hcd with Hcd
        iunfold clientOwn at Hcd
        icases Hcd with ⟨%Hcvdf, %cosd, Hcosd, %Hcod, Hfusd⟩
        ihave %Hcosdlen := ownSlice_len $$ Hcosd
        have hdlen : cosd.length = (chain cs (sint.nat dv)).length := Hcod.1
        have hLZ : (((chain cs (sint.nat dv)).length : Nat) : Int) = sint.Z cvd.cltOps'.len := by
          rw [← hdlen, Hcosdlen.1]; exact Int.toNat_of_nonneg Hcosdlen.2
        have hLh : (chain cs (sint.nat dv)).length ≤ h.length := chain_length_le hok _
        have hh60 : (h.length : Int) < 2 ^ 60 := hwf.1
        have hsl : start ≤ (chain cs (sint.nat dv)).length := by
          rw [hstart]; split
          · exact fue_le
          · exact Nat.zero_le _
        wp_auto
        have hbd' : 0 ≤ sint.Z dv ∧ sint.Z dv < sint.Z chV.clients'.len := hbd
        -- the exponential search
        wp_join iprop(∃ (iv stepv fdkv : w64) (m : Nat),
            "i" ∷ i_ptr ↦ iv ∗ "step" ∷ step_ptr ↦ stepv ∗ "firstDontKnow" ∷ firstDontKnow_ptr ↦ fdkv ∗
            "%HE" ∷ ⌜sint.Z stepv = 2 ^ m ∧ sint.Z iv = start + 2 ^ m - 1 ∧
              sint.Z iv - 2 ^ m / 2 ≤ (chain cs (sint.nat dv)).length ∧
              (∀ j : Nat, start ≤ j → (j : Int) < sint.Z iv - 2 ^ m / 2 →
                PAt h cs (sint.nat c) (st.head (sint.nat c)) (sint.nat dv) j) ∧
              ((fdkv = W64 (-1) ∧ ((chain cs (sint.nat dv)).length : Int) ≤ sint.Z iv) ∨
               (fdkv = iv ∧ sint.Z iv < (chain cs (sint.nat dv)).length ∧
                ¬ PAt h cs (sint.nat c) (st.head (sint.nat c)) (sint.nat dv) (sint.nat iv)))⌝ ∗
            "Hcosd" ∷ cvd.cltOps' ↦* cosd ∗ "Hcosc" ∷ cvc.cltOps' ↦* cosc ∗
            "consistency" ∷ consistency_ptr ↦ cons ∗
            "op" ∷ op_ptr ↦ sliceIndexRef clientOperation (sint.Z cvc.head') cvc.cltOps' ∗
            "cltOps_cd" ∷ (sliceIndexRef client (sint.Z dv) chV.clients').[client, go!"cltOps"]
              ↦{DFrac.own (1 : Qp).half} cvd.cltOps' ∗
            "clients_ch" ∷ ch.[chains, go!"clients"] ↦ chV.clients' ∗
            "ch" ∷ ch_ptr ↦ ch ∗ "d" ∷ d_ptr ↦ dv) at next
          with [i step firstDontKnow Hcosd Hcosc consistency op cltOps_cd clients_ch ch d] as HE
        · ihave IHE : iprop(∃ (iv stepv : w64) (m : Nat),
              "i" ∷ i_ptr ↦ iv ∗ "step" ∷ step_ptr ↦ stepv ∗
              "%HI" ∷ ⌜sint.Z stepv = 2 ^ m ∧ sint.Z iv = start + 2 ^ m - 1 ∧
                sint.Z iv - 2 ^ m / 2 ≤ (chain cs (sint.nat dv)).length ∧
                (∀ j : Nat, start ≤ j → (j : Int) < sint.Z iv - 2 ^ m / 2 →
                  PAt h cs (sint.nat c) (st.head (sint.nat c)) (sint.nat dv) j)⌝) $$ [i step]
          · iexists fu0, W64 1, 0
            iframe
            ipureintro
            refine ⟨by word, by word, by word, fun j h1 h2 => absurd h2 (by word)⟩
          wp_for IHE
          idx_auto [hbd']
          cleanup_bool_decide
          wp_if_destruct
          · have h2m : (1 : Int) ≤ 2 ^ m := by
              have := Nat.one_le_two_pow (n := m); exact_mod_cast this
            have hiL : sint.Z iv < ((chain cs (sint.nat dv)).length : Int) := by rw [hLZ]; exact Hif
            have hbi : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z cvd.cltOps'.len := ⟨by omega, Hif⟩
            have hiLn : sint.nat iv < (chain cs (sint.nat dv)).length := by word
            obtain ⟨a, ha⟩ : ∃ a, cosd[sint.nat iv]? = some a :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            idx_auto [hbd', hbi]
            wp_apply (wp_check_elems wp_Check consistency_ptr cons cvd.cltOps' cvc.cltOps' cosd cosc
              (sint.Z iv) (sint.Z cvc.head') a co (DFrac.own 1) (DFrac.own 1) hbi.1 hbh.1 ha hco)
              $$ [$consistency $Hcosd $Hcosc] as ⟨consistency, Hcosd, Hcosc⟩
            · iframe #
            have hPiff := pAt_iff_linOrder Hcod Hcoc hiLn hhl ha hco'
            wp_if_destruct
            · -- `HardBefore`: double the step
              have hPi := hPiff.mp Hif
              have hstepL : sint.Z stepv ≤ (chain cs (sint.nat dv)).length := by omega
              wp_for_post
              iframe
              iexists iv + stepv, stepv * W64 2, m + 1
              iframe
              ipureintro
              have e1 : sint.Z (iv + stepv) = sint.Z iv + sint.Z stepv := by word
              have e2 : sint.Z (stepv * W64 2) = sint.Z stepv * 2 := by word
              have hp : (2 : Int) ^ (m + 1) = 2 ^ m * 2 := Int.pow_succ 2 m
              refine ⟨by rw [e2, hp, HI.1], by rw [e1, hp]; omega, by rw [e1, hp]; omega,
                fun j h1 h2 => pAt_down hok hiLn (by
                  rw [e1, hp] at h2
                  have := HI.1
                  have : ((sint.nat iv : Nat) : Int) = sint.Z iv := Int.toNat_of_nonneg hbi.1
                  omega) hPi⟩
            · have hnP := fun hP => Hif (hPiff.mpr hP)
              wp_if_destruct
              · exact absurd Hif (linOrder_ne_conc _ _)
              · wp_for_post
                wp_join_done
                iexists iv, stepv, iv, m
                iframe
                ipureintro
                exact ⟨HI.1, HI.2.1, HI.2.2.1, HI.2.2.2, Or.inr ⟨rfl, hiL, hnP⟩⟩
          · wp_join_done
            iexists iv, stepv, W64 (-1), m
            iframe
            ipureintro
            exact ⟨HI.1, HI.2.1, HI.2.2.1, HI.2.2.2, Or.inl ⟨rfl, by rw [hLZ]; exact Int.not_lt.mp Hif⟩⟩
        iNamed HE
        wp_auto
        wp_join iprop(∃ hv : w64, "high" ∷ high_ptr ↦ hv ∗
            "%Hhv" ∷ ⌜sint.Z hv = min (sint.Z iv) ((chain cs (sint.nat dv)).length : Int)⌝ ∗
            "cltOps_cd" ∷ (sliceIndexRef client (sint.Z dv) chV.clients').[client, go!"cltOps"]
              ↦{DFrac.own (1 : Qp).half} cvd.cltOps' ∗
            "clients_ch" ∷ ch.[chains, go!"clients"] ↦ chV.clients' ∗
            "ch" ∷ ch_ptr ↦ ch ∗ "d" ∷ d_ptr ↦ dv) at next
          with [high cltOps_cd clients_ch ch d] as HH
        · idx_auto [hbd']
          wp_if_destruct
          · idx_auto [hbd']
            wp_join_done
            iexists _
            iframe
            ipureintro
            rw [← hLZ] at Hif ⊢
            omega
          · wp_join_done
            iexists _
            iframe
            ipureintro
            rw [← hLZ] at Hif
            omega
        iNamed HH
        obtain ⟨HEs, HEi, HEl, HEp, HEx⟩ := HE
        have h2m : (1 : Int) ≤ 2 ^ m := by
          have := Nat.one_le_two_pow (n := m); exact_mod_cast this
        have hm2 : (2 : Int) ^ m / 2 ≤ 2 ^ m - 1 := by omega
        have hstepL : sint.Z stepv ≤ 2 * ((chain cs (sint.nat dv)).length : Int) + 2 := by omega
        have hq := sint_sdiv_two (a := stepv) (by omega)
        generalize BitVec.sdiv stepv (W64 2) = q at hq ⊢
        have hlow : sint.Z (iv - q) = sint.Z iv - 2 ^ m / 2 := by rw [← HEs, ← hq]; word
        rw [hlow]
        wp_if_destruct
        · exfalso; omega
        -- the binary search
        ihave IHB : iprop(∃ (lv hv fdkv : w64), "low" ∷ low_ptr ↦ lv ∗ "high" ∷ high_ptr ↦ hv ∗
            "firstDontKnow" ∷ firstDontKnow_ptr ↦ fdkv ∗
            "%HB" ∷ ⌜(start : Int) ≤ sint.Z lv ∧ sint.Z lv ≤ sint.Z hv ∧
              sint.Z hv ≤ ((chain cs (sint.nat dv)).length : Int) ∧
              (∀ j : Nat, start ≤ j → (j : Int) < sint.Z lv →
                PAt h cs (sint.nat c) (st.head (sint.nat c)) (sint.nat dv) j) ∧
              ((fdkv = W64 (-1) ∧ sint.Z hv = ((chain cs (sint.nat dv)).length : Int)) ∨
               (fdkv = hv ∧ sint.Z hv < ((chain cs (sint.nat dv)).length : Int) ∧
                ¬ PAt h cs (sint.nat c) (st.head (sint.nat c)) (sint.nat dv) (sint.nat hv)))⌝)
          $$ [low high firstDontKnow]
        · iexists iv - q, hv, fdkv
          iframe
          ipureintro
          refine ⟨by omega, by omega, by omega, fun j h1 h2 => HEp j h1 (by omega), ?_⟩
          rcases HEx with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨h1, by omega⟩
          · refine Or.inr ⟨by subst h1; word, by omega, ?_⟩
            have : hv = fdkv := by subst h1; word
            rw [this, h1]; exact h3
        wp_for IHB
        obtain ⟨HBs, HBlh, HBh, HBp, HBx⟩ := HB
        wp_if_destruct
        · have hq2 := sint_sdiv_two (a := hv - lv) (by word)
          generalize BitVec.sdiv (hv - lv) (W64 2) = q2 at hq2 ⊢
          have hmid : sint.Z (lv + q2) = sint.Z lv + (sint.Z hv - sint.Z lv) / 2 := by
            have : sint.Z (hv - lv) = sint.Z hv - sint.Z lv := by word
            rw [this] at hq2; rw [← hq2]; word
          generalize lv + q2 = mv at hmid ⊢
          have hml : sint.Z lv ≤ sint.Z mv := by omega
          have hmh : sint.Z mv < sint.Z hv := by omega
          have hbm : 0 ≤ sint.Z mv ∧ sint.Z mv < sint.Z cvd.cltOps'.len := by
            constructor <;> omega
          have hmn : ((sint.nat mv : Nat) : Int) = sint.Z mv := Int.toNat_of_nonneg hbm.1
          have hmLn : sint.nat mv < (chain cs (sint.nat dv)).length := by omega
          obtain ⟨a, ha⟩ : ∃ a, cosd[sint.nat mv]? = some a :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          idx_auto [hbd', hbm]
          wp_apply (wp_check_elems wp_Check consistency_ptr cons cvd.cltOps' cvc.cltOps' cosd cosc
            (sint.Z mv) (sint.Z cvc.head') a co (DFrac.own 1) (DFrac.own 1) hbm.1 hbh.1 ha hco)
            $$ [$consistency $Hcosd $Hcosc] as ⟨consistency, Hcosd, Hcosc⟩
          · iframe #
          have hPiff := pAt_iff_linOrder Hcod Hcoc hmLn hhl ha hco'
          wp_if_destruct
          · -- `HardBefore`: the bound is above `mid`
            have hPm := hPiff.mp Hif
            wp_for_post
            iframe
            iexists mv + W64 1, hv, fdkv
            iframe
            ipureintro
            have e : sint.Z (mv + W64 1) = sint.Z mv + 1 := by word
            refine ⟨by omega, by omega, HBh, fun j h1 h2 => pAt_down hok hmLn (by omega) hPm, HBx⟩
          · have hnP := fun hP => Hif (hPiff.mpr hP)
            wp_if_destruct
            · exact absurd Hif (linOrder_ne_conc _ _)
            · have hleaf : (start : Int) ≤ sint.Z lv ∧ sint.Z lv ≤ sint.Z mv ∧
                  sint.Z mv ≤ ((chain cs (sint.nat dv)).length : Int) ∧
                  (∀ j : Nat, start ≤ j → (j : Int) < sint.Z lv →
                    PAt h cs (sint.nat c) (st.head (sint.nat c)) (sint.nat dv) j) ∧
                  ((mv = W64 (-1) ∧ sint.Z mv = ((chain cs (sint.nat dv)).length : Int)) ∨
                   (mv = mv ∧ sint.Z mv < ((chain cs (sint.nat dv)).length : Int) ∧
                    ¬ PAt h cs (sint.nat c) (st.head (sint.nat c)) (sint.nat dv) (sint.nat mv))) :=
                ⟨HBs, hml, by omega, HBp, Or.inr ⟨rfl, by omega, hnP⟩⟩
              wp_if_destruct
              · wp_for_post
                iframe
                iexists lv, mv, mv
                iframe
                ipureintro; exact hleaf
              · wp_if_destruct
                · wp_for_post
                  iframe
                  iexists lv, mv, mv
                  iframe
                  ipureintro; exact hleaf
                · exfalso
                  rename_i hfd
                  rcases HBx with ⟨h1, -⟩ | ⟨h1, -, -⟩
                  · subst h1; exact hfd (by decide)
                  · subst h1; omega
        · have hlh : sint.Z lv = sint.Z hv := by omega
          have hlv : lv = hv := by word
          subst hlv
          wp_join with [result firstDontKnow]
          · wp_if_destruct
            · exfalso
              rcases HBx with ⟨h1, -⟩ | ⟨h1, -, -⟩
              · subst h1; rename_i hh; exact absurd hh (by decide)
              · subst h1; omega
            · iframe
          -- the linear scan (only after a `DontKnow`: one step)
          wp_join iprop("result" ∷ result_ptr ↦ lv ∗
              "Hcosd" ∷ cvd.cltOps' ↦* cosd ∗ "Hcosc" ∷ cvc.cltOps' ↦* cosc ∗
              "consistency" ∷ consistency_ptr ↦ cons ∗
              "op" ∷ op_ptr ↦ sliceIndexRef clientOperation (sint.Z cvc.head') cvc.cltOps' ∗
              "cltOps_cd" ∷ (sliceIndexRef client (sint.Z dv) chV.clients').[client, go!"cltOps"]
                ↦{DFrac.own (1 : Qp).half} cvd.cltOps' ∗
              "clients_ch" ∷ ch.[chains, go!"clients"] ↦ chV.clients' ∗
              "ch" ∷ ch_ptr ↦ ch ∗ "d" ∷ d_ptr ↦ dv ∗
              "firstDontKnow" ∷ firstDontKnow_ptr ↦ fdkv) at next
            with [result Hcosd Hcosc consistency op cltOps_cd clients_ch ch d firstDontKnow] as HL
          · rcases HBx with ⟨rfl, hL⟩ | ⟨h1, hL, hnP⟩
            · wp_auto
              wp_join_done
            · have h1' := h1.symm
              subst h1'
              have hl0 : 0 ≤ sint.Z lv := by omega
              have hlLn : sint.nat lv < (chain cs (sint.nat dv)).length := by word
              obtain ⟨a, ha⟩ : ∃ a, cosd[sint.nat lv]? = some a :=
                ⟨_, List.getElem?_eq_getElem (by omega)⟩
              have hPiff := pAt_iff_linOrder Hcod Hcoc hlLn hhl ha hco'
              have hbl : 0 ≤ sint.Z lv ∧ sint.Z lv < sint.Z cvd.cltOps'.len := ⟨hl0, by omega⟩
              wp_if_destruct
              · wp_for
                idx_auto [hbd']
                cleanup_bool_decide
                wp_if_destruct
                · idx_auto [hbd', hbl]
                  wp_apply (wp_check_elems wp_Check consistency_ptr cons cvd.cltOps' cvc.cltOps' cosd
                    cosc (sint.Z lv) (sint.Z cvc.head') a co (DFrac.own 1) (DFrac.own 1) hl0 hbh.1 ha hco)
                    $$ [$consistency $Hcosd $Hcosc] as ⟨consistency, Hcosd, Hcosc⟩
                  · iframe #
                  wp_if_destruct
                  · exact absurd (hPiff.mp Hif) hnP
                  · wp_for_post
                    iframe
                    ipureintro; rfl
                · exfalso; have : sint.Z (W64 0) = 0 := rfl; omega
              · exfalso; have : sint.Z (W64 0) = 0 := rfl; omega
          iNamed HL
          -- the result is `FUe`
          have hl0 : 0 ≤ sint.Z lv := by omega
          have hlvn : ((sint.nat lv : Nat) : Int) = sint.Z lv := Int.toNat_of_nonneg hl0
          have hres : sint.Z lv = FUe h cs (sint.nat c) (sint.nat dv) (st.head (sint.nat c)) := by
            have := fue_of_search (k := st.head (sint.nat c)) (r := sint.nat lv) hok
              (by rw [← hstart]; omega) (by omega)
              (fun j hj1 hj2 => HBp j (by rw [hstart]; exact hj1) (by omega))
              (fun hr => by
                rcases HBx with ⟨-, h2⟩ | ⟨-, -, h3⟩
                · omega
                · exact h3)
            omega
          -- `op.firstUnk[d] = result`
          icases ownSlice_elem_acc (sint.Z cvc.head') co cvc.cltOps' _ cosc hbh.1 hco $$ Hcosc
            with ⟨Hco, Hcosc⟩
          icases typedPointsto_not_null_dup _ _ _ $$ Hco with ⟨Hco, %Hconn'⟩
          iStructNamedSuffix Hco "_co"
          wp_auto
          ihave Hco := typedPointsto_combine _ co _ Hconn $$
            [Op_co globalId_co id_co firstUnk_co visited_co __co]
          · simp only [TypedPointsto.typedPointstoDef]; iframe
          ihave Hcosc := Hcosc $$ %co Hco
          rw [list_set_lookup_self _ _ _ hco]
          ihave %Hfllen := ownSlice_len $$ Hfl
          have hbf : 0 ≤ sint.Z dv ∧ sint.Z dv < sint.Z co.firstUnk'.len := by
            refine ⟨Hd.1, ?_⟩; have := Hfllen.1; have := Hfllen.2; have := Hd.2.2.1; word
          simp only [hbf, and_self, ↓reduceIte]
          wp_apply (wp_store_slice_index co.firstUnk' (sint.Z dv) fl lv) $$ [Hfl] as Hfl
          · iframe Hfl; ipureintro; refine ⟨Hd.1, ?_⟩; have := Hd.2.2.1; word
          -- client `d` put back
          ihave Hcvd := typedPointsto_combine _ cvd _ Hcvdnn $$ [id_cd cltOps_cd head_cd nDeps_cd __cd]
          · simp only [TypedPointsto.typedPointstoDef]; iframe
          ihave HclB := HclB $$ %cvd Hcvd
          rw [list_set_lookup_self _ _ _ hcvd]
          ihave Hcd : clientOwn h cs st (sint.nat dv) cvd $$ [Hcosd Hfusd]
          · unfold clientOwn
            iframe
            ipureintro; exact ⟨Hcvdf, Hcod⟩
          ihave Hcd := (ite_emp_neg (GF := GF) hdc).2 $$ Hcd
          ihave Hrest := Hrest $$ %cvd Hcd
          rw [list_set_lookup_self _ _ _ hcvd]
          wp_for_post
          iframe
          iexists dv + W64 1, fl.set (sint.nat dv) lv
          iframe
          ipureintro
          refine ⟨by word, by word, by rw [List.length_set]; exact Hd.2.2.1,
            fun d' hd' hd'l hd'c => ?_⟩
          by_cases hdd : d' = sint.nat dv
          · subst hdd
            rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
            exact hres
          · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hdd),
              ← List.getD_eq_getElem?_getD]
            exact Hd.2.2.2 d' (by word) hd'l hd'c
    · sorry

end proof

end porcupine
end EtcdGrove
end Perennial
