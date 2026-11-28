/-
(hraft_robust R3) The proof of `disk.(*Disk).encode`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putUint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__encode

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.encode.wp_proof
    (wp_putUint64 : github_com.hashicorp.raft.examples.hraftnet.disk.putUint64.spec (GF := GF) (hG := hG))
    (wp_putBytes : github_com.hashicorp.raft.examples.hraftnet.disk.putBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.encode.spec (GF := GF) (hG := hG) := by
  intro d I stg
  wp_start as Hd
  iunfold diskMem at Hd
  icases Hd with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hentl := BigSepL2.bigSepL2_length $$ Hent
  wp_auto
  wp_apply (wp_putUint64 slice.nil []) $$ [] as %b0 ⟨Hb, Hcap⟩
  · isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  rw [List.nil_append, dk_w64_of_length lvs es.len Hesl, Hentl]
  ihave HI : (∃ (i : w64) (bb : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗
      "Hb" ∷ bb ↦* (encU64 (W64 I.ents.length) ++ (I.ents.take (sint.nat i)).flatMap encEnt) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗ "Hes" ∷ es ↦* lvs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z es.len⌝ : IProp GF) $$ [i b Hb Hcap Hes]
  · iexists W64 0, b0
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hil : sint.nat i < lvs.length := dk_idx_lt i es.len _ Hesl Hi.1 Hif
    list_elem lvs (sint.nat i) as lv
    list_elem I.ents (sint.nat i) as e
    ihave #Her := BigSepL2.bigSepL2_lookup Hlv_lookup He_lookup $$ Hent
    iunfold entRep at Her
    icases Her with ⟨%Hef, #Hdata, #Hext⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len := ⟨Hi.1, Hif⟩
    icases ownSlice_elem_acc (sint.Z i) lv es (DFrac.own 1) lvs Hi.1
      (by rw [dk_toNat_sint]; exact Hlv_lookup) $$ Hes with ⟨Hv, Hclose⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap⟩
    wp_apply wp_putBytes $$ [$Hb $Hcap $Hdata] as %b4 ⟨Hb, Hcap, -⟩
    wp_apply wp_putBytes $$ [$Hb $Hcap $Hext] as %b5 ⟨Hb, Hcap, -⟩
    ihave Hes := Hclose $$ Hv
    rw [list_set_lookup_self lvs _ lv (by rw [dk_toNat_sint]; exact Hlv_lookup)]
    wp_for_post
    iframe
    iexists i + W64 1, b5
    obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i es.len Hi.1 Hif
    rw [hs1, dk_flatMap_take_succ I.ents encEnt _ e He_lookup]
    obtain ⟨h1, h2, h3⟩ := Hef
    unfold encEnt
    rw [h1, h2, h3]
    simp only [List.append_assoc]
    iframe
    ipureintro; exact ⟨hs2, hs3⟩
  · rw [dk_flatMap_take_length I.ents encEnt _ (by rw [← Hentl]; exact dk_idx_eq i es.len _ Hesl Hi.2 Hif)]
    ihave %Hksl := ownSlice_len $$ Hks
    ihave %Hkrl := BigSepL2.bigSepL2_length $$ Hkr
    ihave %Hvsl := ownSlice_len $$ Hvs
    ihave %Hvrl := BigSepL2.bigSepL2_length $$ Hvr
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %c0 ⟨Hb, Hcap⟩
    rw [dk_w64_of_length kss ks.len Hksl, Hkrl]
    ihave HI2 : (∃ (i : w64) (bb : GoSlice),
        "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗
        "Hb" ∷ bb ↦* (encU64 (W64 I.ents.length) ++ I.ents.flatMap encEnt ++ encU64 (W64 I.kv.length) ++
          (I.kv.take (sint.nat i)).flatMap encKV) ∗
        "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ks.len⌝ : IProp GF) $$ [i b Hb Hcap]
    · iexists W64 0, c0
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
      iframe
      ipureintro; constructor <;> word
    wp_for HI2
    wp_if_destruct
    · have hil : sint.nat i < kss.length := dk_idx_lt i ks.len _ Hksl Hi.1 Hif
      list_elem kss (sint.nat i) as k
      list_elem vss (sint.nat i) as v
      list_elem I.kv (sint.nat i) as p
      ihave #Hk := BigSepL2.bigSepL2_lookup Hk_lookup Hp_lookup $$ Hkr
      ihave #Hv := BigSepL2.bigSepL2_lookup Hv_lookup Hp_lookup $$ Hvr
      have hvb : sint.Z i < sint.Z vs.len := by
        have : sint.nat i < sint.nat vs.len := by rw [← Hvsl.1, Hvrl, ← Hkrl]; exact hil
        word
      have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ks.len := ⟨Hi.1, Hif⟩
      have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z vs.len := ⟨Hi.1, hvb⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index ks (sint.Z i) kss (DFrac.own 1) k Hi.1) $$ [$Hks] as Hks
      · ipureintro; rw [dk_toNat_sint]; exact Hk_lookup
      wp_apply wp_putBytes $$ [$Hb $Hcap $Hk] as %c1 ⟨Hb, Hcap, -⟩
      simp only [hb2, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index vs (sint.Z i) vss (DFrac.own 1) v Hi.1) $$ [$Hvs] as Hvs
      · ipureintro; rw [dk_toNat_sint]; exact Hv_lookup
      wp_apply wp_putBytes $$ [$Hb $Hcap $Hv] as %c2 ⟨Hb, Hcap, -⟩
      wp_for_post
      iframe
      iexists i + W64 1, c2
      obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i ks.len Hi.1 Hif
      rw [hs1, dk_flatMap_take_succ I.kv encKV _ p Hp_lookup]
      unfold encKV
      simp only [List.append_assoc]
      iframe
      ipureintro; exact ⟨hs2, hs3⟩
    · rw [dk_flatMap_take_length I.kv encKV _ (by rw [← Hkrl]; exact dk_idx_eq i ks.len _ Hksl Hi.2 Hif)]
      ihave %Hiksl := ownSlice_len $$ Hiks
      ihave %Hikrl := BigSepL2.bigSepL2_length $$ Hikr
      ihave %Hivsl := ownSlice_len $$ Hivs
      wp_apply wp_putUint64 $$ [$Hb $Hcap] as %c3 ⟨Hb, Hcap⟩
      rw [dk_w64_of_length ikss iks.len Hiksl, Hikrl]
      ihave HI3 : (∃ (i : w64) (bb : GoSlice),
          "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗
          "Hb" ∷ bb ↦* (encU64 (W64 I.ents.length) ++ I.ents.flatMap encEnt ++ encU64 (W64 I.kv.length) ++
            I.kv.flatMap encKV ++ encU64 (W64 I.ikv.length) ++ (I.ikv.take (sint.nat i)).flatMap encIKV) ∗
          "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z iks.len⌝ : IProp GF) $$ [i b Hb Hcap]
      · iexists W64 0, c3
        simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
        iframe
        ipureintro; constructor <;> word
      wp_for HI3
      wp_if_destruct
      · have hil : sint.nat i < ikss.length := dk_idx_lt i iks.len _ Hiksl Hi.1 Hif
        list_elem ikss (sint.nat i) as k
        list_elem I.ikv (sint.nat i) as p
        ihave #Hk := BigSepL2.bigSepL2_lookup Hk_lookup Hp_lookup $$ Hikr
        have hvl : (I.ikv.map Prod.snd)[sint.nat i]? = some p.2 := by
          rw [List.getElem?_map, Hp_lookup]; rfl
        have hvb : sint.Z i < sint.Z ivs.len := by
          have : sint.nat i < sint.nat ivs.len := by
            rw [← Hivsl.1, List.length_map, ← Hikrl]; exact hil
          word
        have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z iks.len := ⟨Hi.1, Hif⟩
        have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ivs.len := ⟨Hi.1, hvb⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index iks (sint.Z i) ikss (DFrac.own 1) k Hi.1) $$ [$Hiks] as Hiks
        · ipureintro; rw [dk_toNat_sint]; exact Hk_lookup
        wp_apply wp_putBytes $$ [$Hb $Hcap $Hk] as %c4 ⟨Hb, Hcap, -⟩
        simp only [hb2, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index ivs (sint.Z i) (I.ikv.map Prod.snd) (DFrac.own 1) p.2 Hi.1) $$ [$Hivs]
          as Hivs
        · ipureintro; rw [dk_toNat_sint]; exact hvl
        wp_apply wp_putUint64 $$ [$Hb $Hcap] as %c5 ⟨Hb, Hcap⟩
        wp_for_post
        iframe
        iexists i + W64 1, c5
        obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i iks.len Hi.1 Hif
        rw [hs1, dk_flatMap_take_succ I.ikv encIKV _ p Hp_lookup]
        unfold encIKV
        simp only [List.append_assoc]
        iframe
        ipureintro; exact ⟨hs2, hs3⟩
      · rw [dk_flatMap_take_length I.ikv encIKV _
          (by rw [← Hikrl]; exact dk_idx_eq i iks.len _ Hiksl Hi.2 Hif)]
        wp_apply wp_putUint64 $$ [$Hb $Hcap] as %c6 ⟨Hb, Hcap⟩
        iapply HΦ
        iframe
        iunfold diskMem
        iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss
        iframe
        iframe #

end proof

end Perennial
