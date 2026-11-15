/- Lean-first (no Rocq counterpart). The proof of `walFoldChk`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walFoldChk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walSaveSnap
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.phsNext
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.readEnt
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem walFoldChk.wp_proof (wp_walSaveSnap : walSaveSnap.spec (GF := GF) (hG := hG))
    (wp_phsNext : phsNext.spec (GF := GF) (hG := hG)) (wp_readEnt : readEnt.spec (GF := GF) (hG := hG)) :
    walFoldChk.spec (GF := GF) (hG := hG) := by
  intro s h hw
  wp_start as Hr
  iunfold opsRep at Hr
  icases Hr with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %e0 ⟨He0, -⟩
  · ipureintro; word
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist He0
  wp_auto
  ihave HI : (∃ (i : w64) (sv : contents) (cur : TContents),
      "i" ∷ i_ptr ↦ i ∗ "s" ∷ s_ptr ↦ sv ∗ "h" ∷ h_ptr ↦ s ∗ "Hc" ∷ contentsRep sv cur ∗
      "%Hfold" ∷ ⌜tFoldChkFrom tC0 (h.take (sint.nat i)) = some cur⌝ ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i s h He0]
  · iexists W64 0, _, tC0
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, contentsRep]
    isplitl []
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      · simp only [tC0]; iexact He0
    isplit
    · ipureintro; rfl
    · ipureintro; constructor <;> word
  wp_for HI
  cleanup_bool_decide
  wp_if_destruct
  · have hil : sint.nat i < es.length := by
      have : sint.nat i < sint.nat s.len := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, es[sint.nat i]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨Hi.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z i) es DFrac.discard v hb.1 as -
    · isplitl []
      · iexact Hs
      ipureintro
      simpa [sint.nat] using Hv
    icases opsElems_lookup es h (sint.nat i) v Hv $$ Hel with ⟨%op, %Hop, Hopr⟩
    iunfold opRep at Hopr
    icases Hopr with ⟨%Hf, #Hoe⟩
    obtain ⟨hsn, hhs, hix, htm⟩ := Hf
    have hwo := hw op (List.mem_of_getElem? Hop)
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have hstep := tFoldChkFrom_take_succ tC0 h (sint.nat i) op Hop
    rw [Hfold, Option.bind_some] at hstep
    rw [hsn]
    cases hos : op.snap
    · -- a Save
      rw [tFoldChkFrom_save cur op hos] at hstep
      wp_auto
      iunfold contentsRep at Hc
      icases Hc with ⟨%Hcf, #Hce⟩
      obtain ⟨hchs, hcbi, hcbt⟩ := Hcf
      wp_apply wp_phsNext
      ihave %Hoel := ownSlice_len $$ Hoe
      ihave HJ : (∃ (jj : w64) (es_s : GoSlice) (x : List TEnt),
          "j" ∷ j_ptr ↦ jj ∗
          "s" ∷ s_ptr ↦ contents.mk (tPhsNext sv.hs' v.hs') sv.baseIdx' sv.baseTerm' es_s ∗
          "Hxs" ∷ es_s ↦*□ x ∗
          "%Hx" ∷ ⌜(op.ents.take (sint.nat jj)).foldlM (fun ents e => tReadEnt cur.baseIdx ents e) cur.ents =
            some x⌝ ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ sint.Z v.ents'.len⌝ : IProp GF) $$ [j s]
      · iexists W64 0, sv.ents', cur.ents
        iframe
        isplitl []
        · iexact Hce
        isplit
        · ipureintro; rfl
        · ipureintro; constructor <;> word
      wp_for HJ
      icases Hxs with #Hxs
      cleanup_bool_decide
      wp_if_destruct
      · have hjl : sint.nat jj < op.ents.length := by
          have : sint.nat jj < sint.nat v.ents'.len := by word
          omega
        obtain ⟨e, He⟩ : ∃ e, op.ents[sint.nat jj]? = some e := ⟨_, List.getElem?_eq_getElem hjl⟩
        have hb : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z v.ents'.len := ⟨Hj.1, Hif⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index v.ents' (sint.Z jj) op.ents DFrac.discard e hb.1 as -
        · isplitl []
          · iexact Hoe
          ipureintro
          simpa [sint.nat] using He
        have hwe := hwo.2 hos e (List.mem_of_getElem? He)
        wp_apply wp_readEnt sv.baseIdx' es_s x e hwe.2.2.1 as %r %ok Hres
        · iexact Hxs
        have hj1 : sint.nat (jj + W64 1) = sint.nat jj + 1 := by word
        have hxs := tReadEnts_take_succ cur.baseIdx op.ents (sint.nat jj) e He cur.ents
        rw [Hx, Option.bind_some] at hxs
        rw [hcbi]
        cases hre : tReadEnt cur.baseIdx x e with
        | none =>
          simp only [hre, entsRes]
          icases Hres with %hok
          subst hok
          wp_auto
          wp_for_post
          wp_for_post
          iapply HΦ
          have hall := tReadEnts_prefix_none cur.baseIdx op.ents (sint.nat jj + 1) cur.ents (by rw [hxs, hre])
          rw [hall] at hstep
          simp only [Option.map_none] at hstep
          simp only [tFoldChk, tFoldChkFrom_prefix_none tC0 h (sint.nat i + 1) hstep, readRes]
          itrivial
        | some y =>
          simp only [hre, entsRes]
          icases Hres with ⟨%hok, #Hr⟩
          subst hok
          wp_auto
          wp_for_post
          iframe
          iexists jj + W64 1, r, y
          iframe
          isplitl []
          · iexact Hr
          isplit
          · ipureintro; rw [hj1, hxs, hre]
          · ipureintro; constructor <;> word
      · have hjn : sint.nat jj = op.ents.length := by
          have : sint.nat jj = sint.nat v.ents'.len := by word
          omega
        rw [hjn, List.take_length] at Hx
        rw [Hx, Option.map_some] at hstep
        wp_for_post
        iframe
        iexists i + W64 1, _, { cur with hs := tPhsNext cur.hs op.hs, ents := x }
        iframe
        iunfold contentsRep
        isplitl []
        · isplitr
          · ipureintro; simp [hchs, hhs, hcbi, hcbt]
          · iexact Hxs
        isplit
        · ipureintro; rw [hi1, hstep]
        · ipureintro; constructor <;> word
    · -- a snapshot record
      rw [tFoldChkFrom_snap cur op hos] at hstep
      wp_auto
      wp_apply wp_walSaveSnap $$ [$Hc] as %sv' Hc
      wp_for_post
      iframe
      iexists i + W64 1, sv', _
      iframe
      rw [hi1, hstep, hix, htm]
      ipureintro; exact ⟨rfl, by word, by word⟩
  · have hin : sint.nat i = h.length := by
      have : sint.nat i = sint.nat s.len := by word
      omega
    rw [hin, List.take_length] at Hfold
    wp_end
    simp only [tFoldChk, Hfold, readRes]
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
