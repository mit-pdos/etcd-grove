/- Lean-first (no Rocq counterpart). The proof of `walFold`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walFold
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walSaveSnap
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.phsNext
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.appendEnts
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

theorem tSaveSnap_ents_sub (c : TContents) (idx term : w64) (e : TEnt)
    (he : e ∈ (tSaveSnap c idx term).ents) : e ∈ c.ents := by
  unfold tSaveSnap at he
  split at he
  · exact he
  · simp only at he
    split at he
    · exact List.mem_of_mem_drop he
    · simp at he

theorem walFold.wp_proof (wp_walSaveSnap : walSaveSnap.spec (GF := GF) (hG := hG))
    (wp_phsNext : phsNext.spec (GF := GF) (hG := hG))
    (wp_appendEnts : appendEnts.spec (GF := GF) (hG := hG)) :
    walFold.spec (GF := GF) (hG := hG) := by
  intro s h
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
      "%Hsub" ∷ ⌜∀ e ∈ cur.ents, ∃ o ∈ h, o.snap = false ∧ e ∈ o.ents⌝ ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i s h He0]
  · iexists W64 0, _, tC0
    iframe
    simp only [contentsRep]
    isplitl []
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      · simp only [tC0]; iexact He0
    isplit
    · ipureintro; intro e he; simp [tC0] at he
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
    have hmem : op ∈ h := List.mem_of_getElem? Hop
    rw [hsn]
    cases hos : op.snap
    · wp_auto
      iunfold contentsRep at Hc
      icases Hc with ⟨%Hcf, #Hce⟩
      wp_apply wp_phsNext
      obtain ⟨hchs, hcbi, hcbt⟩ := Hcf
      wp_apply wp_appendEnts as %r ⟨%rs, #Hrs, %Hrsub⟩
      · isplitl []
        · iexact Hce
        · iexact Hoe
      wp_for_post
      iframe
      iexists i + W64 1, _, { cur with hs := tPhsNext cur.hs op.hs, ents := rs }
      iframe
      iunfold contentsRep
      isplitl []
      · isplitr
        · ipureintro; simp [hchs, hhs, hcbi, hcbt]
        · iexact Hrs
      ipureintro
      refine ⟨fun e he => ?_, by word, by word⟩
      rcases Hrsub e he with h1 | h1
      · exact Hsub e h1
      · exact ⟨op, hmem, hos, h1⟩
    · wp_auto
      wp_apply wp_walSaveSnap $$ [$Hc] as %sv' Hc
      wp_for_post
      iframe
      iexists i + W64 1, sv', _
      iframe
      ipureintro
      refine ⟨fun e he => Hsub e (tSaveSnap_ents_sub _ _ _ e he), by word, by word⟩
  · wp_end

end proof

end etcd_wal
end EtcdGrove
end Perennial
