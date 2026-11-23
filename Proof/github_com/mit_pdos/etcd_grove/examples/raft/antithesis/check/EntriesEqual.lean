/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `EntriesEqual`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry__Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem entriesEqualAux_drop (a b : List Entry) (n : Nat) (ha : n < a.length) (hb : n < b.length) :
    entriesEqualAux (a.drop n) (b.drop n) =
      (do if !(← a[n].equal b[n]) then pure false else entriesEqualAux (a.drop (n + 1)) (b.drop (n + 1))) := by
  rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb]
  rfl

theorem EntriesEqual.wp_proof (wp_EntryEqual : Entry.Equal.spec (GF := GF) (hG := hG)) :
    EntriesEqual.spec (GF := GF) (hG := hG) := by
  intro al a bl b r
  wp_start as ⟨#Ha, #Hb, %Hr⟩
  iunfold logRO at Ha Hb
  icases Ha with ⟨%es, #Hes, #Hae⟩
  icases Hb with ⟨%fs, #Hfs, #Hbf⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hfl := ownSlice_len $$ Hfs
  ihave %Hael := BigSepL2.bigSepL2_length $$ Hae
  ihave %Hbfl := BigSepL2.bigSepL2_length $$ Hbf
  unfold entriesEqual at Hr
  wp_auto
  wp_if_destruct
  · have hxy : es.length = fs.length := by rw [Hel.1, Hfl.1, Hif]
    have hab : a.length = b.length := by rw [← Hael, ← Hbfl, hxy]
    rw [ite_eq_right (by omega)] at Hr
    ihave IH : iprop(∃ (n kv : w64),
        "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z al.len ∧
          entriesEqualAux (a.drop (sint.nat n)) (b.drop (sint.nat n)) = .ok r⌝)
        $$ [i k]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simpa using Hr⟩
    wp_for IH
    obtain ⟨hn0, hn1, hnt⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat n < es.length := by rw [Hel.1]; word
      obtain ⟨e, He⟩ : ∃ e, es[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨f, Hf⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem (hxy ▸ Hlt)⟩
      have Hla : sint.nat n < a.length := Hael ▸ Hlt
      have Hlb : sint.nat n < b.length := hab ▸ Hla
      have Hx : a[sint.nat n]? = some a[sint.nat n] := List.getElem?_eq_getElem Hla
      have Hy : b[sint.nat n]? = some b[sint.nat n] := List.getElem?_eq_getElem Hlb
      ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hae
      ihave #Hfy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hf Hy $$ Hbf
      rw [entriesEqualAux_drop a b _ Hla Hlb] at hnt
      cases hc : a[sint.nat n].equal b[sint.nat n] with
      | error _ => rw [hc] at hnt; cases hnt
      | ok c =>
      rw [hc] at hnt
      have Hif' : sint.Z n < sint.Z bl.len := by
        have : sint.nat n < fs.length := hxy ▸ Hlt
        rw [Hfl.1] at this; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z al.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index al (sint.Z n) es DFrac.discard e hn0 $$ [Hes] as -
      · isplitr
        · iexact Hes
        ipureintro; exact He
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z bl.len from ⟨hn0, Hif'⟩))]
      wp_apply wp_load_slice_index bl (sint.Z n) fs DFrac.discard f hn0 $$ [Hfs] as -
      · isplitr
        · iexact Hfs
        ipureintro; exact Hf
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z al.len from ⟨hn0, Hif⟩))]
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry.TypeAssumptions.ptr_Equal_unfold.method_unfold]
      try wp_auto
      wp_apply wp_load_slice_index al (sint.Z n) es DFrac.discard e hn0 $$ [Hes] as -
      · isplitr
        · iexact Hes
        ipureintro; exact He
      try wp_auto
      wp_apply wp_EntryEqual e _ f _ c $$ [Hex Hfy]
      · iframe Hex Hfy; ipureintro; exact hc
      try wp_auto
      cases c
      · -- `a[k] != b[k]`
        try wp_auto
        wp_for_post
        try wp_auto
        cases hnt
        iapply HΦ; ipureintro; trivial
      · try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
        exact hnt
    · try wp_auto
      have hnx : sint.nat n = a.length := by rw [← Hael, Hel.1]; word
      rw [hnx, List.drop_length, hab, List.drop_length] at hnt
      cases hnt
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    rw [ite_eq_left (by
      intro h; apply Hif
      rw [← Hael, ← Hbfl, Hel.1, Hfl.1] at h; word)] at Hr
    cases Hr
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
