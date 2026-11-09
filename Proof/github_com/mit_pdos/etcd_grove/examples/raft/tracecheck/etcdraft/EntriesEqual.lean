/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `EntriesEqual`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Entry__Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem EntriesEqual.wp_proof (wp_EntryEqual : Entry.Equal.spec (GF := GF) (hG := hG)) :
    EntriesEqual.spec (GF := GF) (hG := hG) := by
  intro al a bl b
  wp_start as ⟨#Ha, #Hb⟩
  iunfold logRO at Ha Hb
  icases Ha with ⟨%es, #Hes, #Hae⟩
  icases Hb with ⟨%fs, #Hfs, #Hbf⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hfl := ownSlice_len $$ Hfs
  ihave %Hael := BigSepL2.bigSepL2_length $$ Hae
  ihave %Hbfl := BigSepL2.bigSepL2_length $$ Hbf
  wp_auto
  wp_if_destruct
  · have hxy : es.length = fs.length := by rw [Hel.1, Hfl.1, Hif]
    have hab : a.length = b.length := by rw [← Hael, ← Hbfl, hxy]
    ihave IH : iprop(∃ (n kv : w64),
        "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z al.len ∧ a.take (sint.nat n) = b.take (sint.nat n)⌝)
        $$ [i k]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IH
    obtain ⟨hn0, hn1, hnt⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat n < es.length := by rw [Hel.1]; word
      obtain ⟨e, He⟩ : ∃ e, es[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨f, Hf⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem (hxy ▸ Hlt)⟩
      obtain ⟨x, Hx⟩ : ∃ x, a[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem (Hael ▸ Hlt)⟩
      obtain ⟨y, Hy⟩ : ∃ y, b[sint.nat n]? = some y :=
        ⟨_, List.getElem?_eq_getElem (Hbfl ▸ hxy ▸ Hlt)⟩
      ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hae
      ihave #Hfy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hf Hy $$ Hbf
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z al.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index al (sint.Z n) es DFrac.discard e hn0 $$ [Hes] as -
      · isplitr
        · iexact Hes
        ipureintro; exact He
      try wp_auto
      have Hif' : sint.Z n < sint.Z bl.len := by
        have : sint.nat n < fs.length := hxy ▸ Hlt
        rw [Hfl.1] at this; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z bl.len from ⟨hn0, Hif'⟩))]
      wp_apply wp_load_slice_index bl (sint.Z n) fs DFrac.discard f hn0 $$ [Hfs] as -
      · isplitr
        · iexact Hfs
        ipureintro; exact Hf
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z al.len from ⟨hn0, Hif⟩))]
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Entry.TypeAssumptions.ptr_Equal_unfold.method_unfold]
      try wp_auto
      wp_apply wp_load_slice_index al (sint.Z n) es DFrac.discard e hn0 $$ [Hes] as -
      · isplitr
        · iexact Hes
        ipureintro; exact He
      try wp_auto
      wp_apply wp_EntryEqual e x f y $$ [Hex Hfy]
      · iframe Hex Hfy
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        have hxy' : x = y := Hif
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, List.take_add_one,
          hnt, Hx, Hy, hxy']
      · -- `a[k] != b[k]`
        wp_for_post
        try wp_auto
        have : decide (a = b) = false := by
          rw [decide_eq_false_iff_not]; intro h
          rw [h, Hy] at Hx; cases Hx
          exact Hif rfl
        rw [this]
        iapply HΦ; ipureintro; trivial
    · try wp_auto
      have hnx : sint.nat n = a.length := by rw [← Hael, Hel.1]; word
      have : decide (a = b) = true := by
        rw [decide_eq_true_iff]
        rw [hnx, List.take_length, hab, List.take_length] at hnt
        exact hnt
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have : decide (a = b) = false := by
      rw [decide_eq_false_iff_not]; intro h
      apply Hif
      have := congrArg List.length h
      rw [← Hael, ← Hbfl, Hel.1, Hfl.1] at this; word
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
