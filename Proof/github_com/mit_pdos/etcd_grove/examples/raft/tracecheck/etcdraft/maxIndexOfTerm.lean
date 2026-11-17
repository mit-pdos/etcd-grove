/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `maxIndexOfTerm`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.maxIndexOfTerm
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StateRead

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

theorem maxIndexOfTerm.wp_proof : maxIndexOfTerm.spec (GF := GF) (hG := hG) := by
  intro sl l t
  wp_start as ⟨#Hl, %Hlen⟩
  iunfold logRO at Hl
  icases Hl with ⟨%es, #Hes, #Hb⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hb
  have hlz : sint.Z sl.len = (l.length : Int) := by rw [← Hbl, Hel.1]; word
  let f : Nat → Nat → Nat := fun acc n => if ((l[n]?).map Entry.term) == some (sint.Z t) then n + 1 else acc
  wp_auto
  ihave IH : iprop(∃ (k mv : w64),
      "n" ∷ n_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sl.len + 1 ∧
        sint.Z mv = ((List.range (sint.nat k - 1)).foldl f 0 : Nat)⌝) $$ [n m]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 1) - 1 = 0 from rfl]; rfl
  wp_for IH
  obtain ⟨hk1, hk2, hkm⟩ := Hk
  wp_if_destruct
  · have hk0 : 0 ≤ sint.Z (k - W64 1) := by clear hkm; word
    have hkk : sint.Z (k - W64 1) = sint.Z k - 1 := by clear hkm; word
    have Hlt : sint.nat (k - W64 1) < es.length := by rw [Hel.1]; clear hkm; word
    obtain ⟨e, He⟩ : ∃ e, es[sint.nat (k - W64 1)]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat (k - W64 1)]? = some x := ⟨_, List.getElem?_eq_getElem (Hbl ▸ Hlt)⟩
    ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hb
    iunfold entryRO at Hex
    icases Hex with ⟨%Hex, -⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z sl.len from
      ⟨hk0, by clear hkm; word⟩))]
    icases ownSlice_elem_acc _ e sl _ es hk0 He $$ Hes with ⟨He', -⟩
    icases typedPointsto_split _ _ _ $$ He' with Hef
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hef
    wp_auto
    have hk' : sint.nat (k + W64 1) - 1 = (sint.nat k - 1) + 1 := by clear hkm; word
    have hkn : sint.nat (k - W64 1) = sint.nat k - 1 := by clear hkm; word
    have hfold : (List.range (sint.nat (k + W64 1) - 1)).foldl f 0 =
        f ((List.range (sint.nat k - 1)).foldl f 0) (sint.nat k - 1) := by
      rw [hk', List.range_succ, List.foldl_append]; rfl
    rw [hkn] at Hx
    wp_if_destruct
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hkm; word, by clear hkm; word, ?_⟩
      rw [hfold]
      have : f ((List.range (sint.nat k - 1)).foldl f 0) (sint.nat k - 1) = sint.nat k := by
        simp only [f, Hx, Option.map_some, Hex.1, beq_iff_eq]
        rw [ite_true]; show (sint.Z k).toNat - 1 + 1 = (sint.Z k).toNat; omega
      rw [this]; clear hkm; word
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hkm; word, by clear hkm; word, ?_⟩
      rw [hfold, hkm]
      have hne : ¬ x.term = sint.Z t := by rw [← Hex.1]; exact fun h => Hif ((int_eq_iff _ _).2 h)
      simp only [f, Hx, Option.map_some, beq_iff_eq, Option.some.injEq, hne, ite_false]
  · try wp_auto
    iapply HΦ
    ipureintro
    have : sint.nat k - 1 = l.length := by rw [← Hbl, Hel.1]; clear hkm; word
    rw [hkm, this]
    rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
