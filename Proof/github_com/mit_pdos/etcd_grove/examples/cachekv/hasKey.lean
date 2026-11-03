/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/cachekv/hasKey.lean` (2026-11-02): the
loop over the key-values, none of the prefix read of the key.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.hasKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.cachekv go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

theorem hasKey.wp_proof : hasKey.spec (GF := GF) (hG := hG) := by
  intro sl ps s key
  wp_start as ⟨#Hs, #Hh⟩
  ihave %Hl := ownSlice_len $$ Hs
  iunfold kvsHold at Hh
  icases Hh with ⟨%Hlen, #Hkv⟩
  wp_auto
  ihave HI : (∃ (j : w64) (p0 : Loc),
      "i" ∷ i_ptr ↦ j ∗ "kv" ∷ kv_ptr ↦ p0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        ∀ v ∈ s.take (sint.nat j), v.key ≠ key⌝ : IProp GF) $$ [i kv]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ps (sint.nat j) as p
    obtain ⟨v, hv⟩ : ∃ v, s[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact (List.getElem?_eq_some_iff.1 Hp_lookup).1)⟩
    wp_apply wp_load_slice_index sl (sint.Z j) ps DFrac.discard p Hj.1 $$ [Hs] as -
    · iframe #; ipureintro; exact Hp_lookup
    ihave #Hv := Hkv $$ %(sint.nat j) %p %v %Hp_lookup %hv
    iunfold kvValAt at Hv
    icases Hv with ⟨%keySl, %valSl, #HkF, #HkS, -, -, -, -, -, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string keySl v.key DFrac.discard $$ [HkS] as -
    · iframe #
    (try wp_auto)
    have Htake : s.take (sint.nat (j + W64 1)) = s.take (sint.nat j) ++ [v] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hv]; rfl
    wp_if_destruct
    · (try wp_auto)
      wp_for_post
      iapply HΦ
      ipureintro
      simp only [true_iff]
      exact ⟨v, List.mem_of_getElem? hv, rfl⟩
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Htake]
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact Hj.2.2 w hw
      · rw [List.mem_singleton.1 hw]; exact Hif
  · (try wp_auto)
    iapply HΦ
    ipureintro
    have : s.take (sint.nat j) = s := List.take_of_length_le (by rw [← Hlen]; word)
    rw [this] at Hj
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    exact fun v hv h => Hj.2.2 v hv h

end proof

end cachekv
end EtcdGrove
end Perennial
