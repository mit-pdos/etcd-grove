/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `confsAfterCount`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.confsAfterCount
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsConf
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem confsAfterCount_step (l : List Entry) (a d i : Nat) (hi : a + d = i) (h : i < l.length) :
    (((l.drop a).take (d + 1)).filter isConf).length =
      (((l.drop a).take d).filter isConf).length + (if isConf l[i] then 1 else 0) := by
  subst hi
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h, List.filter_append]
  simp only [Option.toList_some, List.length_append]
  cases h' : isConf l[a + d] <;> simp [h']

theorem confsAfterCount_arith (kv a : w64) (L : Nat) (hL : (L : Int) < 2 ^ 63 - 1) (ha0 : 0 ≤ sint.Z a)
    (hk0 : sint.Z a + 1 ≤ sint.Z kv) (hkl : sint.Z kv ≤ L) :
    sint.nat (kv + W64 1) = sint.nat kv + 1 ∧ sint.nat (kv - W64 1) = sint.nat kv - 1 ∧
      sint.nat a + 1 ≤ sint.nat kv ∧ sint.Z (kv - W64 1) = sint.Z kv - 1 ∧ sint.nat (kv - W64 1) < L ∧
      0 ≤ sint.Z (kv - W64 1) ∧ sint.Z a + 1 ≤ sint.Z (kv + W64 1) ∧ sint.Z (kv + W64 1) ≤ L + 1 := by
  refine ⟨by word, by word, by word, by word, by word, by word, by word, by word⟩

theorem confsAfterCount_inc (nv : w64) (c L : Nat) (hL : (L : Int) < 2 ^ 63 - 1) (hc : c ≤ L)
    (hn : sint.Z nv = c) : sint.Z (nv + W64 1) = ((c + 1 : Nat) : Int) := by
  push_cast; rw [← hn]; word

theorem confsAfterCount.wp_proof (wp_IsConf : IsConf.spec (GF := GF) (hG := hG)) :
    confsAfterCount.spec (GF := GF) (hG := hG) := by
  intro sl l a k
  wp_start as ⟨#Hl, %Hk, %Ha, %Hlen⟩
  ihave #Hl' := Hl
  iunfold logRO at Hl'
  icases Hl' with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  have hlz : sint.Z sl.len = (l.length : Int) := by rw [← Hll, Hel.1]; word
  unfold confsAfterCount at Hk
  have ha0 : 0 ≤ sint.Z a := by
    rcases Int.lt_or_le (sint.Z a) 0 with h | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at Hk; cases Hk
    · exact h
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at Hk
  have hk : ((l.drop (sint.nat a)).filter isConf).length = k := by
    exact Except.ok.inj Hk
  clear Hk
  wp_auto
  ihave IH : iprop(∃ (kv nv : w64),
      "k" ∷ k_ptr ↦ kv ∗ "n" ∷ n_ptr ↦ nv ∗
      "%Hn" ∷ ⌜sint.Z a + 1 ≤ sint.Z kv ∧ (sint.Z kv ≤ l.length + 1 ∨ sint.Z kv = sint.Z a + 1) ∧
        sint.Z nv = ((((l.drop (sint.nat a)).take (sint.nat kv - sint.nat a - 1)).filter isConf).length : Int)⌝)
      $$ [k n]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by right; word, ?_⟩
    rw [show sint.nat (a + W64 1) - sint.nat a - 1 = 0 by word]
    simp
  wp_for IH
  obtain ⟨hk0, hk1, hkn⟩ := Hn
  have hcnt : (((l.drop (sint.nat a)).take (sint.nat kv - sint.nat a - 1)).filter isConf).length ≤
      l.length := by
    have := List.length_filter_le isConf ((l.drop (sint.nat a)).take (sint.nat kv - sint.nat a - 1))
    have h2 := List.length_take_le' (sint.nat kv - sint.nat a - 1) (l.drop (sint.nat a))
    have h3 := List.length_drop (i := sint.nat a) (l := l)
    omega
  wp_if_destruct
  · have hkl : sint.Z kv ≤ l.length := by rw [← hlz]; exact Hif
    obtain ⟨h1, h2, h3, hidx, hlt, hidx0, hkp0, hkp1⟩ := confsAfterCount_arith kv a l.length Hlen ha0 hk0 hkl
    have hd : sint.nat (kv + W64 1) - sint.nat a - 1 = (sint.nat kv - sint.nat a - 1) + 1 := by omega
    have hi : sint.nat a + (sint.nat kv - sint.nat a - 1) = sint.nat (kv - W64 1) := by omega
    obtain ⟨e, He⟩ : ∃ e, es[sint.nat (kv - W64 1)]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hll]; exact hlt)⟩
    have Hx : l[sint.nat (kv - W64 1)]? = some l[sint.nat (kv - W64 1)] := List.getElem?_eq_getElem hlt
    ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) He Hx $$ Hle
    wp_apply wp_load_index sl (kv - W64 1) es e hidx0 He $$ [Hes]
    · iexact Hes
    try wp_auto
    wp_apply wp_IsConf e _ $$ [Hex]
    · iexact Hex
    iintro -
    have hstep := confsAfterCount_step l (sint.nat a) (sint.nat kv - sint.nat a - 1) _ hi hlt
    cases hc : isConf l[sint.nat (kv - W64 1)]
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨hkp0, Or.inl hkp1, ?_⟩
      rw [hd, hstep, hc, hkn]; simp
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨hkp0, Or.inl hkp1, ?_⟩
      rw [hd, hstep, hc]
      exact confsAfterCount_inc nv _ l.length Hlen hcnt hkn
  · try wp_auto
    iapply HΦ
    ipureintro
    rw [hkn, ← hk, List.take_of_length_le (by
      rw [List.length_drop]
      have : ¬ sint.Z kv ≤ l.length := by rw [← hlz]; exact Hif
      have e1 : (sint.nat kv : Int) = sint.Z kv := by word
      have e2 : (sint.nat a : Int) = sint.Z a := by word
      omega)]

end proof

end AntCheck
end EtcdGrove
end Perennial
