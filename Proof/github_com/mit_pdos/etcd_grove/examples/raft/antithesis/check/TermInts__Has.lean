/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `TermInts.Has`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__Has
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

theorem TermInts.Has.wp_proof : TermInts.Has.spec (GF := GF) (hG := hG) := by
  intro sl f t
  wp_start as #Hs
  iunfold termIntsRO at Hs
  icases Hs with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  wp_auto
  ihave IH : iprop(∃ (n : w64) (y : G.TermInt),
      "i" ∷ i_ptr ↦ n ∗ "p" ∷ p_ptr ↦ y ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ TermFn.has (f.take (sint.nat n)) (sint.Z t) = false⌝) $$ [i p]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · word
    · word
    · rw [show sint.nat (W64 0) = 0 from rfl]; rfl
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < f.length := by rw [← Hl, Hlen.1]; word
    obtain ⟨y0, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem (Hl ▸ Hlt)⟩
    obtain ⟨p1, Hp1⟩ : ∃ p, f[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have HTV := forall₂_getElem Hrel (sint.nat n) (Hl ▸ Hlt) Hlt
    rw [Option.some.inj ((List.getElem?_eq_getElem (Hl ▸ Hlt)).symm.trans Hy),
      Option.some.inj ((List.getElem?_eq_getElem Hlt).symm.trans Hp1)] at HTV
    have HT : sint.Z y0.T' = f[sint.nat n]!.1 := by rw [HTV.1]; simp [Hp1]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) gs DFrac.discard y0 Hn.1 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    obtain ⟨p0, Hp0⟩ : ∃ p, f[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have HT' : sint.Z y0.T' = p0.1 := by rw [HT]; simp [Hp0]
    wp_if_destruct
    · wp_for_post
      have : f.has (sint.Z y0.T') = true := by
        unfold TermFn.has; rw [List.any_eq_true]
        exact ⟨p0, List.mem_of_getElem? Hp0, by rw [← HT']; simp⟩
      rw [this]
      iapply HΦ; ipureintro; trivial
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨?_, ?_, ?_⟩
      · word
      · word
      · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hp0]
        unfold TermFn.has at Hn ⊢
        rw [List.any_append, Hn.2.2]
        simp only [Option.toList_some, List.any_cons, List.any_nil, Bool.false_or, Bool.or_false,
          beq_eq_false_iff_ne, ne_eq]
        intro h; apply Hif; rw [← HT'] at h; exact BitVec.toInt_inj.mp h
  · try wp_auto
    have hnx : sint.nat n = f.length := by rw [← Hl, Hlen.1]; word
    have h := Hn.2.2
    rw [hnx, List.take_length] at h
    rw [h]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
