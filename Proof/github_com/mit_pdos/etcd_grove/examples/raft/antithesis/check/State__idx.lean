/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.idx`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__idx

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

theorem State.idx_findIdx {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (n : Nat) (x : α), xs[n]? = some x → (xs.take n).all (fun y => !p y) = true →
      p x = true → xs.findIdx? p = some n
  | [], _, _, h, _, _ => by simp at h
  | y :: ys, 0, x, h, _, hx => by
    simp at h; subst h; simp [List.findIdx?_cons, hx]
  | y :: ys, n + 1, x, h, hall, hx => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    rw [List.findIdx?_cons, hall.1]
    simp only [Bool.false_eq_true, ite_false]
    rw [State.idx_findIdx p ys n x h hall.2 hx]
    rfl

theorem State.idx_none {α : Type} (p : α → Bool) (xs : List α)
    (h : xs.all (fun y => !p y) = true) : xs.findIdx? p = none := by
  rw [List.findIdx?_eq_none_iff]
  intro y hy
  have := List.all_eq_true.1 h y hy
  simpa using this

theorem State.idx.wp_proof : State.idx.spec (GF := GF) (hG := hG) := by
  intro p s nm k
  wp_start as ⟨#Hs, %Hk⟩
  iunfold stateRO at Hs
  iNamed Hs
  iNamed Hf
  iStructNamed Hp
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hc, #Hsrv, #Hiv, %Hb⟩
  iStructNamed Hc
  iunfold strsRO at Hsrv
  ihave %Hlen := ownSlice_len $$ Hsrv
  unfold State.idx at Hk
  wp_auto
  ihave IH : iprop(∃ (n kk : w64) (xv : Str),
      "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ xv ∗ "k" ∷ k_ptr ↦ kk ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gc.Server'.len ∧
        (s.cfg.server.take (sint.nat n)).all (fun y => !(y == nm)) = true⌝) $$ [i x k]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hna⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < s.cfg.server.length := by clear hna; rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, s.cfg.server[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gc.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) s.cfg.server DFrac.discard y hn0 $$ [Hsrv] as -
    · iframe Hsrv; ipureintro; exact Hy
    try wp_auto
    wp_if_destruct
    · -- found
      try wp_auto
      wp_for_post
      try wp_auto
      have hf : s.cfg.server.findIdx? (· == nm) = some (sint.nat n) :=
        State.idx_findIdx _ _ _ _ Hy hna (by simp [Hif])
      have hk : List.idxOf? nm s.cfg.server = some (sint.nat n) := by
        unfold List.idxOf?; exact hf
      rw [hk] at Hk
      cases Hk
      iapply HΦ
      ipureintro
      exact ⟨by clear hna; word, Hlt⟩
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by clear hna; word, by clear hna; word, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by clear hna; word, List.take_add_one, Hy]
      simp only [Option.toList_some, List.all_append, hna, List.all_cons, List.all_nil, Bool.and_true,
        Bool.true_and]
      simpa using Hif
  · -- not found: excluded by the premise
    exfalso
    have hnx : sint.nat n = s.cfg.server.length := by clear hna; rw [Hlen.1]; word
    rw [hnx, List.take_length] at hna
    have hk : List.idxOf? nm s.cfg.server = none := by
      unfold List.idxOf?; exact State.idx_none _ _ hna
    rw [hk] at Hk
    cases Hk

end proof

end AntCheck
end EtcdGrove
end Perennial
