module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.checkedEvents

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem rejectsL_snoc (l : List WEv) (e : WEv) (rv : Nat) :
    rejectsL (l ++ [e]) rv = ((rejectsL l rv).or (decide (5 ≤ e.t))).or
      ((decide (e.t ≠ 4)).and (decide (rv < uint.nat e.o.ResourceVersion'))) := by
  unfold rejectsL keptL
  rw [List.any_append, List.filter_append, List.any_append]
  cases h1 : l.any (fun e => decide (5 ≤ e.t)) <;>
    cases h2 : (l.filter fun e => decide (e.t ≠ 4)).any (fun e => decide (rv < uint.nat e.o.ResourceVersion')) <;>
    by_cases h4 : e.t = 4 <;> simp [h4]

theorem keptL_snoc (l : List WEv) (e : WEv) :
    keptL (l ++ [e]) = keptL l ++ (if e.t ≠ 4 then [e] else []) := by
  unfold keptL; rw [List.filter_append]; by_cases h : e.t = 4 <;> simp [h]

theorem rejectsL_prefix (l : List WEv) (j : Nat) (rv : Nat) (h : rejectsL (l.take j) rv = true) :
    rejectsL l rv = true := by
  rw [← List.take_append_drop j l]
  unfold rejectsL keptL at *
  rw [List.any_append, List.filter_append, List.any_append]
  simp only [Bool.or_eq_true, List.any_eq_true] at h ⊢
  rcases h with h | h
  · left; left; exact h
  · right; left; exact h

theorem checkedEvents.wp_proof : checkedEvents.spec (GF := GF) (hG := hG) := by
  intro s all rv Hty
  wp_start as #Hs
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  ihave HI : (∃ (j : w64) (evv : WEvent) (sl : GoSlice) (ks : List WEvent),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ evv ∗ "evs" ∷ evs_ptr ↦ sl ∗
      "Hw" ∷ sl ↦* ks ∗ "Hc" ∷ ownSliceCap WEvent sl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
        ks.map wevOf = keptL ((ws.map wevOf).take (sint.nat j)) ∧
        rejectsL ((ws.map wevOf).take (sint.nat j)) (uint.nat rv) = false⌝ : IProp GF)
      $$ [i ev evs]
  · iexists W64 0, _, slice.nil, []
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro; refine ⟨by word, by word, rfl, rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, Hif⟩
    list_elem ws (sint.nat j) as w
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z j) ws _ w Hj.1 $$ [Hk] as -
    · isplit
      · iexact Hk
      · ipureintro; exact Hw_lookup
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : (ws.map wevOf).take (sint.nat j + 1) = (ws.map wevOf).take (sint.nat j) ++ [wevOf w] := by
      rw [List.take_add_one]; simp [Hw_lookup]
    have hwt : uint.nat w.Type' < 2 ^ 63 :=
      Hty (wevOf w) (List.mem_map_of_mem (List.mem_of_getElem? Hw_lookup))
    have ht : (wevOf w).t = uint.nat w.Type' := rfl
    have hrej := rejectsL_snoc ((ws.map wevOf).take (sint.nat j)) (wevOf w) (uint.nat rv)
    have hkept := keptL_snoc ((ws.map wevOf).take (sint.nat j)) (wevOf w)
    rw [Hj.2.2.2, ht] at hrej
    rw [ht] at hkept
    (try wp_auto)
    wp_if_destruct
    · have h5 : 5 ≤ uint.nat w.Type' := by word
      wp_for_post
      iapply HΦ
      rw [rejectsL_prefix _ (sint.nat j + 1) _ (by rw [htake, hrej]; simp [h5]), if_pos rfl]
      ipureintro; rfl
    · have h5 : ¬ 5 ≤ uint.nat w.Type' := by word
      (try wp_auto)
      wp_if_destruct
      · have h4 : uint.nat w.Type' = 4 := by word
        wp_for_post
        iframe
        iexists j + W64 1, w, sl, ks
        iframe
        ipureintro
        refine ⟨by word, by word, ?_, ?_⟩
        · rw [hj1, htake, hkept, Hj.2.2.1]; simp [h4]
        · rw [hj1, htake, hrej]; simp [h5, h4]
      · have h4 : uint.nat w.Type' ≠ 4 := by word
        (try wp_auto)
        wp_if_destruct
        · have hgt : uint.nat rv < uint.nat w.Obj'.ResourceVersion' := by word
          have hr1 : rejectsL ((ws.map wevOf).take (sint.nat j + 1)) (uint.nat rv) = true := by
            rw [htake, hrej]; simp [h5, h4]; exact hgt
          wp_for_post
          iapply HΦ
          rw [rejectsL_prefix _ (sint.nat j + 1) _ hr1, if_pos rfl]
          ipureintro; rfl
        · have hle : ¬ uint.nat rv < uint.nat w.Obj'.ResourceVersion' := by word
          wp_apply wp_slice_literal (V := WEvent) (l := [w])
          isplitr
          · ipureintro; rfl
          iintro %nsl ⟨Hn, -⟩
          wp_apply wp_slice_append $$ [$Hw $Hc $Hn] as %sl' ⟨Hw', Hc', -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, w, sl', ks ++ [w]
          iframe
          ipureintro
          refine ⟨by word, by word, ?_, ?_⟩
          · rw [hj1, htake, hkept, List.map_append, Hj.2.2.1]; simp [h4]
          · rw [hj1, htake, hrej]; simp [h5, h4]; exact Nat.le_of_not_lt hle
  · (try wp_auto)
    have hfull : (ws.map wevOf).take (sint.nat j) = ws.map wevOf := List.take_of_length_le (by simp; word)
    rw [hfull] at Hj
    iapply HΦ
    rw [Hj.2.2.2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr
    · ipureintro; first | rfl | trivial
    unfold wevsOwnM
    iexists ks
    iframe
    ipureintro; exact Hj.2.2.1

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
