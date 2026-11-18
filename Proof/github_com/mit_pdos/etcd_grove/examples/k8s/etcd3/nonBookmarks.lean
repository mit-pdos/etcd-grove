module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.nonBookmarks

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

theorem nonBookmarks.wp_proof : nonBookmarks.spec (GF := GF) (hG := hG) := by
  intro s evs
  wp_start as #Hs
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  ihave HI : (∃ (j : w64) (evv : WEvent) (sl : GoSlice) (gs : List WEvent),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ evv ∗ "got" ∷ got_ptr ↦ sl ∗
      "Hw" ∷ sl ↦* gs ∗ "Hc" ∷ ownSliceCap WEvent sl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
        gs.map wevOf = ((ws.map wevOf).take (sint.nat j)).filter (fun e => e.t ≠ 3)⌝ : IProp GF)
      $$ [i ev got]
  · iexists W64 0, _, slice.nil, []
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro; refine ⟨by word, by word, rfl⟩
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
    have h3 : uint.nat w.Type' = 3 ↔ w.Type' = W64 3 := by
      constructor
      · intro h; word
      · intro h; rw [h]; rfl
    (try wp_auto)
    have ht : (wevOf w).t = uint.nat w.Type' := rfl
    wp_if_destruct
    · wp_for_post
      iframe
      iexists j + W64 1, w, sl, gs
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hj1, htake, List.filter_append, Hj.2.2]
      simp [ht, h3, Hif]
    · wp_apply wp_slice_literal (V := WEvent) (l := [w])
      isplitr
      · ipureintro; rfl
      iintro %nsl ⟨Hn, -⟩
      wp_apply wp_slice_append $$ [$Hw $Hc $Hn] as %sl' ⟨Hw', Hc', -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, w, sl', gs ++ [w]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have hne3 : (wevOf w).t ≠ 3 := by rw [ht]; intro h; exact Hif (h3.1 h)
      rw [hj1, htake, List.filter_append, List.map_append, Hj.2.2]
      simp [hne3]
  · (try wp_auto)
    iapply HΦ
    unfold wevsOwnM
    iexists gs
    iframe
    ipureintro
    have : (ws.map wevOf).take (sint.nat j) = ws.map wevOf := List.take_of_length_le (by simp; word)
    rw [Hj.2.2, this]

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
