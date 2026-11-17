module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeWEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvBytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input WEvent)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem encodeWEvents.wp_proof
    (wp_encodeObj : encodeObj.spec (GF := GF) (hG := hG))
    (wp_rvBytes : rvBytes.spec (GF := GF) (hG := hG)) :
    encodeWEvents.spec (GF := GF) (hG := hG) := by
  intro sl evs
  wp_start as #Hs
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hs, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
  ihave HI : (∃ (j k : w64) (out : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "Hiu" ∷ iu_ptr ↦ k ∗ "out" ∷ out_ptr ↦ out ∗
      "Ho" ∷ out ↦* encWEventsL ((ws.map wevOf).take (sint.nat j)) ∗
      "Hc" ∷ ownSliceCap w8 out (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        ∀ e ∈ (ws.map wevOf).take (sint.nat j), (encodeWith tagV1 e.o).length < 2 ^ 63⌝ : IProp GF)
      $$ [i Hiu out]
  · iexists W64 0, _, slice.nil
    iframe
    isplitl
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero,
        show encWEventsL [] = [] from rfl]
      iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro
      refine ⟨by word, by word, fun e he => ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero] at he
      cases he
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    have Hjall := Hj.2.2
    list_elem ws (sint.nat j) as w
    icases ownSlice_elem_acc (sint.Z j) w sl DFrac.discard _ Hj.1 Hw_lookup $$ Hs with ⟨#Hel, -⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) ws DFrac.discard w Hj.1 $$ [Hs] as -
    · isplit
      · iexact Hs
      · ipureintro; exact Hw_lookup
    (try wp_auto)
    iStructNamed Hel
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_encodeObj $$ [$Obj] as %e ⟨He, -⟩
    (try wp_auto)
    iStructNamed Obj
    simp only [Hb', _root_.and_self, ↓reduceIte]
    (try wp_auto)
    cases ha : w.Obj'.Annotated'
    all_goals
      (try wp_auto)
      simp only [Hb', _root_.and_self, ↓reduceIte]
      (try wp_auto)
      wp_apply wp_slice_literal (V := w8) [_, _]
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply wp_slice_append $$ [$Ho $Hc $Hlit] as %s1 ⟨Hs1, Hc1, -⟩
      (try wp_auto)
      simp only [Hb', _root_.and_self, ↓reduceIte]
      (try wp_auto)
      wp_apply wp_rvBytes
      (try wp_auto)
      wp_apply wp_string_to_bytes as %s2 ⟨Hs2, -⟩
      wp_apply wp_slice_append $$ [$Hs1 $Hc1 $Hs2] as %s3 ⟨Hs3, Hc3, -⟩
      (try wp_auto)
      ihave %Hel' := ownSlice_len $$ He
      (try wp_auto)
      wp_apply wp_rvBytes
      (try wp_auto)
      wp_apply wp_string_to_bytes as %s4 ⟨Hs4, -⟩
      wp_apply wp_slice_append $$ [$Hs3 $Hc3 $Hs4] as %s5 ⟨Hs5, Hc5, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hs5 $Hc5 $He] as %s6 ⟨Hs6, Hc6, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, j, s6
      iframe
      have hlen : e.len = W64 ((encodeWith tagV1 w.Obj').length : Int) := by have := Hel'; word
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one,
        List.getElem?_map, Hw_lookup]
      simp only [Option.map_some, Option.toList_some, encWEventsL, List.map_append,
        List.flatten_append, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, encWEvL, wevOf, ha, hlen, List.append_assoc]
      have hb : W8 (sint.Z w.Type') = W8 ((uint.nat w.Type' : Nat) : Int) := by word
      rw [← hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro
      refine ⟨by word, by word, fun e he => ?_⟩
      rcases List.mem_append.1 he with he | he
      · exact Hjall e he
      · simp only [List.mem_singleton] at he
        subst he
        simp only [wevOf]
        have := Hel'.1; word
  · (try wp_auto)
    wp_apply wp_bytes_to_string $$ [$Ho] as -
    (try wp_auto)
    have : (ws.map wevOf).take (sint.nat j) = ws.map wevOf :=
      List.take_of_length_le (by simp; word)
    have Hall := Hj.2.2
    rw [this] at Hall ⊢
    iapply HΦ; ipureintro; exact Hall

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
