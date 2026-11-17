module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeWEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeObj
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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

theorem decWEventsL_drop (s : GoString) (j : Nat) (hj : j < s.length) :
    decWEventsL (s.drop j) =
      if s.length - j < 18 then none
      else if s.length - (j + 18) < (bytesBE ((s.drop (j + 10)).take 8)).toNat then none
      else match decodeD ((s.drop (j + 18)).take (bytesBE ((s.drop (j + 10)).take 8)).toNat) with
        | none => none
        | some o => (decWEventsL (s.drop (j + 18 + (bytesBE ((s.drop (j + 10)).take 8)).toNat))).map
            fun rest => WEv.mk (s.getD j (W8 0)).toNat
              (withRvAnn o (bytesBE ((s.drop (j + 2)).take 8)) (decide (s.getD (j + 1) (W8 0) = W8 1)))
              :: rest := by
  have hne : s.drop j ≠ [] := by simp; omega
  rw [decWEventsL, dif_neg hne]
  have h1 : ∀ k, (s.drop k).headD (W8 0) = s.getD k (W8 0) := by
    intro k
    simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
  simp only [List.length_drop, List.drop_drop, h1]
  rfl

theorem decodeWEvents.wp_proof
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_decodeObj : decodeObj.spec (GF := GF) (hG := hG)) :
    decodeWEvents.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as -
  wp_auto
  ihave HI : (∃ (j : w64) (sl : GoSlice) (ws : List WEvent),
      "i" ∷ i_ptr ↦ j ∗ "evs" ∷ evs_ptr ↦ sl ∗ "Hw" ∷ sl ↦* ws ∗
      "Hc" ∷ ownSliceCap WEvent sl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ s.length ∧
        decWEventsL s = (decWEventsL (s.drop (sint.nat j))).map (fun rest => ws.map wevOf ++ rest)⌝ :
      IProp GF) $$ [i evs]
  · iexists W64 0, slice.nil, []
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro
      refine ⟨by word, by word, ?_⟩
      simp only [List.map_nil, List.nil_append, Option.map_id']
      rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
  wp_for HI
  wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len s) as %Hlen
  (try wp_auto)
  have hnt : ¬ ((#false : val) = #true) := fun h => by have := go.intoVal_inj h; simp at this
  by_cases hlt : sint.Z j < sint.Z (W64 (s.length : Int))
  case neg =>
    rw [decide_eq_false hlt, if_neg (by simpa using hnt)]
    (try wp_auto)
    (try rw [if_pos (by simp)])
    (try wp_auto)
    iapply HΦ
    have hdrop : s.drop (sint.nat j) = [] := List.drop_eq_nil_of_le (by word)
    rw [Hj.2.2, hdrop, show decWEventsL [] = some [] by rw [decWEventsL]; rfl]
    simp only [Option.map_some, List.append_nil]
    isplitr
    · ipureintro; first | rfl | trivial
    unfold wevsOwnM
    iexists ws
    iframe
    ipureintro; rfl
  rw [decide_eq_true hlt, if_pos (by simp)]
  have hjl : sint.nat j < s.length := by word
  have hstep := decWEventsL_drop s (sint.nat j) hjl
  (try wp_auto)
  wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len s) as %Hlen2
  (try wp_auto)
  wp_if_destruct
  · have h18 : s.length - sint.nat j < 18 := by word
    wp_for_post
    iapply HΦ
    rw [Hj.2.2, hstep, if_pos h18]
    simp only [Option.map_none]
    ipureintro; first | rfl | trivial
  have h18 : ¬ s.length - sint.nat j < 18 := by word
  have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
  have hj2 : sint.nat (j + W64 2) = sint.nat j + 2 := by word
  have hj10 : sint.nat (j + W64 10) = sint.nat j + 10 := by word
  have hj18 : sint.nat (j + W64 18) = sint.nat j + 18 := by word
  have hg0 : s[sint.nat j]? = some (s.getD (sint.nat j) (W8 0)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have hg1 : s[sint.nat (j + W64 1)]? = some (s.getD (sint.nat j + 1) (W8 0)) := by
    rw [hj1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have hz0 : 0 ≤ sint.Z j := Hj.1
  have hz1 : 0 ≤ sint.Z (j + W64 1) := by word
  have hs1 : 0 ≤ sint.Z (j + W64 2) ∧ sint.Z (j + W64 2) ≤ sint.Z (j + W64 10) ∧
      sint.Z (j + W64 10) ≤ (s.length : Int) := ⟨by word, by word, by word⟩
  have hs2 : 0 ≤ sint.Z (j + W64 10) ∧ sint.Z (j + W64 10) ≤ sint.Z (j + W64 18) ∧
      sint.Z (j + W64 18) ≤ (s.length : Int) := ⟨by word, by word, by word⟩
  iterate 4 ((try simp only [hz0, hz1, ↓reduceIte, hg0, hg1, hs1, hs2]); (try wp_auto))
  have hparse : ∀ k : Nat, k + 8 ≤ s.length → parseRVD ((s.drop k).take 8) = some (bytesBE ((s.drop k).take 8)) := by
    intro k hk
    have hl8 : ((s.drop k).take 8).length = 8 := by simp; omega
    unfold parseRVD
    rw [hl8]
    rfl
  simp only [hj10, hj2]
  rw [show sint.nat j + 10 - (sint.nat j + 2) = 8 by omega]
  wp_apply wp_parseRV as %rvw %err1 Hp1
  rw [hparse (sint.nat j + 2) (by omega)]
  icases Hp1 with %Hp1
  obtain ⟨rfl, rfl⟩ := Hp1
  iterate 3 ((try simp only [hz0, hz1, ↓reduceIte, hg0, hg1, hs1, hs2]); (try wp_auto))
  simp only [hj18, hj10]
  rw [show sint.nat j + 18 - (sint.nat j + 10) = 8 by omega]
  wp_apply wp_parseRV as %nw %err2 Hp2
  rw [hparse (sint.nat j + 10) (by omega)]
  icases Hp2 with %Hp2
  obtain ⟨rfl, rfl⟩ := Hp2
  (try wp_auto)
  wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len s) as %Hlen3
  (try wp_auto)
  rw [if_neg h18] at hstep
  wp_if_destruct
  · have hn : s.length - (sint.nat j + 18) < (bytesBE ((s.drop (sint.nat j + 10)).take 8)).toNat := by
      word
    wp_for_post
    iapply HΦ
    rw [Hj.2.2, hstep, if_pos hn]
    simp only [Option.map_none]
    ipureintro; first | rfl | trivial
  have hn : ¬ s.length - (sint.nat j + 18) < (bytesBE ((s.drop (sint.nat j + 10)).take 8)).toNat := by
    word
  rw [if_neg hn] at hstep
  have hs3 : 0 ≤ sint.Z (j + W64 18) ∧
      sint.Z (j + W64 18) ≤ sint.Z (j + W64 18 + bytesBE ((s.drop (sint.nat j + 10)).take 8)) ∧
      sint.Z (j + W64 18 + bytesBE ((s.drop (sint.nat j + 10)).take 8)) ≤ (s.length : Int) :=
    ⟨by word, by word, by word⟩
  iterate 3 ((try simp only [hs3, ↓reduceIte]); (try wp_auto))
  have hNn : sint.nat (j + W64 18 + bytesBE ((s.drop (sint.nat j + 10)).take 8)) - sint.nat (j + W64 18) =
      (bytesBE ((s.drop (sint.nat j + 10)).take 8)).toNat := by word
  rw [hNn, hj18]
  wp_apply wp_string_to_bytes as %bs ⟨Hbs, -⟩
  wp_apply wp_decodeObj $$ [$Hbs] as %o %ok ⟨-, %Hdo⟩
  rcases hdd : decodeD ((s.drop (sint.nat j + 18)).take (bytesBE ((s.drop (sint.nat j + 10)).take 8)).toNat)
    with _ | ob
  · rw [hdd] at Hdo
    subst Hdo
    rw [hdd] at hstep
    (try wp_auto)
    wp_for_post
    iapply HΦ
    rw [Hj.2.2, hstep]
    simp only [Option.map_none]
    ipureintro; first | rfl | trivial
  rw [hdd] at Hdo hstep
  obtain ⟨rfl, rfl⟩ := Hdo
  (try wp_auto)
  let ev : WEvent := ⟨W64 (uint.Z (s.getD (sint.nat j) (W8 0))),
    { o with ResourceVersion' := bytesBE ((s.drop (sint.nat j + 2)).take 8),
             Annotated' := decide (s.getD (sint.nat j + 1) (W8 0) = W8 1) }⟩
  have hev : wevOf ev = WEv.mk (s.getD (sint.nat j) (W8 0)).toNat
      (withRvAnn o (bytesBE ((s.drop (sint.nat j + 2)).take 8))
        (decide (s.getD (sint.nat j + 1) (W8 0) = W8 1))) := by
    simp only [wevOf, ev, withRvAnn, WEv.mk.injEq, _root_.and_true]
    have := (s.getD (sint.nat j) (W8 0)).isLt
    word
  wp_apply wp_slice_literal (V := WEvent) (l := [ev])
  isplitr
  · ipureintro; rfl
  iintro %nsl ⟨Hn, -⟩
  wp_apply wp_slice_append $$ [$Hw $Hc $Hn] as %sl' ⟨Hw', Hc', -⟩
  (try wp_auto)
  wp_for_post
  iframe
  iexists _, sl', ws ++ [ev]
  iframe
  ipureintro
  have hjn : sint.nat (j + W64 18 + bytesBE ((s.drop (sint.nat j + 10)).take 8)) =
      sint.nat j + 18 + (bytesBE ((s.drop (sint.nat j + 10)).take 8)).toNat := by word
  refine ⟨by word, by rw [hjn]; omega, ?_⟩
  rw [hjn, Hj.2.2, hstep, Option.map_map]
  congr 1
  funext rest
  simp [List.map_append, hev]

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
