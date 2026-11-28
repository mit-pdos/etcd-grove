module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeItemRVs
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
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj item)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem decItemRVsL_drop (s : GoString) (j : Nat) (hj : j < s.length) :
    decItemRVsL (s.drop j) =
      if s.length - j < 16 then none
      else if s.length - (j + 16) < (bytesBE ((s.drop (j + 8)).take 8)).toNat then none
      else match decodeD ((s.drop (j + 16)).take (bytesBE ((s.drop (j + 8)).take 8)).toNat) with
        | none => none
        | some o => (decItemRVsL (s.drop (j + 16 + (bytesBE ((s.drop (j + 8)).take 8)).toNat))).map
            fun rest => { o with ResourceVersion' := bytesBE ((s.drop j).take 8) } :: rest := by
  have hne : s.drop j ≠ [] := by simp; omega
  rw [decItemRVsL, dif_neg hne]
  simp only [List.length_drop, List.drop_drop]
  rfl

theorem decodeItemRVs.wp_proof
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_decodeObj : decodeObj.spec (GF := GF) (hG := hG)) :
    decodeItemRVs.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as -
  wp_auto
  ihave HI : (∃ (j : w64) (sl : GoSlice) (os0 : List Obj),
      "i" ∷ i_ptr ↦ j ∗ "its" ∷ its_ptr ↦ sl ∗
      "Hw" ∷ sl ↦* os0.map (fun o => item.mk (objKeyL o) o false) ∗
      "Hc" ∷ ownSliceCap item sl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ s.length ∧
        decItemRVsL s = (decItemRVsL (s.drop (sint.nat j))).map (fun rest => os0 ++ rest)⌝ :
      IProp GF) $$ [i its]
  · iexists W64 0, slice.nil, []
    iframe
    isplitl
    · simp only [List.map_nil]; iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro
      refine ⟨by word, by word, ?_⟩
      simp only [List.nil_append, Option.map_id']
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
    rw [Hj.2.2, hdrop, show decItemRVsL [] = some [] by rw [decItemRVsL]; rfl]
    simp only [Option.map_some, List.append_nil]
    isplitr
    · ipureintro; first | rfl | trivial
    iframe
  rw [decide_eq_true hlt, if_pos (by simp)]
  have hjl : sint.nat j < s.length := by word
  have hstep := decItemRVsL_drop s (sint.nat j) hjl
  (try wp_auto)
  wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len s) as %Hlen2
  (try wp_auto)
  wp_if_destruct
  · have h16 : s.length - sint.nat j < 16 := by word
    wp_for_post
    iapply HΦ
    rw [Hj.2.2, hstep, if_pos h16]
    simp only [Option.map_none]
    ipureintro; first | rfl | trivial
  have h16 : ¬ s.length - sint.nat j < 16 := by word
  have hj8 : sint.nat (j + W64 8) = sint.nat j + 8 := by word
  have hj16 : sint.nat (j + W64 16) = sint.nat j + 16 := by word
  have hs1 : 0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z (j + W64 8) ∧
      sint.Z (j + W64 8) ≤ (s.length : Int) := ⟨Hj.1, by word, by word⟩
  have hs2 : 0 ≤ sint.Z (j + W64 8) ∧ sint.Z (j + W64 8) ≤ sint.Z (j + W64 16) ∧
      sint.Z (j + W64 16) ≤ (s.length : Int) := ⟨by word, by word, by word⟩
  iterate 4 ((try simp only [hs1, hs2, ↓reduceIte]); (try wp_auto))
  have hparse : ∀ k : Nat, k + 8 ≤ s.length → parseRVD ((s.drop k).take 8) = some (bytesBE ((s.drop k).take 8)) := by
    intro k hk
    have hl8 : ((s.drop k).take 8).length = 8 := by simp; omega
    unfold parseRVD
    rw [hl8]
    rfl
  simp only [hj8]
  rw [show sint.nat j + 8 - sint.nat j = 8 by omega]
  wp_apply wp_parseRV as %rvw %err1 Hp1
  rw [hparse (sint.nat j) (by omega)]
  icases Hp1 with %Hp1
  obtain ⟨rfl, rfl⟩ := Hp1
  iterate 3 ((try simp only [hs1, hs2, ↓reduceIte]); (try wp_auto))
  simp only [hj16, hj8]
  rw [show sint.nat j + 16 - (sint.nat j + 8) = 8 by omega]
  wp_apply wp_parseRV as %nw %err2 Hp2
  rw [hparse (sint.nat j + 8) (by omega)]
  icases Hp2 with %Hp2
  obtain ⟨rfl, rfl⟩ := Hp2
  (try wp_auto)
  wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len s) as %Hlen3
  (try wp_auto)
  rw [if_neg h16] at hstep
  wp_if_destruct
  · have hn : s.length - (sint.nat j + 16) < (bytesBE ((s.drop (sint.nat j + 8)).take 8)).toNat := by
      word
    wp_for_post
    iapply HΦ
    rw [Hj.2.2, hstep, if_pos hn]
    simp only [Option.map_none]
    ipureintro; first | rfl | trivial
  have hn : ¬ s.length - (sint.nat j + 16) < (bytesBE ((s.drop (sint.nat j + 8)).take 8)).toNat := by
    word
  rw [if_neg hn] at hstep
  have hs3 : 0 ≤ sint.Z (j + W64 16) ∧
      sint.Z (j + W64 16) ≤ sint.Z (j + W64 16 + bytesBE ((s.drop (sint.nat j + 8)).take 8)) ∧
      sint.Z (j + W64 16 + bytesBE ((s.drop (sint.nat j + 8)).take 8)) ≤ (s.length : Int) :=
    ⟨by word, by word, by word⟩
  iterate 3 ((try simp only [hs3, ↓reduceIte]); (try wp_auto))
  have hNn : sint.nat (j + W64 16 + bytesBE ((s.drop (sint.nat j + 8)).take 8)) - sint.nat (j + W64 16) =
      (bytesBE ((s.drop (sint.nat j + 8)).take 8)).toNat := by word
  rw [hNn, hj16]
  wp_apply wp_string_to_bytes as %bs ⟨Hbs, -⟩
  wp_apply wp_decodeObj $$ [$Hbs] as %o %ok ⟨-, %Hdo⟩
  rcases hdd : decodeD ((s.drop (sint.nat j + 16)).take (bytesBE ((s.drop (sint.nat j + 8)).take 8)).toNat)
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
  let o' : Obj := { o with ResourceVersion' := bytesBE ((s.drop (sint.nat j)).take 8) }
  wp_apply wp_slice_literal (V := item) (l := [item.mk (objKeyL o') o' false])
  isplitr
  · ipureintro; rfl
  iintro %nsl ⟨Hn, -⟩
  wp_apply wp_slice_append $$ [$Hw $Hc $Hn] as %sl' ⟨Hw', Hc', -⟩
  (try wp_auto)
  wp_for_post
  iframe
  iexists _, sl', os0 ++ [o']
  simp only [List.map_append, List.map_cons, List.map_nil]
  iframe
  ipureintro
  have hjn : sint.nat (j + W64 16 + bytesBE ((s.drop (sint.nat j + 8)).take 8)) =
      sint.nat j + 16 + (bytesBE ((s.drop (sint.nat j + 8)).take 8)).toNat := by word
  refine ⟨by word, by rw [hjn]; omega, ?_⟩
  rw [hjn, Hj.2.2, hstep, Option.map_map]
  congr 1
  funext rest
  simp [o']

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
