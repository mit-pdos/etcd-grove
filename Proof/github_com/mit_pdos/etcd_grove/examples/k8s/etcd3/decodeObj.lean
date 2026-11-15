module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getField

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- One `getField` of `decodeObj` at the index `j` (`sint.Z j = i`, within the data); a failing read
is `decodeD d = none`, by `hdn` (the earlier reads' equations); the next goal has the field `f`,
the index `j'` (`sint.Z j' = i'`) and `hf : getFieldD d i = some (f, i')`. -/
local macro "get_field " j:term:max i:term:max hf:ident f:ident j':ident i':ident hj':ident :
    tactic => `(tactic| (
  wp_apply wp_getField sl dq d $j (by first | word | omega) (by first | word | omega) $$ [Hs] as %$f %$j' %okf ⟨Hs, %Hg⟩
  · iframe Hs
  rw [show sint.nat $j = $i by first | word | omega] at Hg
  cases $hf:ident : getFieldD d $i
  case none =>
    rw [$hf:ident] at Hg
    subst Hg
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have hdn : decodeD d = none := by
      unfold decodeD
      rw [if_neg hnl, if_neg hbad]
      simp only [*]
    rw [hdn]
  rename_i p
  obtain ⟨_, $i'⟩ := p
  rw [$hf:ident] at Hg
  obtain ⟨rfl, rfl, $hj':ident⟩ := Hg
  obtain ⟨hjeq, _, _⟩ := getFieldD_some _ _ _ _ $hf:ident
  have := hjeq.symm
  clear hjeq
  (try wp_auto)))

set_option hygiene false in
/-- The end of `decodeObj`: the value is the rest of the data, from the index `j5` (`= i5`). -/
local macro "finish_decode" : tactic => `(tactic| (
  have hj5n : sint.nat j5 = i5 := by first | word | omega
  rw [if_pos (show 0 ≤ sint.Z j5 ∧ sint.Z j5 ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap by
    first | word | omega)]
  icases (ownSlice_slice j5 sl.len sl dq d (by first | word | omega)).1 $$ Hs with ⟨A, B, C⟩
  wp_apply wp_bytes_to_string _ _ dq $$ [B] as B
  · iexact B
  ihave Hs := (ownSlice_slice j5 sl.len sl dq d (by first | word | omega)).2 $$ [A B C]
  · iframe A B C
  (try wp_auto)
  iapply HΦ
  iframe Hs
  ipureintro
  have hdec : decodeD d = some ⟨ns, name, uid, d.drop i5, node, app, 0, false⟩ := by
    unfold decodeD; rw [if_neg hnl, if_neg hbad]; simp only [h1, h2, h3, h4, h5]
  rw [hdec]
  refine ⟨rfl, ?_⟩
  unfold subslice
  rw [hj5n, show sint.nat sl.len = d.length by first | word | omega, List.take_of_length_le (by simp)]))

theorem decodeObj.wp_proof (wp_getField : getField.spec (GF := GF) (hG := hG)) :
    decodeObj.spec (GF := GF) (hG := hG) := by
  intro sl dq d
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  (try wp_auto)
  have hlen : (d.length : Int) = sint.Z sl.len := by rw [Hl.1]; word
  wp_if_destruct
  · -- too short
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : decodeD d = none := by
      unfold decodeD; rw [if_pos (by word)]
    rw [this]
  -- the tag
  icases (ownSlice_slice (W64 0) (W64 3) sl dq d ⟨by word, by word, by word⟩).1 $$ Hs
    with ⟨H0, Ht, H3⟩
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 3) ∧
    sint.Z (W64 3) ≤ sint.Z sl.cap by word)]
  wp_apply wp_bytes_to_string _ _ dq $$ [$Ht] as Ht
  ihave Hs := (ownSlice_slice (W64 0) (W64 3) sl dq d ⟨by word, by word, by word⟩).2 $$ [H0 Ht H3]
  · rw [show sint.nat (W64 0) = 0 from rfl, show sint.nat (W64 3) = 3 from rfl]
    iframe H0 H3 Ht
  have hsub : subslice 0 3 d = d.take 3 := by
    unfold subslice; simp
  simp only [hsub]
  have hnl : ¬ d.length < 3 := by word
  by_cases hbad : d.take 3 ≠ tagV1 ∧ d.take 3 ≠ tagV0
  · rw [decide_eq_false (show ¬ d.take 3 = go!"v1:" from hbad.1)]
    (try wp_auto)
    rw [decide_eq_false (show ¬ d.take 3 = go!"v0:" from hbad.2)]
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : decodeD d = none := by
      unfold decodeD
      rw [if_neg hnl, if_pos hbad]
    rw [this]
  -- either tag takes the same path
  by_cases hv1 : d.take 3 = go!"v1:"
  · rw [decide_eq_true hv1]
    (try wp_auto)
    get_field (W64 3) 3 h1 ns j1 i1 hj1
    get_field j1 i1 h2 name j2 i2 hj2
    get_field j2 i2 h3 uid j3 i3 hj3
    get_field j3 i3 h4 node j4 i4 hj4
    get_field j4 i4 h5 app j5 i5 hj5
    finish_decode
  · rw [decide_eq_false hv1]
    (try wp_auto)
    have hv0 : d.take 3 = go!"v0:" := by
      by_cases h : d.take 3 = go!"v0:"
      · exact h
      · exact absurd ⟨hv1, h⟩ hbad
    rw [decide_eq_true hv0]
    (try wp_auto)
    get_field (W64 3) 3 h1 ns j1 i1 hj1
    get_field j1 i1 h2 name j2 i2 hj2
    get_field j2 i2 h3 uid j3 i3 hj3
    get_field j3 i3 h4 node j4 i4 hj4
    get_field j4 i4 h5 app j5 i5 hj5
    finish_decode

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
