/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.ReadAsked` (B 657-661).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ReadAsked
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__ctx
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setReads
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem State.ReadAsked.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_ctx : Event.ctx.spec (GF := GF) (hG := hG))
    (wp_setReads : setReads.spec (GF := GF) (hG := hG)) :
    State.ReadAsked.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  obtain ⟨bb, EE, HW, -, -, hbb, -⟩ := HBd
  unfold numBound at hbb
  unfold State.readAsked at Ho
  obtain ⟨cx, hcx, Ho⟩ := bind_ok Ho
  simp only [pure_ok, Except.ok.injEq] at Ho
  subst Ho
  icases readsRO_at g.Reads' s.reads n ⟨Hn, by rw [HWf.len_reads]; exact Hlt⟩ $$ HReads with ⟨%rv, #Hra, #Hr⟩
  ihave %Hchl := logRO_len _ _ $$ HChain
  have hrl : (s.reads[sint.nat n]!).length ≤ bb := by
    have hn' : sint.nat n < s.reads.length := by rw [HWf.len_reads]; have := sint_nat_cast Hn; omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hn']
    exact (HW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hn')).1
  ihave #Hr' := Hr
  iunfold readRecsRO at Hr'
  icases Hr' with ⟨%items, #Hitems, %Hrel⟩
  ihave %Hil := ownSlice_len $$ Hitems
  have Hl := Hrel.length_eq
  wp_auto
  wp_apply wp_ctx e ev cx $$ [He]
  · iframe He; ipureintro; exact hcx
  try wp_auto
  wp_apply wp_load_at _ _ rv Hn $$ [Hra]
  · iexact Hra
  try wp_auto
  have hrv : sint.Z rv.len = (s.reads[sint.nat n]!).length := by rw [← Hl, Hil.1]; exact (sint_nat_cast Hil.2).symm
  wp_apply (wp_slice_make3 (V := G.ReadRec) (W64 0) (rv.len + W64 1) ⟨by word, by word⟩) as %o ⟨Ho, Hocap, -⟩
  try wp_auto
  wp_apply wp_slice_append o _ rv items DFrac.discard $$ [Ho Hocap Hitems] as %o1 ⟨Ho1, Hocap1, -⟩
  · iframe Ho Hocap; iexact Hitems
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [Ho1 Hocap1 Hsl1] as %o2 ⟨Ho2, -, -⟩
  · iframe
  try wp_auto
  ihave %Hwf2 := ownSlice_wf $$ Ho2
  imod ownSlice_persist $$ Ho2 with #Ho2
  have hrel2 : List.Forall₂ readRel (List.replicate 0 (zero_val G.ReadRec) ++ items ++ [{ Ctx' := cx, Floor' := g.Chain'.len }])
      (s.reads[sint.nat n]! ++ [{ ctx := cx, floor := s.chain.length }]) := by
    simp only [List.replicate, List.nil_append]
    exact List.Forall₂.append Hrel (List.Forall₂.cons ⟨rfl, Hchl⟩ List.Forall₂.nil)
  ihave #Hq2 : readRecsRO o2 (s.reads[sint.nat n]! ++ [{ ctx := cx, floor := s.chain.length }]) $$ [Ho2]
  · iunfold readRecsRO; iexists _; iframe Ho2; ipureintro; exact hrel2
  ihave %Ho2l := readRecsRO_len _ _ $$ Hq2
  simp only [List.length_append, List.length_singleton] at Ho2l
  have hmr : sint.Z (W64 16) = (maxReads : Int) := rfl
  rw [hmr, Ho2l]
  by_cases hm : (maxReads : Int) < ((s.reads[sint.nat n]!.length + 1 : Nat) : Int)
  · rw [decide_eq_true hm]
    have hgt : (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)]).length > maxReads := by
      simp only [List.length_append, List.length_singleton]; exact_mod_cast hm
    simp only [hgt, ite_true]
    try wp_auto
    have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z o2.len ∧ sint.Z o2.len ≤ sint.Z o2.len := by
      rw [sint_one]; omega
    have hcapT := eq_true (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z o2.len ∧ sint.Z o2.len ≤ sint.Z o2.cap by
      rw [sint_one]; omega)
    rw [ite_eq_left_of_eq_true _ _ hcapT]
    ihave #Hq3 := readRecsRO_subslice o2 _ (W64 1) o2.len hb1 $$ Hq2
    have hsub : subslice (sint.nat (W64 1)) (sint.nat o2.len) (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)]) = List.drop 1 (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)]) := by
      unfold subslice
      have h1 := sint_nat_cast' o2.len
      have : sint.nat o2.len = (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)]).length := by
        rw [List.length_append, List.length_singleton]; omega
      rw [this, List.take_length]; rfl
    ihave #Hq4 : readRecsRO (slice.slice o2 G.ReadRec (W64 1) o2.len) (List.drop 1 (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)])) $$ [Hq3]
    · rw [← hsub]; iexact Hq3
    try wp_auto
    wp_apply wp_clone p s $$ [Hs] as %q Hq
    · iexact Hs
    try wp_auto
    wp_apply wp_setReads g.Reads' s.reads n _ (List.drop 1 (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)])) $$ [HReads Hq4] as %out #Hout
    · iframe HReads Hq4; ipureintro; exact ⟨Hn, by rw [HWf.len_reads]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_reads q s out (s.reads.set (sint.nat n) (List.drop 1 (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)]))) (by rw [List.length_set, HWf.len_reads]) $$ [Hq Hout] as Hq
    · iframe Hq Hout
    try wp_auto
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq
  · rw [decide_eq_false hm]
    have hgt : ¬ (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)]).length > maxReads := by
      simp only [List.length_append, List.length_singleton]; intro h; exact hm (by exact_mod_cast h)
    simp only [hgt, ite_false]
    try wp_auto
    wp_apply wp_clone p s $$ [Hs] as %q Hq
    · iexact Hs
    try wp_auto
    wp_apply wp_setReads g.Reads' s.reads n _ (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)]) $$ [HReads Hq2] as %out #Hout
    · iframe HReads Hq2; ipureintro; exact ⟨Hn, by rw [HWf.len_reads]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_reads q s out (s.reads.set (sint.nat n) (s.reads[sint.nat n]! ++ [({ ctx := cx, floor := s.chain.length } : ReadRec)])) (by rw [List.length_set, HWf.len_reads]) $$ [Hq Hout] as Hq
    · iframe Hq Hout
    try wp_auto
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
