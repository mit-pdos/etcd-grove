/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `oneLessMessage`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.oneLessMessage
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Count

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem oneLessMessage.wp_proof (wp_Count : Bag.Count.spec (GF := GF) (hG := hG)) :
    oneLessMessage.spec (GF := GF) (hG := hG) := by
  intro p s p2 s2 q m
  wp_start as ⟨#Hs, #Hs2, #Hmsg⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = oneLessMessage s s2 m⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  ihave #Hs0 := Hs
  iunfold stateRO at Hs0
  icases Hs0 with ⟨%g, %sm, #Hp, -, -, -, -, -, #Hm, -, -⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨-, -, #PM, -⟩
  ihave #Hs20 := Hs2
  iunfold stateRO at Hs20
  icases Hs20 with ⟨%g2, %sm2, #Hp2, -, -, -, -, -, #Hm2, -, -⟩
  icases typedPointsto_split _ _ _ $$ Hp2 with Hpf2
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf2 with ⟨-, -, #PM2, -⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Count_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Count g.Messages' s.messages q m $$ [Hm Hmsg] as %c1 %Hc1
  · iframe Hm Hmsg
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Count_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Count g2.Messages' s2.messages q m $$ [Hm2 Hmsg] as %c2 %Hc2
  · iframe Hm2 Hmsg
  try wp_auto
  rw [sint_decide_nat Hc1 (show sint.Z (W64 1) = ((1 : Nat) : Int) from rfl)]
  by_cases hb1 : s.messages.count m = 1
  · rw [decide_eq_true hb1]
    wp_auto
    rw [sint_decide_nat Hc2 (show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl)]
    by_cases ha0 : s2.messages.count m = 0
    · rw [decide_eq_true ha0]
      wp_auto
      iapply HΦ'; ipureintro; simp [oneLessMessage, hb1, ha0]
    · rw [decide_eq_false ha0]
      wp_auto
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z c1 by rw [Hc1, hb1]; word)]
      wp_auto
      have hs : sint.Z (c1 - W64 1) = ((0 : Nat) : Int) := by rw [hb1] at Hc1; word
      rw [sint_decide_nat Hc2 hs]
      iapply HΦ'; ipureintro; simp [oneLessMessage, hb1, ha0]
  · rw [decide_eq_false hb1]
    wp_auto
    by_cases hb0 : s.messages.count m = 0
    · rw [decide_eq_false (show ¬ (sint.Z (W64 0) < sint.Z c1) by rw [Hc1, hb0]; word)]
      wp_auto
      iapply HΦ'; ipureintro; simp [oneLessMessage, hb0]
    have hpos : sint.Z (W64 0) < sint.Z c1 := by
      have : (0 : Int) < (s.messages.count m : Nat) := by omega
      rw [Hc1]; word
    rw [decide_eq_true hpos]
    wp_auto
    have hs : sint.Z (c1 - W64 1) = (s.messages.count m : Int) - 1 := by
      have : (0 : Int) < sint.Z c1 := by omega
      rw [← Hc1]; word
    rw [sint_decide Hc2 hs]
    have e : ((s2.messages.count m : Int) = (s.messages.count m : Int) - 1) ↔
        (s2.messages.count m + 1 = s.messages.count m) := by omega
    iapply HΦ'; ipureintro
    have : 0 < s.messages.count m := by omega
    simp only [oneLessMessage]
    rw [Bool.eq_iff_iff]; simp; omega

end proof

end Etcdraft
end EtcdGrove
end Perennial
