/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `oneMoreMessage`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.oneMoreMessage
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

/-- `c2 == c1 + 1` on counts (non-negative, below `2^63`): `+ 1` may wrap, never onto a count. -/
theorem count_succ_iff (c1 c2 : w64) (a b : Nat) (h1 : sint.Z c1 = (b : Int)) (h2 : sint.Z c2 = (a : Int)) :
    c2 = c1 + W64 1 ↔ a = b + 1 := by
  constructor
  · intro e
    subst e
    by_cases hb : (b : Int) + 1 < 2 ^ 63
    · have : sint.Z (c1 + W64 1) = (b : Int) + 1 := by rw [← h1] at hb ⊢; word
      omega
    · have : sint.Z (c1 + W64 1) < 0 := by rw [← h1] at hb; word
      omega
  · intro e
    have hlt : (a : Int) < 2 ^ 63 := by rw [← h2]; word
    have : sint.Z (c1 + W64 1) = (b : Int) + 1 := by
      have : (b : Int) + 1 < 2 ^ 63 := by omega
      rw [← h1] at this ⊢; word
    exact (sint_eq_iff _ _ _ _ h2 this).2 (by omega)

theorem oneMoreMessage.wp_proof (wp_Count : Bag.Count.spec (GF := GF) (hG := hG)) :
    oneMoreMessage.spec (GF := GF) (hG := hG) := by
  intro p s p2 s2 q m
  wp_start as ⟨#Hs, #Hs2, #Hmsg⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = oneMoreMessage s s2 m⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  ihave #Hs0 := Hs
  iunfold stateRO at Hs0
  icases Hs0 with ⟨%g, %sm, #Hp, -, -, -, -, -, -, #Hpm, -⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨-, -, -, #PM, -⟩
  ihave #Hs20 := Hs2
  iunfold stateRO at Hs20
  icases Hs20 with ⟨%g2, %sm2, #Hp2, -, -, -, -, -, -, #Hpm2, -⟩
  icases typedPointsto_split _ _ _ $$ Hp2 with Hpf2
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf2 with ⟨-, -, -, #PM2, -⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Count_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Count g.PendingMessages' s.pendingMessages q m $$ [Hpm Hmsg] as %c1 %Hc1
  · iframe Hpm Hmsg
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Count_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Count g2.PendingMessages' s2.pendingMessages q m $$ [Hpm2 Hmsg] as %c2 %Hc2
  · iframe Hpm2 Hmsg
  try wp_auto
  rw [sint_decide_nat Hc1 (show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl)]
  by_cases hb0 : s.pendingMessages.count m = 0
  · rw [decide_eq_true hb0]
    wp_auto
    rw [sint_decide_nat Hc2 (show sint.Z (W64 1) = ((1 : Nat) : Int) from rfl)]
    by_cases ha1 : s2.pendingMessages.count m = 1
    · rw [decide_eq_true ha1]
      wp_auto
      iapply HΦ'; ipureintro; simp [oneMoreMessage, hb0, ha1]
    · rw [decide_eq_false ha1]
      wp_auto
      rw [decide_eq_false (show ¬ (sint.Z (W64 0) < sint.Z c1) by rw [Hc1, hb0]; word)]
      wp_auto
      iapply HΦ'; ipureintro; simp [oneMoreMessage, hb0, ha1]
  · rw [decide_eq_false hb0]
    wp_auto
    have hpos : sint.Z (W64 0) < sint.Z c1 := by
      have : (0 : Int) < (s.pendingMessages.count m : Nat) := by omega
      rw [Hc1]; word
    rw [decide_eq_true hpos]
    wp_auto
    rw [show decide (c2 = c1 + W64 1) = decide (s2.pendingMessages.count m = s.pendingMessages.count m + 1) from
      decide_eq_decide.2 (count_succ_iff c1 c2 _ _ Hc1 Hc2)]
    iapply HΦ'; ipureintro
    have : 0 < s.pendingMessages.count m := by omega
    simp only [oneMoreMessage]
    rw [Bool.eq_iff_iff]; simp; omega

end proof

end Etcdraft
end EtcdGrove
end Perennial
