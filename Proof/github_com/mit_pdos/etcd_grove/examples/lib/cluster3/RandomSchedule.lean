/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/cluster3/RandomSchedule.lean`: the loop keeps
`sched` a slice of `i` steps (for `0 ≤ i ≤ n`), one appended per iteration (`below`'s moduli are
constants, not zero). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.RandomSchedule
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.below

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

theorem RandomSchedule.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    RandomSchedule.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as #Hpkg
  (try wp_auto)
  ihave IH : iprop(∃ (i : w64) (sv : GoSlice)
      (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step),
      "i" ∷ i_ptr ↦ i ∗ "sched" ∷ sched_ptr ↦ sv ∗
      "Hsv" ∷ sv ↦* steps ∗ "Hsvc" ∷ ownSliceCap github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step
        sv (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ (0 ≤ sint.Z n → sint.Z i ≤ sint.Z n) ∧
        steps.length = sint.nat i⌝) $$ [i sched]
  · iexists W64 0, slice.nil, []
    iframe i sched
    simp only [named]
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; refine ⟨by word, fun h => by word, by simp; word⟩
  wp_for IH
  wp_if_destruct
  · (try wp_auto)
    wp_apply wp_below (W64 1000000000) (by decide) as %d -
    (try wp_auto)
    wp_apply wp_below (W64 5) (by decide) as %kd -
    (try wp_auto)
    wp_apply wp_below (W64 3) (by decide) as %a -
    (try wp_auto)
    wp_apply wp_below (W64 3) (by decide) as %b -
    (try wp_auto)
    wp_apply wp_slice_literal (V := github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsv $Hsvc $Hsl1] as %sv' ⟨Hsv, Hsvc, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists i + W64 1, sv', _
    iframe
    ipureintro
    refine ⟨by word, fun _ => by word, ?_⟩
    simp only [List.length_append, List.length_singleton]
    rw [Hi.2.2]; word
  (try wp_auto)
  iapply HΦ
  iexists steps
  iframe
  ipureintro
  intro hn
  rw [Hi.2.2]
  have := Hi.2.1 hn
  word

end proof

end cluster3
end EtcdGrove
end Perennial
