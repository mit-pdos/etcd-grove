/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Majority`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Majority
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.interCount

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Majority.wp_proof (wp_interCount : interCount.spec (GF := GF) (hG := hG)) :
    Majority.spec (GF := GF) (hG := hG) := by
  intro sl xs vl vs
  wp_start as ⟨#Hx, #Hv, %Hb⟩
  ihave #Hv' := Hv
  iunfold strsRO at Hv'
  ihave %Hvl := ownSlice_len $$ Hv'
  wp_auto
  wp_apply wp_interCount sl xs vl vs $$ [Hx Hv] as %w %Hw
  · iframe Hx Hv
  try wp_auto
  have hle : (interCount xs vs : Int) ≤ xs.length := by
    unfold interCount; exact_mod_cast List.length_filter_le _ _
  have hm : decide (sint.Z vl.len < sint.Z (w * W64 2)) = majority xs vs := by
    unfold majority
    have h2 : sint.Z (w * W64 2) = sint.Z w * 2 := by
      have : 0 ≤ sint.Z w := by rw [Hw]; omega
      word
    rw [h2, Hw, show sint.Z vl.len = (vs.length : Int) by rw [Hvl.1]; word]
    simp only [decide_eq_decide, gt_iff_lt]
    omega
  rw [hm]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
