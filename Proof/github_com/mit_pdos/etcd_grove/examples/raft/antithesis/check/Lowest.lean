/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `Lowest` (B 288).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Lowest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Min

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

theorem Lowest.wp_proof (wp_Min : Min.spec (GF := GF) (hG := hG)) :
    Lowest.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start as #_
  wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; ipureintro
    simp [lowest]
  · try wp_auto
    have ha : sint.Z a ≠ 0 := fun h => Hif (by word)
    wp_if_destruct
    · try wp_auto
      iapply HΦ; ipureintro
      simp [lowest, ha]
    · try wp_auto
      have hb : sint.Z b ≠ 0 := fun h => Hif (by word)
      wp_apply wp_Min a b as %w %Hw
      try wp_auto
      iapply HΦ; ipureintro
      simp [lowest, ha, hb, Hw]

end proof

end AntCheck
end EtcdGrove
end Perennial
