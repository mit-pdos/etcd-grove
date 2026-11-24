/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Min`.
-/
module

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

theorem Min.wp_proof : Min.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; unfold imin; rw [ite_eq_left (by word)]
  · iapply HΦ; ipureintro; unfold imin; rw [ite_eq_right (by word)]

end proof

end AntCheck
end EtcdGrove
end Perennial
