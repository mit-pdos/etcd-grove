/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `Comparable` (B 130).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Comparable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsPrefix
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

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

theorem Comparable.wp_proof (wp_IsPrefix : IsPrefix.spec (GF := GF) (hG := hG)) :
    Comparable.spec (GF := GF) (hG := hG) := by
  intro al a bl b r
  wp_start as ⟨#Ha, #Hb, %Hr⟩
  unfold comparable at Hr
  obtain ⟨x, hx, ht, hf⟩ := orM_ok Hr
  wp_auto
  wp_apply wp_IsPrefix al a bl b x $$ [Ha Hb]
  · iframe Ha Hb; ipureintro; exact hx
  cases x
  · try wp_auto
    wp_apply wp_IsPrefix bl b al a r $$ [Ha Hb]
    · iframe Ha Hb; ipureintro; exact hf rfl
    try wp_auto
    iapply HΦ; ipureintro; trivial
  · try wp_auto
    rw [ht rfl]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
