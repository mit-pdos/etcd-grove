/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.VoteOf` (B 99).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__VoteOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__BootTerm

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

theorem State.VoteOf.wp_proof (wp_BootTerm : State.BootTerm.spec (GF := GF) (hG := hG)) :
    State.VoteOf.spec (GF := GF) (hG := hG) := by
  intro p s vt vf t
  wp_start as #Hs
  wp_auto
  wp_if_destruct
  · subst Hif
    wp_apply wp_BootTerm p s $$ [Hs] as %bt %Hbt
    · iexact Hs
    try wp_auto
    wp_if_destruct
    · try wp_auto
      have : s.voteOf (sint.Z vt) vf (sint.Z vt) = vf := by
        unfold State.voteOf; simp; omega
      rw [this]; iapply HΦ; ipureintro; trivial
    · try wp_auto
      have : s.voteOf (sint.Z vt) vf (sint.Z vt) = [] := by
        unfold State.voteOf; simp; omega
      rw [this]; iapply HΦ; ipureintro; trivial
  · try wp_auto
    have : s.voteOf (sint.Z vt) vf (sint.Z t) = [] := by
      unfold State.voteOf; simp; intro h; exact absurd (by word) Hif
    rw [this]; iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
