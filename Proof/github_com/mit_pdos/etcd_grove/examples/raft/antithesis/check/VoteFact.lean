/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `VoteFact` (B 63-65).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.VoteFact
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__from
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__logTerm

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

theorem VoteFact.wp_proof (wp_from : Msg.«from».spec (GF := GF) (hG := hG))
    (wp_term : Msg.term.spec (GF := GF) (hG := hG))
    (wp_index : Msg.index.spec (GF := GF) (hG := hG))
    (wp_logTerm : Msg.logTerm.spec (GF := GF) (hG := hG)) :
    VoteFact.spec (GF := GF) (hG := hG) := by
  intro g m f
  wp_start as ⟨#Hm, %Hf⟩
  unfold voteFact at Hf
  cases h1 : m.from_ with
  | error _ => rw [h1] at Hf; cases Hf
  | ok src =>
  cases h2 : m.term_ with
  | error _ => rw [h1, h2] at Hf; cases Hf
  | ok t =>
  cases h3 : m.index_ with
  | error _ => rw [h1, h2, h3] at Hf; cases Hf
  | ok k =>
  cases h4 : m.logTerm_ with
  | error _ => rw [h1, h2, h3, h4] at Hf; cases Hf
  | ok lt =>
  rw [h1, h2, h3, h4] at Hf
  cases Hf
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'from.method_unfold]
  try wp_auto
  wp_apply wp_from g m src $$ [Hm]
  · iframe Hm; ipureintro; exact h1
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
  try wp_auto
  wp_apply wp_term g m t $$ [Hm] as %ut %Hut
  · iframe Hm; ipureintro; exact h2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
  try wp_auto
  wp_apply wp_index g m k $$ [Hm] as %uk %Huk
  · iframe Hm; ipureintro; exact h3
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'logTerm.method_unfold]
  try wp_auto
  wp_apply wp_logTerm g m lt $$ [Hm] as %ul %Hul
  · iframe Hm; ipureintro; exact h4
  try wp_auto
  iapply HΦ
  ipureintro
  exact ⟨rfl, rfl, rfl, Hut, Huk, Hul, rfl⟩

end proof

end AntCheck
end EtcdGrove
end Perennial
