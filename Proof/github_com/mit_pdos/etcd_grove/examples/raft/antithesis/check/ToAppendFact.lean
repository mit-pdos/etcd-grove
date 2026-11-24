/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `ToAppendFact` (B 68-71).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ToAppendFact
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__from
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__to
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__logTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__commit

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

theorem ToAppendFact.wp_proof (wp_from : Msg.«from».spec (GF := GF) (hG := hG))
    (wp_to : Msg.to.spec (GF := GF) (hG := hG))
    (wp_term : Msg.term.spec (GF := GF) (hG := hG))
    (wp_index : Msg.index.spec (GF := GF) (hG := hG))
    (wp_logTerm : Msg.logTerm.spec (GF := GF) (hG := hG))
    (wp_entries : Msg.entries.spec (GF := GF) (hG := hG))
    (wp_commit : Msg.commit.spec (GF := GF) (hG := hG)) :
    ToAppendFact.spec (GF := GF) (hG := hG) := by
  intro g m f
  wp_start as ⟨#Hm, %Hf⟩
  unfold toAppendFact at Hf
  cases h1 : m.from_ with
  | error _ => rw [h1] at Hf; cases Hf
  | ok src =>
  cases h2 : m.to_ with
  | error _ => rw [h1, h2] at Hf; cases Hf
  | ok dst =>
  cases h3 : m.term_ with
  | error _ => rw [h1, h2, h3] at Hf; cases Hf
  | ok t =>
  cases h4 : m.index_ with
  | error _ => rw [h1, h2, h3, h4] at Hf; cases Hf
  | ok p =>
  cases h5 : m.logTerm_ with
  | error _ => rw [h1, h2, h3, h4, h5] at Hf; cases Hf
  | ok pt =>
  cases h6 : m.entries_ with
  | error _ => rw [h1, h2, h3, h4, h5, h6] at Hf; cases Hf
  | ok es =>
  cases h7 : m.commit_ with
  | error _ => rw [h1, h2, h3, h4, h5, h6, h7] at Hf; cases Hf
  | ok c =>
  rw [h1, h2, h3, h4, h5, h6, h7] at Hf
  cases Hf
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_from_unfold.method_unfold]
  try wp_auto
  wp_apply wp_from g m src $$ [Hm]
  · iframe Hm; ipureintro; exact h1
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_to_unfold.method_unfold]
  try wp_auto
  wp_apply wp_to g m dst $$ [Hm]
  · iframe Hm; ipureintro; exact h2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_term_unfold.method_unfold]
  try wp_auto
  wp_apply wp_term g m t $$ [Hm] as %ut %Hut
  · iframe Hm; ipureintro; exact h3
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_index_unfold.method_unfold]
  try wp_auto
  wp_apply wp_index g m p $$ [Hm] as %up %Hup
  · iframe Hm; ipureintro; exact h4
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_logTerm_unfold.method_unfold]
  try wp_auto
  wp_apply wp_logTerm g m pt $$ [Hm] as %ul %Hul
  · iframe Hm; ipureintro; exact h5
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_entries_unfold.method_unfold]
  try wp_auto
  wp_apply wp_entries g m es $$ [Hm] as %ue #Hue
  · iframe Hm; ipureintro; exact h6
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_commit_unfold.method_unfold]
  try wp_auto
  wp_apply wp_commit g m c $$ [Hm] as %uc %Huc
  · iframe Hm; ipureintro; exact h7
  try wp_auto
  iapply HΦ
  iunfold appendFactRO
  iframe Hue
  ipureintro
  exact ⟨rfl, rfl, Hut, Hup, Hul, Huc⟩

end proof

end AntCheck
end EtcdGrove
end Perennial
