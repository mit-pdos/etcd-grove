/-
`value.IntCompare`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.IntCompare
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.IntCompare.wp_proof :
    value.IntCompare.spec (GF := GF) := fun a b => by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_end; ipureintro
    have : BitVec.toInt a > BitVec.toInt b := by word
    simp [intCompare, this]
  wp_if_destruct
  · wp_end; ipureintro
    have : ¬ BitVec.toInt a > BitVec.toInt b := by word
    have : BitVec.toInt a ≠ BitVec.toInt b := by word
    simp [intCompare, *]
  · wp_end; ipureintro
    have : ¬ BitVec.toInt a > BitVec.toInt b := by word
    have : BitVec.toInt a = BitVec.toInt b := by word
    simp [intCompare, *]

end proof

end smd
end EtcdGrove
end Perennial
