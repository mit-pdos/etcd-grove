/-
Lean-first (no Rocq counterpart).

The proof of `inputEqual`: Go's `==` on the struct.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.inputEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem Input_eq_iff (a b : Input) : a = b ↔
    a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val' ∧ a.NCmps' = b.NCmps' ∧
    a.Cmp0'.Kind' = b.Cmp0'.Kind' ∧ a.Cmp0'.Key' = b.Cmp0'.Key' ∧ a.Cmp0'.Val' = b.Cmp0'.Val' ∧
    a.Cmp0'.Num' = b.Cmp0'.Num' ∧ a.NThen' = b.NThen' ∧
    a.Then0'.Kind' = b.Then0'.Kind' ∧ a.Then0'.Key' = b.Then0'.Key' ∧ a.Then0'.Val' = b.Then0'.Val' ∧
    a.Then1'.Kind' = b.Then1'.Kind' ∧ a.Then1'.Key' = b.Then1'.Key' ∧ a.Then1'.Val' = b.Then1'.Val' ∧
    a.Then2'.Kind' = b.Then2'.Kind' ∧ a.Then2'.Key' = b.Then2'.Key' ∧ a.Then2'.Val' = b.Then2'.Val' ∧
    a.NElse' = b.NElse' ∧
    a.Else0'.Kind' = b.Else0'.Kind' ∧ a.Else0'.Key' = b.Else0'.Key' ∧ a.Else0'.Val' = b.Else0'.Val' := by
  obtain ⟨_, _, _, _, ⟨_, _, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩⟩ := a
  obtain ⟨_, _, _, _, ⟨_, _, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩⟩ := b
  simp [and_assoc]

theorem inputEqual.wp_proof : inputEqual.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals first
    | (rw [decide_eq_false (fun h => by subst h; simp_all)]; iapply HΦ; itrivial)
    | (rw [decide_eq_true (by rw [Input_eq_iff]; and_intros <;> assumption)]
       iapply HΦ; itrivial)

end proof

end linkvtxn
end EtcdGrove
end Perennial
