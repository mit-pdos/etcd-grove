/-
`merge.Conflict.Equals`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `fieldpath.Path.Equals`.

Lean-first (2026-11-19).
-/
module

import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Conflict__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Path__Equals

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
variable [package_sem : merge.Assumptions]

theorem merge.Conflict.Equals.wp_proof
    (h_Path_Equals : fieldpath.Path.Equals.spec (GF := GF)) :
    merge.Conflict.Equals.spec (GF := GF) := fun c c2 a b => by
  wp_start as ⟨Hc, Hc2⟩
  unfold isConflict
  icases Hc with ⟨%hm, Hp⟩
  icases Hc2 with ⟨%hm2, Hp2⟩
  ihave Hp := (isPath_isPathF_law_holds _ _).1 $$ Hp
  ihave Hp2 := (isPath_isPathF_law_holds _ _).1 $$ Hp2
  wp_auto
  by_cases hmm : c.Manager' = c2.Manager'
  · simp only [hmm, decide_true, Bool.not_true]
    iStructNamed c
    wp_auto
    wp_apply (h_Path_Equals c.Path' c2.Path' _ _ a.2 b.2) $$ [Hp Hp2] as %r ⟨-, -, %hr⟩
    · iframe Hp Hp2
    wp_auto
    iapply HΦ
    ipureintro
    rw [hr]
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only at hm hm2 ⊢
    have : a1 = b1 := hm ▸ hm2 ▸ hmm
    subst this
    simp
  · simp only [hmm, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ
    ipureintro
    constructor
    · intro h; cases h
    · intro h; subst h; exact absurd (hm.trans hm2.symm) hmm

end proof

end smd
end EtcdGrove
end Perennial
