/-
`typed.mergingWalker.doLeaf`: proved (Prove phase, 2026-11-19): in a leaf already, nothing; else
mark the walker in a leaf and run `ruleKeepRHS` (`ruleKeepRHSOk`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doLeaf
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers

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
variable [package_sem : typed.Assumptions]

theorem typed.mergingWalker.doLeaf.wp_proof :
    typed.mergingWalker.doLeaf.spec (GF := GF) := fun w sc S st dql dqr l r => by
  wp_start as ⟨Hown, Hl, Hr, %Hlr⟩
  iNamed Hown
  icases Hown with ⟨Hcore, Hps, Hsp, Ha⟩
  iNamed Hcore
  icases Hcore with ⟨Hw, #Htr, #Hsc, %HWF, #Hrule, #Ho⟩
  wp_auto
  cases Hif : st.inLeaf
  rotate_left
  · wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    unfold mwOwn mwCore; rw [Hif]
    iexists ps, sp, a
    iframe
    isplitr; iexact Htr
    isplitr; iexact Hsc
    isplitr; ipureintro; exact HWF
    isplitr; iexact Hrule
    iexact Ho
  · wp_auto
    ihave Hc := ruleKeepRHSOk_call rule w _ dql dqr l r $$ Hrule
    wp_apply Hc $$ [Hw Hl Hr] as ⟨%o', Hw, #Ho', Hl, Hr⟩
    · iframe; ipureintro; exact Hlr
    simp only
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    unfold mwOwn mwCore
    iexists ps, sp, a
    iframe
    simp only
    isplitr; iexact Htr
    isplitr; iexact Hsc
    isplitr; ipureintro; exact HWF
    isplitr; iexact Hrule
    iexact Ho'

end proof

end smd
end EtcdGrove
end Perennial
