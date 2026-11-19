/-
`typed.handleAtom`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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

theorem typed.handleAtom.wp_proof :
    typed.handleAtom.spec (GF := GF) := fun a A tr T hv Pre Q => by
  wp_start as ⟨#Ha, HP, Hh⟩
  cases A with
  | map fs e rel =>
    icases (isAtomOpt_map_law_holds a fs e rel).1 $$ Ha with ⟨%Hn, #Hm⟩
    ihave %Hm0 := isMapRep_nonnull_law_holds _ _ _ _ $$ Hm
    wp_auto
    simp only [Hm0, decide_false, Bool.not_false, decide_true]
    wp_auto
    unfold atomHandlerOk
    wp_apply Hh $$ [$HP] as %errs HQ
    iapply HΦ $$ HQ
  | scalar s =>
    icases (isAtomOpt_scalar_law_holds a s).1 $$ Ha with ⟨#Hs, %Hn⟩
    ihave %Hs0 := typedPointsto_not_null $$ Hs
    wp_auto
    simp only [Hn.2, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
    wp_auto
    simp only [Hs0, decide_false, Bool.not_false, decide_true]
    wp_auto
    unfold atomHandlerOk
    wp_apply Hh $$ [$HP] as %errs HQ
    iapply HΦ $$ HQ
  | list e rel ks =>
    icases (isAtomOpt_list_law_holds a e rel ks).1 $$ Ha with ⟨%Hn, #Hl⟩
    ihave %Hl0 := isListRep_nonnull_law_holds _ _ _ _ $$ Hl
    wp_auto
    simp only [Hn.2, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
    wp_auto
    simp only [Hn.1, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
    wp_auto
    simp only [Hl0, decide_false, Bool.not_false, decide_true]
    wp_auto
    unfold atomHandlerOk
    wp_apply Hh $$ [$HP] as %errs HQ
    iapply HΦ $$ HQ

end proof

end smd
end EtcdGrove
end Perennial
