/-
`typed.TypedValue.ToFieldSet`: proved (Prove phase, 2026-11-20): a fresh walker (empty set) walks the
conforming value with no errors; its set, `fieldSet`, is returned before the deferred `finished`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__toFieldSetWalker
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__finished
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSet
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
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

theorem typed.TypedValue.ToFieldSet.wp_proof
    (h_TypedValue_toFieldSetWalker : typed.TypedValue.toFieldSetWalker.spec (GF := GF))
    (h_toFieldSetWalker_finished : typed.toFieldSetWalker.finished.spec (GF := GF))
    (h_toFieldSetWalker_toFieldSet : typed.toFieldSetWalker.toFieldSet.spec (GF := GF)) :
    typed.TypedValue.ToFieldSet.spec (GF := GF) :=
    fun tv sc S t x => by
  wp_start as ⟨Htv, %Hsz⟩
  ihave #Htv := isTVv_persistent_law_holds tv sc S t x $$ Htv
  wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply h_TypedValue_toFieldSetWalker tv sc S t x $$ [] as %w ⟨%s, %a, Hown⟩
  · iframe #
  try wp_auto
  unfold isTVv
  icases Htv with ⟨%Hsc, #Hv, -, -, %Hc⟩
  have hu : (PathSet.empty.union (fieldsAt S t [] x)) = fieldsAt S t [] x :=
    LawB.fset_empty_union _
  wp_apply h_toFieldSetWalker_toFieldSet w sc S ⟨tv.value', t, [], a⟩ s PathSet.empty DFrac.discard x
    $$ [Hown] as %errs ⟨Herrs, -, Hown⟩
  · iframe; iframe #
    ipureintro
    refine ⟨Hc.2, ?_⟩
    simp only
    rw [hu]
    exact fieldSet_card_law_holds S t [] x Hsz
  ihave %Hlen := noErrs_len $$ Herrs
  rw [hu]
  iunfold twOwn at Hown
  icases Hown with ⟨%ps, %sp, Hcore, -, Hsp, -, Hs⟩
  iunfold twCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc', %HWF⟩
  rw [show decide (errs.len = W64 0) = true by simp; word]
  wp_auto
  wp_apply h_toFieldSetWalker_finished w sc S ⟨tv.value', t, [], a⟩ ps s sp a $$ [Hw Hsp]
  · iframe Hsp
    unfold twCore
    iexists tr
    iframe
    iframe #
    ipureintro; exact HWF
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end smd
end EtcdGrove
end Perennial
