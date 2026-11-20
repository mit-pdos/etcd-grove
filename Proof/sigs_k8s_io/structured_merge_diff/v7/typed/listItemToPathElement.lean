/-
`typed.listItemToPathElement`: an associative list with keys: `keyedAssociativeListItemToPathElement`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.keyedAssociativeListItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.setItemToPathElement
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

theorem typed.listItemToPathElement.wp_proof
    (h_keyedAssociativeListItemToPathElement : typed.keyedAssociativeListItemToPathElement.spec (GF := GF))
    (h_setItemToPathElement : typed.setItemToPathElement.spec (GF := GF)) :
    typed.listItemToPathElement.spec (GF := GF) :=
    fun a sc S lp e ks fs el r child dq x tn => by
  wp_start as ⟨Ha, #Hsc, #Hl, Hv, %Hpre⟩
  obtain ⟨Hwf, Hne, Hfe, Hft, Hc, Hk⟩ := Hpre
  icases isListRep_elim_law_holds lp e .associative ks $$ Hl with ⟨%lv, %ksl, #Hlv, %Hlv', #Hks, -⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  wp_auto
  have hg : decide (ElemRel.associative.goName = go!"associative") = true := by decide
  rw [Hlv'.1, hg]
  wp_auto
  have hpos : decide (sint.Z (W64 0) < sint.Z lv.Keys'.len) = true := by
    have h0 : sint.Z (W64 0) = 0 := rfl
    have : ks.length ≠ 0 := by simpa using Hne
    have h1 := Hkl.1
    rw [← Hlv'.2] at h1
    simp only [decide_eq_true_eq]; word
  rw [hpos]
  wp_auto
  wp_apply h_keyedAssociativeListItemToPathElement a sc S lp e .associative ks fs el r child dq x tn
    $$ [Ha Hv] as %pe %err Hpost
  · iframe; iframe #; ipureintro; exact ⟨Hwf, Hne, Hfe, Hft, Hc, Hk⟩
  try wp_auto
  iapply HΦ
  iexact Hpost

end proof

end smd
end EtcdGrove
end Perennial
