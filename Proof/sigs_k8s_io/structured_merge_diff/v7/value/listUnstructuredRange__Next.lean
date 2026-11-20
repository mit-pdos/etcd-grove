/-
`value.listUnstructuredRange.Next`: proved (Prove step, notes/smd-plan.md), over the premise
`n < vs.length` (post-freeze change B2c): the cursor's increment then stays below `2^63`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Next
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

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

theorem value.listUnstructuredRange.Next.wp_proof :
    value.listUnstructuredRange.Next.spec (GF := GF) := fun q vs n => by
  wp_start as ⟨Hr, %Hnlt⟩
  iunfold ownRange at Hr
  icases Hr with (⟨%q', %h⟩ | ⟨%q', %sl, %w, %iw, %h, Hq, #Hli, Hw⟩)
  · exfalso; simp at h; exact emptyRange_ne_listUnstructuredRange h.1.1.symm
  obtain ⟨hq, rfl⟩ := h
  simp [intoVal_eq_iff] at hq
  subst hq
  ihave #Hl := isListV_intro $$ Hli
  icases isListV_val $$ Hl with ⟨%xs, #Hs, HL⟩
  ihave %Hlen := isIfaceL_length $$ HL
  ihave %Hsl := ownSlice_len $$ Hs
  wp_auto
  by_cases hov : iw.toInt + 1 < 2 ^ 63
  · iapply HΦ
    isplitl
    · iapply ownRange_intro q sl w (iw + W64 1) vs _ (by word)
      iframe
      iexact Hli
    · ipureintro
      simp only [decide_eq_decide]
      constructor <;> intro h <;> word
  · exfalso
    have := BitVec.toInt_lt (x := sl.len)
    simp only [sint.nat, sint.Z] at Hsl
    omega

end proof

end smd
end EtcdGrove
end Perennial
