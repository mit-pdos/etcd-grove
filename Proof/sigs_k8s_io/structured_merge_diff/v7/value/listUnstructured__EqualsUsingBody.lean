/-
`value.listUnstructured.EqualsUsing`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `listUnstructured__EqualsUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__EqualsUsingBody
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsRec

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

theorem value.listUnstructured.EqualsUsing.wp_proofBody :
    value.listUnstructured.EqualsUsing.specBody (GF := GF) := by
  iintro #IH
  iunfold value.listUnstructured.EqualsUsing.specI
  iintro %l %vs %ws %al %o
  wp_start as ⟨#Hl, Ho, Ha⟩
  iunfold value.EqualsUsingRec.specI at IH
  icases IH with ⟨-, #HLE, -, -, -⟩
  iunfold value.ListEqualsUsing.specI at HLE
  wp_auto
  ipersist l
  ihave #Hlp := isListV_ptr_intro l_ptr l vs $$ [l Hl]
  · isplitr
    · iexact l
    · iexact Hl
  wp_apply HLE $$ %al %_ %o %vs %ws [Ha Ho] as %b Hb
  · iframe; iexact Hlp
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
