/-
`value.listUnstructured.EqualsUsing_ptr`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `listUnstructured__EqualsUsing_ptrBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__EqualsUsing_ptrBody
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

theorem value.listUnstructured.EqualsUsing_ptr.wp_proofBody :
    value.listUnstructured.EqualsUsing_ptr.specBody (GF := GF) := by
  iintro #IH
  iunfold value.listUnstructured.EqualsUsing_ptr.specI
  iintro %p %vs %ws %al %o
  wp_start as ⟨Hl, Ho, Ha⟩
  icases isListV_ptr $$ Hl with ⟨%sl, #Hp, Hl⟩
  iunfold value.EqualsUsingRec.specI at IH
  icases IH with ⟨-, -, #HLE, -, -⟩
  iunfold value.listUnstructured.EqualsUsing.specI at HLE
  wp_auto
  wp_apply HLE $$ %sl %vs %ws %al %o [Hl Ho Ha] as %b Hb
  · iframe
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
