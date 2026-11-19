/-
`value.listUnstructured.EqualsUsing`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `listUnstructured__EqualsUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__EqualsUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsingRec

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

theorem value.listUnstructured.EqualsUsing.wp_proof
    (hrec : value.EqualsUsingRec.spec (GF := GF)) :
    value.listUnstructured.EqualsUsing.spec (GF := GF) := hrec.2.2.1

end proof

end smd
end EtcdGrove
end Perennial
