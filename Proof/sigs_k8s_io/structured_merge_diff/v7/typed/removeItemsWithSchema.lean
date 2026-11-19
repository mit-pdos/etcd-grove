/-
`typed.removeItemsWithSchema`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removeItemsWithSchemaBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalkerRec

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

theorem typed.removeItemsWithSchema.wp_proof
    (hrec : typed.removingWalkerRec.spec (GF := GF)) :
    typed.removeItemsWithSchema.spec (GF := GF) := hrec.1

end proof

end smd
end EtcdGrove
end Perennial
