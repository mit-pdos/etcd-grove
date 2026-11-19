/-
`typed.mergingWalker.mergeListItem`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__mergeListItemBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeListItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__prepareDescent

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

theorem typed.mergingWalker.mergeListItem.wp_proofBody
    (h_mergingWalker_finishDescent : typed.mergingWalker.finishDescent.spec (GF := GF))
    (h_mergingWalker_prepareDescent : typed.mergingWalker.prepareDescent.spec (GF := GF)) :
    typed.mergingWalker.mergeListItem.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
