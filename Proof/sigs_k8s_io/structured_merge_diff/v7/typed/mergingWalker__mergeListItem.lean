/-
`typed.mergingWalker.mergeListItem`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__mergeListItemBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeListItem
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalkerRec

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

theorem typed.mergingWalker.mergeListItem.wp_proof
    (hrec : typed.mergingWalkerRec.spec (GF := GF)) :
    typed.mergingWalker.mergeListItem.spec (GF := GF) := hrec.2.2.2.1

end proof

end smd
end EtcdGrove
end Perennial
