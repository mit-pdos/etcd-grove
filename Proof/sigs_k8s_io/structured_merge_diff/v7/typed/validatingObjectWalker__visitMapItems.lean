/-
`typed.validatingObjectWalker.visitMapItems`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__visitMapItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitMapItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalkerRec

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

theorem typed.validatingObjectWalker.visitMapItems.wp_proof
    (hrec : typed.validatingObjectWalkerRec.spec (GF := GF)) :
    typed.validatingObjectWalker.visitMapItems.spec (GF := GF) := hrec.2.2.2.2

end proof

end smd
end EtcdGrove
end Perennial
