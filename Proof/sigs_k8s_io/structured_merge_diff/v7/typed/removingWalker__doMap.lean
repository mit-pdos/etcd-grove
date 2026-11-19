/-
`typed.removingWalker.doMap`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removingWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMap
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

theorem typed.removingWalker.doMap.wp_proof
    (hrec : typed.removingWalkerRec.spec (GF := GF)) :
    typed.removingWalker.doMap.spec (GF := GF) := hrec.2.2

end proof

end smd
end EtcdGrove
end Perennial
