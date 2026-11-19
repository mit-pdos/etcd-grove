/-
`typed.compareWalker.visitMapItem`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__visitMapItemBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__prepareDescent

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

theorem typed.compareWalker.visitMapItem.wp_proofBody
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_compareWalker_finishDescent : typed.compareWalker.finishDescent.spec (GF := GF))
    (h_compareWalker_prepareDescent : typed.compareWalker.prepareDescent.spec (GF := GF)) :
    typed.compareWalker.visitMapItem.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
