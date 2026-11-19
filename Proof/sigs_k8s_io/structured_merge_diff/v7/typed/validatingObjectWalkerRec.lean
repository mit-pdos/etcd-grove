/-
`typed.validatingObjectWalkerRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validateBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitMapItemsBody
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

/-- Löb induction over the members' bodies (with `typed.validatingObjectWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.validatingObjectWalkerRec.wp_proof
    (h_validatingObjectWalker_doList_body : typed.validatingObjectWalker.doList.specBody (GF := GF))
    (h_validatingObjectWalker_doMap_body : typed.validatingObjectWalker.doMap.specBody (GF := GF))
    (h_validatingObjectWalker_validate_body : typed.validatingObjectWalker.validate.specBody (GF := GF))
    (h_validatingObjectWalker_visitListItems_body : typed.validatingObjectWalker.visitListItems.specBody (GF := GF))
    (h_validatingObjectWalker_visitMapItems_body : typed.validatingObjectWalker.visitMapItems.specBody (GF := GF)) :
    typed.validatingObjectWalkerRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
