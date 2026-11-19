/-
`typed.removingWalkerRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchemaBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMapBody
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

/-- Löb induction over the members' bodies (with `typed.removingWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.removingWalkerRec.wp_proof
    (h_removeItemsWithSchema_body : typed.removeItemsWithSchema.specBody (GF := GF))
    (h_removingWalker_doList_body : typed.removingWalker.doList.specBody (GF := GF))
    (h_removingWalker_doMap_body : typed.removingWalker.doMap.specBody (GF := GF)) :
    typed.removingWalkerRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
