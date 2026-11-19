/-
`fieldpath.EmptyRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EmptyBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EmptyBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.EmptyRec

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
variable [package_sem : fieldpath.Assumptions]

/-- Löb induction over the members' bodies (with `fieldpath.EmptyRec.specI`'s members read back as their
specs). -/
theorem fieldpath.EmptyRec.wp_proof
    (h_Set_Empty_body : fieldpath.Set.Empty.specBody (GF := GF))
    (h_SetNodeMap_Empty_body : fieldpath.SetNodeMap.Empty.specBody (GF := GF)) :
    fieldpath.EmptyRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
