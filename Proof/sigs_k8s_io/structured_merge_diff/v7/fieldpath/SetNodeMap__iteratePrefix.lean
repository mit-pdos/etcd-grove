/-
`fieldpath.SetNodeMap.iteratePrefix`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__iteratePrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__iteratePrefix

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

theorem fieldpath.SetNodeMap.iteratePrefix.wp_proof
    (wp_Set_iteratePrefix : fieldpath.Set.iteratePrefix.spec (GF := GF)) :
    fieldpath.SetNodeMap.iteratePrefix.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
