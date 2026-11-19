/-
`typed.mergingWalker.indexListPathElements`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__indexListPathElements
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementValueMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__String
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface

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

theorem typed.mergingWalker.indexListPathElements.wp_proof
    (hlistItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (hMakePathElementValueMap : fieldpath.MakePathElementValueMap.spec (GF := GF))
    (hPathElementValueMap_Get : fieldpath.PathElementValueMap.Get.spec (GF := GF))
    (hPathElementValueMap_Insert : fieldpath.PathElementValueMap.Insert.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hPathElement_String : fieldpath.PathElement.String.spec (GF := GF))
    (hNewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    typed.mergingWalker.indexListPathElements.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
