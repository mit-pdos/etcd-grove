/-
`typed.removingWalker.doList`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePath
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchema

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

theorem typed.removingWalker.doList.wp_proof
    (hlistItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (hMakePath : fieldpath.MakePath.spec (GF := GF))
    (hSet_Has : fieldpath.Set.Has.spec (GF := GF))
    (hSet_WithPrefix : fieldpath.Set.WithPrefix.spec (GF := GF))
    (hSet_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (hremoveItemsWithSchema : typed.removeItemsWithSchema.spec (GF := GF)) :
    typed.removingWalker.doList.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
