/-
`typed.toFieldSetWalker.visitListItems`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__finishDescent

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

theorem typed.toFieldSetWalker.visitListItems.wp_proof
    (hMakePathElementSet : fieldpath.MakePathElementSet.spec (GF := GF))
    (hlistItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (hPathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (hPathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (hSet_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (htoFieldSetWalker_prepareDescent : typed.toFieldSetWalker.prepareDescent.spec (GF := GF))
    (htoFieldSetWalker_toFieldSet : typed.toFieldSetWalker.toFieldSet.spec (GF := GF))
    (htoFieldSetWalker_finishDescent : typed.toFieldSetWalker.finishDescent.spec (GF := GF)) :
    typed.toFieldSetWalker.visitListItems.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
