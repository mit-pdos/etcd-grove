/-
`typed.validatingObjectWalker.visitListItems`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__String
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finishDescent

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

theorem typed.validatingObjectWalker.visitListItems.wp_proof
    (hMakePathElementSet : fieldpath.MakePathElementSet.spec (GF := GF))
    (hlistItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (hPathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (hPathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hPathElement_String : fieldpath.PathElement.String.spec (GF := GF))
    (hvalidatingObjectWalker_prepareDescent : typed.validatingObjectWalker.prepareDescent.spec (GF := GF))
    (hvalidatingObjectWalker_validate : typed.validatingObjectWalker.validate.spec (GF := GF))
    (hvalidatingObjectWalker_finishDescent : typed.validatingObjectWalker.finishDescent.spec (GF := GF)) :
    typed.validatingObjectWalker.visitListItems.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
