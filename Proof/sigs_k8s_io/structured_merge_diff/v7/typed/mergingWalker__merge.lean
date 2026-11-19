/-
`typed.mergingWalker.merge`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Recursive (`merge` → `handleAtom` → `doList`/`doMap` → `visit*` → `mergeListItem`/`visitMapItem` → `merge`): the link needs a form for a cycle of specs (open question in the report).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__merge
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doMap

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

theorem typed.mergingWalker.merge.wp_proof
    (hSchema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (hdeduceAtom : typed.deduceAtom.spec (GF := GF))
    (hhandleAtom : typed.handleAtom.spec (GF := GF))
    (hAtom_Equals : schema.Atom.Equals.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hValidationErrors_WithLazyPrefix : typed.ValidationErrors.WithLazyPrefix.spec (GF := GF))
    (hmergingWalker_doScalar : typed.mergingWalker.doScalar.spec (GF := GF))
    (hmergingWalker_doList : typed.mergingWalker.doList.spec (GF := GF))
    (hmergingWalker_doMap : typed.mergingWalker.doMap.spec (GF := GF)) :
    typed.mergingWalker.merge.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
