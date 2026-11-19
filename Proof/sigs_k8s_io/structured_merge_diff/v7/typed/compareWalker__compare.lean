/-
`typed.compareWalker.compare`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Recursive (`compare` → `handleAtom` → `doList`/`doMap` → `visit*` → `compareListItem`/`visitMapItem` → `compare`): the link needs a form for a cycle of specs (open question in the report).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doMap

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

theorem typed.compareWalker.compare.wp_proof
    (hSchema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (hdeduceAtom : typed.deduceAtom.spec (GF := GF))
    (hhandleAtom : typed.handleAtom.spec (GF := GF))
    (hAtom_Equals : schema.Atom.Equals.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hValidationErrors_WithLazyPrefix : typed.ValidationErrors.WithLazyPrefix.spec (GF := GF))
    (hSet_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (hcompareWalker_doScalar : typed.compareWalker.doScalar.spec (GF := GF))
    (hcompareWalker_doList : typed.compareWalker.doList.spec (GF := GF))
    (hcompareWalker_doMap : typed.compareWalker.doMap.spec (GF := GF)) :
    typed.compareWalker.compare.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
