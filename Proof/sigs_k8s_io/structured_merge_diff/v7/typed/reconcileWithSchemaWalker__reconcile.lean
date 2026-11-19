/-
`typed.reconcileWithSchemaWalker.reconcile`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Recursive (`reconcile` → `handleAtom` → `doList`/`doMap` → `visit*` → `reconcile`): the link needs a form for a cycle of specs (open question in the report).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcile
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doMap

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

theorem typed.reconcileWithSchemaWalker.reconcile.wp_proof
    (hSchema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hhandleAtom : typed.handleAtom.spec (GF := GF))
    (hreconcileWithSchemaWalker_doScalar : typed.reconcileWithSchemaWalker.doScalar.spec (GF := GF))
    (hreconcileWithSchemaWalker_doList : typed.reconcileWithSchemaWalker.doList.spec (GF := GF))
    (hreconcileWithSchemaWalker_doMap : typed.reconcileWithSchemaWalker.doMap.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.reconcile.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
