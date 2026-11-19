/-
**`fieldpath`'s representation laws, proved** (`fieldpath/Vocab.lean`, "Representation"), and the
representation facts the package's proofs share (injectivity of its struct values, the sealed
predicates' basic rules).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpL

/-- Two values with a field's deterministic projection have equal projections. -/
theorem proj_eq [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    {t : Tag} {f : GoInstruction} {a b : val} {ea eb : Expr}
    (ha : go.IsGoStepPureDetTagged t f a ea) (hb : go.IsGoStepPureDetTagged t f b eb)
    (h : a = b) : ea = eb := by
  have h1 := ha.isGoStep_det_internal.isGoStep_pure_det
  have h2 := hb.isGoStep_det_internal.isGoStep_pure_det
  subst h
  rw [h2] at h1
  exact cast (congrFun h1 eb) rfl

section inj
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

include sem package_sem in
theorem versionedSet_inj : Function.Injective (intoVal (V := fieldpath.versionedSet)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have i := package_sem.versionedSet_instance
  have e1 := go.intoVal_inj (Expr.Val.inj (proj_eq (i.get_set x) (i.get_set y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj (proj_eq (i.get_apiVersion x) (i.get_apiVersion y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj (proj_eq (i.get_applied x) (i.get_applied y) h))
  cases x; cases y; simp_all

end inj

end fpL

end smd
end EtcdGrove
end Perennial
