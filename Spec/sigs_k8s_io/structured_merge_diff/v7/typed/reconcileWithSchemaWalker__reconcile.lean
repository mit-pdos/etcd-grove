/-
`reconcileWithSchemaWalker.reconcile()` (internal; recursive through `handleAtom` and the walker's
`doScalar`/`doList`/`doMap`): at a node of path `st.path`, type `st.t`, reached with the child set
`F` (the field set's paths below the node; nil for a member without children, `isAtomic`), adds to
the accumulators the atomic nodes with children at and below it (`reconOut`). The accumulators
start as the parent's (`*v2 = *v`) and a node's own may replace them (`toRemove = NewSet(path)`),
so the post says what they are joined with the parent's (`optU`): `finishDescent`'s merge. No
error (the type resolves).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.reconcileWithSchemaWalker.reconcile.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (F R A : Option PathSet) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwn w sc S st F R A sp ∗ ⌜(S.find st.t.name).isSome ∧ (st.isAtomic = true → F = none) ∧ (F.getD PathSet.empty).CardLt (2 ^ 63)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"reconcile")) (Val #()))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwn w sc S st F R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty)) ∧
        optU A A' = optU A (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty))⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
