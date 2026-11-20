/-
`reconcileWithSchemaWalker.doMap(t)` (internal; the `atomHandler` method for a map type) (the deduced map type is skipped: not in the scope):
an atomic type reached with children (not `isAtomic`) and a non-empty child set sets both
accumulators to `{path}` (`NewSet(path)`, empty at the root); else, with a child set, the children
(`visitMapItems`): `reconOut`.

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
abbrev typed.reconcileWithSchemaWalker.doMap.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (F R A : Option PathSet) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwn w sc S st F R A sp ∗ isMapRep tp fs e rel ∗ ⌜S.find st.t.name = some (.map fs e rel) ∧ (st.isAtomic = true → F = none)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwn w sc S st F R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty)) ∧
        optU A A' = optU A (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty))⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
