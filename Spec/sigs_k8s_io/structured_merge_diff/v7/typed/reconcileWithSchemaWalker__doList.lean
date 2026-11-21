/-
`reconcileWithSchemaWalker.doList(t)` (internal; the `atomHandler` method for a list type):
an atomic type reached with children (not `isAtomic`) sets both
accumulators to `{path}` (`NewSet(path)`, empty at the root); else, with a child set, the children
(`visitListItems`): `reconOut`.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).

The walker is `rwOwnAt` with its path slice `ps` the same before and after (spec change, Prove
phase 2026-11-21, ownership rule: `LawProofsBRecon2Own.lean`; it was `rwOwn`, slice hidden).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon2Own

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
abbrev typed.reconcileWithSchemaWalker.doList.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (F R A : Option PathSet) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwnAt w sc S st ps F R A sp ∗ isListRep tp e rel ks ∗ ⌜S.find st.t.name = some (.list e rel ks) ∧ (st.isAtomic = true → F = none) ∧ (F.getD PathSet.empty).CardLt (2 ^ 63)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwnAt w sc S st ps F R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty)) ∧
        optU A A' = optU A (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty))⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
