/-
`reconcileWithSchemaWalker.visitListItems(t, element)` (internal): at a granular list node with
child set `element` (`F`), each child path element (`Children`, then `Members`) visited in a child
walker with its own child set and `isAtomic` (a member without children):
adds the atomic nodes with children below the node (`reconBelow`).

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
abbrev typed.reconcileWithSchemaWalker.visitListItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (R A : Option PathSet) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) (ep : Loc)
    (F : PathSet) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwnAt w sc S st ps (some F) R A sp ∗ isListRep tp e rel ks ∗ isSet ep F ∗
      ⌜S.find st.t.name = some (.list e rel ks) ∧ rel ≠ .atomic ∧ F.CardLt (2 ^ 63)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ep))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwnAt w sc S st ps (some F) R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconBelow S st.t st.path F) ∧ optU A A' = optU A (reconBelow S st.t st.path F)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
