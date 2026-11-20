/-
`mergingWalker.visitListItems(t, lhs, rhs)` (internal): merges an associative list's items: the
items of each side indexed by key (`indexListPathElements`; the right side's keys distinct, the
scope's conformance), then merged in **`mergeKeys`'s order**, the loop of Go step by step
(`mergeOrderF`): walking both key lists, a key at the head of both is merged and emitted; a
left key the right side also has, met before the next shared key in the right side's order, is
skipped (emitted later where the right side has it); a left-only key is emitted in place (its
item merged with nothing); otherwise the right side's next key is emitted (merged with the left
item of that key, if any). Each emitted key's merge (`mergeF` on the two items, `mergeListItem`)
is appended unless absent. `out` becomes the list of those, or stays nil if none
(`mergeListOut`). The item merges' errors are dropped (`errs = append(errs, errs...)` shadows:
`nonissues/smd-merge-list-item-errors-dropped.md`); none occur in the scope.

Checked against Go: `mergeKeys` equals SMD's order on 20000 random pairs of key lists
(`notes/smd-plan.md`, "Against Go", `TestMergeOrder`).

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
abbrev typed.mergingWalker.visitListItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (tp : Loc) (e : TypeRef) (ks : List GoString)
    (ll rl : value.List') (ol or_ : Option (List UVal)) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st sp ∗ isListRep tp e .associative ks ∗ isListO ll ol ∗ isListO rl or_ ∗
      ⌜S.find st.t.name = some (.list e .associative ks) ∧ st.out = none ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.list) ∧ confO S st.t (or_.map UVal.list)⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll)) (Val #rl))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      (∃ sp' : Loc, mwOwn w sc S { st with out := (mergeListOut (fuelL (ol.getD []) (or_.getD [])) S e ks
        (ol.getD []) (or_.getD [])) } sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
