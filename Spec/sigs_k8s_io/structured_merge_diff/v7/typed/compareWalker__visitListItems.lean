/-
`compareWalker.visitListItems(t, lhs, rhs)` (internal): compares an associative list's items by
key: the left side's keys in order, then the right side's keys the left lacks, each item pair
compared in a child walker (`compareListItem`) (`cmpListOut`). The duplicate-key branches (a
whole key modified, removed or added) are not taken: the keys are distinct (conformance).

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
abbrev typed.compareWalker.visitListItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (tp : Loc) (e : TypeRef)
    (ks : List GoString) (ll rl : value.List') (ol or_ : Option (List UVal)) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C sp ∗ isListRep tp e .associative ks ∗ isListO ll ol ∗ isListO rl or_ ∗
      ⌜S.find st.t.name = some (.list e .associative ks) ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.list) ∧ confO S st.t (or_.map UVal.list) ∧
        (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path (ol.getD []) (or_.getD []))).removed.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path (ol.getD []) (or_.getD []))).modified.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path (ol.getD []) (or_.getD []))).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll)) (Val #rl))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      (∃ sp' : Loc, cwOwn w sc S st c (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path
        (ol.getD []) (or_.getD []))) sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
