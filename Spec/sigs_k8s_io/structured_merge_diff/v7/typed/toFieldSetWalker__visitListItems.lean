/-
`toFieldSetWalker.visitListItems(t, list)` (internal): an associative list's items: each item's
path and what the item sets (in a child walker) (`fieldsL`). The duplicate-key branch (a key
seen twice: only its path) is not taken: the keys are distinct (conformance).

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
abbrev typed.toFieldSetWalker.visitListItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (tp : Loc) (e : TypeRef)
    (ks : List GoString) (ll : value.List') (vs : List UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F ∗ isListRep tp e .associative ks ∗ isListV ll vs ∗
      ⌜S.find st.t.name = some (.list e .associative ks) ∧ conforms S st.t (.list vs) ∧
        (F.union (fieldsL S e ks st.path vs)).CardLt typedSizeMax⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ twOwn w sc S st s (F.union (fieldsL S e ks st.path vs)) }}

end spec

end smd
end EtcdGrove
end Perennial
