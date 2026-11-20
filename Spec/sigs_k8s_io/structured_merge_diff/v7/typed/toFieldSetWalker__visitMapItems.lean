/-
`toFieldSetWalker.visitMapItems(t, m)` (internal): a granular map's entries (`Map.Iterate`, any
order): what each sets (in a child walker), and the entry's own path if it is `null`, `{}` or
not a declared field (`fieldsM`).

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
abbrev typed.toFieldSetWalker.visitMapItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (tp : Loc)
    (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (m : value.Map)
    (kvs : List (GoString × UVal)) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F sp ∗ isMapRep tp fs e rel ∗ isMapV m kvs ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ conforms S st.t (.map kvs) ∧
        (F.union (fieldsM S fs e st.path kvs)).CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #m))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ (∃ sp' : Loc, twOwn w sc S st s (F.union (fieldsM S fs e st.path kvs)) sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
