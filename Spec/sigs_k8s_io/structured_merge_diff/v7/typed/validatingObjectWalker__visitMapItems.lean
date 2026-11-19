/-
`validatingObjectWalker.visitMapItems(t, m)` (internal): validates each entry (`IterateUsing`, any
order) against its type (the declared field's, else the element type) in a child walker; an
undeclared key without an element type is an error (and stops the iteration): no error exactly
when the map conforms.

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
abbrev typed.validatingObjectWalker.visitMapItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (tp : Loc) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (m : value.Map) (kvs : List (GoString × UVal)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st ∗ isMapRep tp fs e rel ∗ isMapV m kvs ∗
      ⌜S.find st.t.name = some (.map fs e rel)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #m))
  {{ (errs : GoSlice), RET #errs; errsIff errs (conforms S st.t (.map kvs)) ∗ vwOwn w sc S st }}

end spec

end smd
end EtcdGrove
end Perennial
