/-
`compareWalker.visitMapItems(t, lhs, rhs)` (internal): compares a granular map's entries: for each
key of either side (`MapZipUsing`, any order), `visitMapItem` (`cmpMapOut`).

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
abbrev typed.compareWalker.visitMapItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (tp : Loc)
    (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (lm rm : value.Map)
    (ol or_ : Option (List (GoString × UVal))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isMapRep tp fs e rel ∗ isMapO lm ol ∗ isMapO rm or_ ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.map) ∧ confO S st.t (or_.map UVal.map) ∧
        (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path (kvsOrEmpty ol) (kvsOrEmpty or_))).removed.CardLt typedSizeMax ∧
        (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path (kvsOrEmpty ol) (kvsOrEmpty or_))).modified.CardLt typedSizeMax ∧
        (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path (kvsOrEmpty ol) (kvsOrEmpty or_))).added.CardLt typedSizeMax⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #lm)) (Val #rm))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      cwOwn w sc S st c (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path
        (kvsOrEmpty ol) (kvsOrEmpty or_))) }}

end spec

end smd
end EtcdGrove
end Perennial
