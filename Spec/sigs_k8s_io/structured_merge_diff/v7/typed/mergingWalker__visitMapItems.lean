/-
`mergingWalker.visitMapItems(t, lhs, rhs)` (internal): merges a granular map's entries: for each
key of either side (`MapZipUsing`, any order), the entry's merge (`visitMapItem`) into a fresh map;
`out` becomes that map if it is not empty, else stays nil (`mergeMapOut`: the entries in key
order, the map canonical).

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
abbrev typed.mergingWalker.visitMapItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (tp : Loc) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (lm rm : value.Map)
    (ol or_ : Option (List (GoString × UVal))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isMapRep tp fs e rel ∗ isMapO lm ol ∗ isMapO rm or_ ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ st.out = none ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.map) ∧ confO S st.t (or_.map UVal.map)⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #lm)) (Val #rm))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      mwOwn w sc S { st with out := (mergeMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e
        (kvsOrEmpty ol) (kvsOrEmpty or_)) } }}

end spec

end smd
end EtcdGrove
end Perennial
