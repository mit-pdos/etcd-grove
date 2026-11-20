/-
`mergingWalker.indexListPathElements(t, list, allowDuplicates)` (internal): the keys of a list's
items in order (`keysOf ks vs`, as a fresh slice of path elements) and a fresh map from each key
to its item (`itemOf`). In the scope the items are keyed and the keys distinct (conformance), so
no error and no duplicate (the duplicate branches, an error or a `null` item, are not taken).
Each item value in the map is a fresh wrapper (`list.At`) whose interface is the item's: the map
holds, for each key, a value of the item (persistent).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows). Prove phase (2026-11-20,
ownership rule: the only caller is `mergingWalker.visitListItems`): the pre adds the list type
`S.find tn` and the items' conformance, which `listItemToPathElement`'s spec takes.
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
abbrev typed.mergingWalker.indexListPathElements.spec : Prop :=
  ∀ (w : Loc) (wv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker) (sc : Loc) (S : Schema) (tp : Loc) (e : TypeRef)
    (ks : List GoString) (fs : List (GoString × TypeRef)) (el : Option TypeRef) (r : ElemRel)
    (ll : value.List') (ol : Option (List UVal)) (allowDup : Bool) (tn : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ w ↦ wv ∗ isAlloc wv.allocator' ∗ isSchema sc S ∗ ⌜wv.schema' = sc⌝ ∗
      isListRep tp e .associative ks ∗ isListO ll ol ∗
      ⌜S.WF ∧ ks ≠ [] ∧ S.find e.name = some (.map fs el r) ∧ S.find tn = some (.list e .associative ks) ∧
        (∀ v ∈ ol.getD [], conforms S e v ∧ itemKeyOk ks v) ∧ (keysOf ks (ol.getD [])).Nodup⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"indexListPathElements")) (Val #tp)) (Val #ll)) (Val #allowDup))
  {{ (pes : GoSlice) (obs : fieldpath.PathElementValueMap) (errs : GoSlice),
      RET (PairV (PairV #pes #obs) #errs); w ↦ wv ∗ isAlloc wv.allocator' ∗ noErrs errs ∗
      (∃ es : List fieldpath.PathElement, pes ↦* es ∗ isPEs es (keysOf ks (ol.getD []))) ∗
      (∃ M : PEMap value.Value, ownPEVMapV obs M ∗
        ∀ k, match itemOf ks (ol.getD []) k, M k with
          | none, none => iprop(True)
          | some x, some v => isVal v x
          | _, _ => iprop(False)) }}

end spec

end smd
end EtcdGrove
end Perennial
