/-
`typed.keyedAssociativeListItemToPathElement(a, s, list, child)` (internal): the path element of an
item of an associative list with keys `ks` (`keyOf ks x`: the key fields the item has, sorted by
name). The item is lent (any share); the allocator is threaded (`isAlloc`).

Post-freeze change (round 2, coordinator; D1d): the item has a key (`(keyOf ks x).isSome`; Go's
error branches, a `null` item, a non-map, a map without any key field, build their errors with the
out-of-scope `errors.New`/`fmt.Errorf`); the list type is `S.find tn` and the item conforms to the
element type (so the key fields' names are distinct and their values scalars: `FieldList.Sort`'s
and `isPE`'s premises). Callers have all three from the list's conformance.

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
abbrev typed.keyedAssociativeListItemToPathElement.spec : Prop :=
  ∀ (a : value.Allocator) (sc : Loc) (S : Schema) (lp : Loc) (e : TypeRef) (rel : ElemRel)
    (ks : List GoString) (fs : List (GoString × TypeRef)) (el : Option TypeRef) (r : ElemRel)
    (child : value.Value) (dq : DFrac) (x : UVal) (tn : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isAlloc a ∗ isSchema sc S ∗ isListRep lp e rel ks ∗ isValF child dq x ∗
      ⌜S.WF ∧ rel = .associative ∧ ks ≠ [] ∧ S.find e.name = some (.map fs el r) ∧ S.find tn = some (.list e rel ks) ∧
        conforms S e x ∧ (keyOf ks x).isSome⌝ }}
    (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.keyedAssociativeListItemToPathElement)) (Val #a)) (Val #sc)) (Val #lp)) (Val #child))
  {{ (pe : fieldpath.PathElement) (err : GoInterface), RET (PairV #pe #err);
      isAlloc a ∗ isValF child dq x ∗
      match keyOf ks x with
      | some k => iprop(⌜err = interface.nil⌝ ∗ isPE pe k)
      | none => iprop(False) }}

end spec

end smd
end EtcdGrove
end Perennial
