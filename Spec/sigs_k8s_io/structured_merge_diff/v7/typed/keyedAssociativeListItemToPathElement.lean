/-
`typed.keyedAssociativeListItemToPathElement(a, s, list, child)` (internal): the path element of an
item of an associative list with keys `ks` (`keyOf ks x`: the key fields the item has, sorted by
name), or an error (a `null` item, an item that is not a map, a map without any key field). The
item is lent (any share); the allocator is threaded (`isAlloc`).

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
    (child : value.Value) (dq : DFrac) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isAlloc a ∗ isSchema sc S ∗ isListRep lp e rel ks ∗ isValF child dq x ∗
      ⌜S.WF ∧ ks ≠ [] ∧ S.find e.name = some (.map fs el r)⌝ }}
    (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.keyedAssociativeListItemToPathElement)) (Val #a)) (Val #sc)) (Val #lp)) (Val #child))
  {{ (pe : fieldpath.PathElement) (err : GoInterface), RET (PairV #pe #err);
      isAlloc a ∗ isValF child dq x ∗
      match keyOf ks x with
      | some k => iprop(⌜err = interface.nil⌝ ∗ isPE pe k)
      | none => iprop(⌜err ≠ interface.nil⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
