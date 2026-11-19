/-
`removingWalker.doMap(t)` (internal; the `atomHandler` method for a map type): not a map, an empty
map or an atomic map: nothing (`null`); else each entry whose path is removed goes, an entry with
removed paths below it loses them (`removeItemsWithSchema` at the entry's type), the rest kept;
the output is the map left, or nil if empty (`removeAt`, `removeM`).

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
abbrev typed.removingWalker.doMap.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (v : value.Value) (dq : DFrac) (x : UVal) (rp : Loc) (R : PathSet) (a : value.Allocator) (t : TypeRef) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rmOwn w sc S v rp R a interface.nil ∗ isValF v dq x ∗ isMapRep tp fs e rel ∗ ⌜S.find t.name = some (.map fs e rel) ∧ conforms S t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; ∃ out : GoInterface, rmOwn w sc S v rp R a out ∗ isIface out (removeAt S t R x) ∗ isValF v dq x }}

end spec

end smd
end EtcdGrove
end Perennial
