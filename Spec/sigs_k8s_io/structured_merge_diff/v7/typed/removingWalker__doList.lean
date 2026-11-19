/-
`removingWalker.doList(t)` (internal; the `atomHandler` method for a list type): not a list, an
empty list or an atomic list: nothing (the output stays nil: `null`); else each item whose path is
removed goes, an item with removed paths below it loses them (`removeItemsWithSchema` on the
item), the rest kept; the output is the items left, or nil if none (`removeAt`, `removeL`).

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
abbrev typed.removingWalker.doList.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (v : value.Value) (dq : DFrac) (x : UVal) (rp : Loc) (R : PathSet) (a : value.Allocator) (t : TypeRef) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rmOwn w sc S v rp R a interface.nil ∗ isValF v dq x ∗ isListRep tp e rel ks ∗ ⌜S.find t.name = some (.list e rel ks) ∧ conforms S t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; ∃ out : GoInterface, rmOwn w sc S v rp R a out ∗ isIface out (removeAt S t R x) ∗ isValF v dq x }}

end spec

end smd
end EtcdGrove
end Perennial
