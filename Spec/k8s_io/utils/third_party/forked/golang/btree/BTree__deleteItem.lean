module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Model
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- `(*BTree[T]).deleteItem(item, typ)`: remove the entry with `item`'s key, the
smallest or the largest (`tgt`); the removed item and whether there was one. -/
abbrev BTree.deleteItem.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (s : List (V × K)) (item : V) (tgt : Target K) (typ : w64),
  typ = tgt.code →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownBTree o t (DFrac.own 1) s ∗ targetItem o tgt item }}
    (App (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"deleteItem")) (Val #item)) (Val #typ))
  {{ RET (PairV #((removeOp tgt s).2.getD (zero_val V)) #((removeOp tgt s).2.isSome));
      ownBTree o t (DFrac.own 1) (removeOp tgt s).1 }}

end spec

end btree
end EtcdGrove
end Perennial
