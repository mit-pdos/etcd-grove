/-
`(*BTree[T]).Delete(key)`, of `k8s.io/utils/third_party/forked/golang/btree` (translated names-only:
the trust boundary). Lean-first (no Rocq counterpart); see `InvBtree.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvBtree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `t.Delete(key)`: Go's documentation: "Delete removes an item equal to the passed in
item from the tree, returning it. If no such item exists, returns (zeroValue, false)." On a
fully owned tree: the items become `btDelete`, and the removed one (`btFind`) is
returned. -/
abbrev btree.BTree.Delete.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (key : T') (k : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ ownBTree T t isItem less items (DFrac.own 1) ∗ isItem key k }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"Delete")) (Val #key))
  {{ (old : T') (ok : Bool), RET (PairV #old #ok);
      ownBTree T t isItem less (btDelete less k items) (DFrac.own 1) ∗
      match btFind less k items with
      | some w => ⌜ok = true⌝ ∗ isItem old w
      | none => ⌜ok = false ∧ old = zero_val T'⌝ }}

end spec

end EtcdGrove
end Perennial
