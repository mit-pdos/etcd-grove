/-
`(*BTree[T]).ReplaceOrInsert(item)`, of `k8s.io/utils/third_party/forked/golang/btree` (translated names-only:
the trust boundary). Lean-first (no Rocq counterpart); see `InvBtree.lean`.
-/
import EtcdGrove.Cache.InvBtree

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

/-- `t.ReplaceOrInsert(item)`: Go's documentation: "ReplaceOrInsert adds the given item to
the tree. If an item in the tree already equals the given one, it is removed from the
tree and returned, and the second return value is true. Otherwise, (zeroValue, false)."
On a fully owned tree: the items become `btInsert` (the equivalent item replaced, or `v`
inserted in order), and the replaced one (`btFind`) is returned. -/
abbrev btree.BTree.ReplaceOrInsert.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (item : T') (v : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ ownBTree T t isItem less items (DFrac.own 1) ∗ isItem item v }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"ReplaceOrInsert")) (Val #item))
  {{ (old : T') (ok : Bool), RET (PairV #old #ok);
      ownBTree T t isItem less (btInsert less v items) (DFrac.own 1) ∗
      match btFind less v items with
      | some w => ⌜ok = true⌝ ∗ isItem old w
      | none => ⌜ok = false ∧ old = zero_val T'⌝ }}

end spec

end EtcdGrove
end Perennial
