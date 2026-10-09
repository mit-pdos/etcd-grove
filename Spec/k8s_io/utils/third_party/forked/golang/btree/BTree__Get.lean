/-
`(*BTree[T]).Get(key)`, of `k8s.io/utils/third_party/forked/golang/btree` (translated names-only:
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

/-- `t.Get(key)`: Go's documentation: "Get looks for the key item in the tree, returning
it. It returns (zeroValue, false) if unable to find that item." The item found is the one
equivalent to `key` (`btFind`); a read, on any fraction. -/
abbrev btree.BTree.Get.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (dq : DFrac) (key : T') (k : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ ownBTree T t isItem less items dq ∗ isItem key k }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"Get")) (Val #key))
  {{ (item : T') (ok : Bool), RET (PairV #item #ok);
      ownBTree T t isItem less items dq ∗
      match btFind less k items with
      | some v => ⌜ok = true⌝ ∗ isItem item v
      | none => ⌜ok = false ∧ item = zero_val T'⌝ }}

end spec

end EtcdGrove
end Perennial
