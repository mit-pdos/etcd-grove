/-
`(*BTree[T]).Clone()`, of `k8s.io/utils/third_party/forked/golang/btree` (translated names-only:
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

/-- `t.Clone()`: Go's documentation: "Clone clones the btree, lazily. Clone should not be
called concurrently, but the original tree (t) and the new tree (t2) can be used
concurrently once the Clone call completes." Clone writes `t` (its copy-on-write context),
so it takes the tree fully owned; it gives two fully owned trees with the same items
(copy-on-write keeps them independent). -/
abbrev btree.BTree.Clone.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ ownBTree T t isItem less items (DFrac.own 1) }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"Clone")) (Val #()))
  {{ (t2 : Loc), RET #t2;
      ownBTree T t isItem less items (DFrac.own 1) ∗ ownBTree T t2 isItem less items (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
