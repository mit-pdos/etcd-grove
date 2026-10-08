/-
`(*BTree[T]).AscendGreaterOrEqual(pivot, iter)`, of `k8s.io/utils/third_party/forked/golang/btree` (translated names-only:
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

/-- `t.AscendGreaterOrEqual(pivot, iter)`: Go's documentation: "AscendGreaterOrEqual calls
the iterator for every value in the tree within the range [pivot, last], until iterator
returns false." The visited items are `btAscendGe` (those not less than `pivot`, in order);
with `iter` meeting `btIterSpec` for an invariant `P` and a final postcondition `Q`: `Q`
if `iter` stopped the iteration, `P` of the number of visited items if not. A read, on any
fraction. -/
abbrev btree.BTree.AscendGreaterOrEqual.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (dq : DFrac)
    (pivot : T') (vp : V) (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ ownBTree T t isItem less items dq ∗ isItem pivot vp ∗ P 0 ∗
      btIterSpec iter isItem (btAscendGe less vp items) P Q }}
    (App (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"AscendGreaterOrEqual")) (Val #pivot)) (Val #iter))
  {{ RET #(); ownBTree T t isItem less items dq ∗
      (Q ∨ P (btAscendGe less vp items).length) }}

end spec

end EtcdGrove
end Perennial
