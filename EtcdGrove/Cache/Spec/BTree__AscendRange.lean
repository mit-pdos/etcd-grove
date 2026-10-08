/-
`(*BTree[T]).AscendRange(greaterOrEqual, lessThan, iter)`, of `k8s.io/utils/third_party/forked/golang/btree` (translated names-only:
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

/-- `t.AscendRange(greaterOrEqual, lessThan, iter)`: Go's documentation: "AscendRange
calls the iterator for every value in the tree within the range [greaterOrEqual,
lessThan), until iterator returns false." The visited items are `btAscendRange` (those
not less than `greaterOrEqual` and less than `lessThan`, in order), in the loop-invariant
style of `AscendGreaterOrEqual`. A read, on any fraction. -/
abbrev btree.BTree.AscendRange.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (dq : DFrac)
    (ge lt : T') (vge vlt : V) (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ ownBTree T t isItem less items dq ∗ isItem ge vge ∗
      isItem lt vlt ∗ P 0 ∗ btIterSpec iter isItem (btAscendRange less vge vlt items) P Q }}
    (App (App (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"AscendRange")) (Val #ge)) (Val #lt)) (Val #iter))
  {{ RET #(); ownBTree T t isItem less items dq ∗
      (Q ∨ P (btAscendRange less vge vlt items).length) }}

end spec

end EtcdGrove
end Perennial
