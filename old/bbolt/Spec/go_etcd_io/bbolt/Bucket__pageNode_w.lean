module
public import Proof.go_etcd_io.bbolt.WriteCursor
public import Proof.go_etcd_io.bbolt.WriteTxPred
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.pageNode(id)` of a bucket of a write transaction: the node at position `id`
(`resolve`: `b.nodes[id]`, or an inline bucket's root node), else the page (`wpageAt`: the
inline page, or page `id` of the transaction, `tx.page`). It panics on an inline bucket and an
`id` other than 0. -/
abbrev Bucket.pageNode.wspec : Prop :=
  ∀ (W : WView) (bl : Loc) (bv : Bucket) (B : BRec) (dqb : DFrac) (txl : Loc) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (id : w64),
  bv = B.bv → B.bv.tx' = txl → (∀ c l, B.nm !! c = some l → l ≠ null) →
  (B.ib.root' = W64 0 → id = W64 0) →
  (B.ib.root' ≠ W64 0 → resolve B id = none → pm !! id = none ∧ ∃ pg,
    W.pages !! uint.nat id = some pg ∧ 16 ≤ pg.length ∧ W64 (pageId pg) = id ∧
    validPageFlags (W16 (pageFlags pg)) ∧ uint.nat id * W.ps < 281474976710655) →
  W.data.locCar ≠ 0 → W.ps < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗
      B.bv.InBucket' ↦{dqb} B.ib ∗ B.bv.nodes' ↦${dqb} B.nm ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗ pmap ↦${dqp} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ (p n : Loc), RET (PairV #p #n);
      ⌜(resolve B id = some n ∧ p = null) ∨
        (resolve B id = none ∧ n = null ∧ ∃ pg, wpageAt W B id = some (p, pg))⌝ ∗
      bl ↦{dqb} bv ∗ B.bv.InBucket' ↦{dqb} B.ib ∗ B.bv.nodes' ↦${dqb} B.nm ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗ pmap ↦${dqp} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }}

end spec

end bbolt
end EtcdGrove
end Perennial
