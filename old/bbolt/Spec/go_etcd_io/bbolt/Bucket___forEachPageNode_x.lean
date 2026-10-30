module
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w

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

/-- `b._forEachPageNode(pgId, depth, fn)` at a position of a write transaction's bucket that is
a materialized leaf node `nl` (what `Bucket.free` of an inlineable bucket visits during the
spill): `fn(nil, nl, depth)` (`fn`'s spec: from `R` to `Q` and the node, still a leaf; it is lent the
bucket's struct, the view and the transaction's fields), and no child to visit. -/
abbrev Bucket._forEachPageNode.xspec : Prop :=
  ∀ (W : WView) (bl : Loc) (bv : Bucket) (B : BRec) (dqb : DFrac) (txl : Loc) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (pgid depth : w64) (fn : GoFunc) (nl : Loc)
    (R : IProp GF) (Q : node → IProp GF),
  bv = B.bv → B.bv.tx' = txl → (∀ c l, B.nm !! c = some l → l ≠ null) →
  (B.ib.root' = W64 0 → pgid = W64 0) → resolve B pgid = some nl →
  W.data.locCar ≠ 0 → W.ps < 2 ^ 32 →
  {{ R ∗ bl ↦{dqb} bv ∗ wView W ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }}
    (App (App (App (Val #fn) (Val #null)) (Val #nl)) (Val #depth))
    {{ RET #(); ∃ (nv : node), nl ↦ nv ∗ ⌜nv.isLeaf' = true⌝ ∗ Q nv ∗ bl ↦{dqb} bv ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗ pmap ↦${dqp} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }} →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗
      B.bv.InBucket' ↦{dqb} B.ib ∗ B.bv.nodes' ↦${dqb} B.nm ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗ pmap ↦${dqp} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗ R }}
    (App (App (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"_forEachPageNode"))
      (Val #pgid)) (Val #depth)) (Val #fn))
  {{ RET #(); bl ↦{dqb} bv ∗ B.bv.InBucket' ↦{dqb} B.ib ∗ B.bv.nodes' ↦${dqb} B.nm ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗ pmap ↦${dqp} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗ ∃ (nv : node), nl ↦ nv ∗ ⌜nv.isLeaf' = true⌝ ∗ Q nv }}

end spec

end bbolt
end EtcdGrove
end Perennial
