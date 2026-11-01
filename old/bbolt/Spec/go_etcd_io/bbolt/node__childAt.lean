module
public import Spec.go_etcd_io.bbolt.Bucket__node

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.childAt(index)` of a branch node `nl` (record `r`) of the bucket `bl`: `b.node` of the
child page of its inode `index` (entry `w`), under `n` (see `Bucket.node.spec`). It panics on a
leaf, and on an index out of range. -/
abbrev node.childAt.spec : Prop :=
  ∀ (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (st : TxStats) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (nl : Loc) (r : NRec) (idx : w64) (w : WEntry)
    (p : Loc) (pg : List w8) (src : Src),
  viewOK W → B.bv.tx' = txl → B.ns !! nl = some r → r.nv.bucket' = bl → r.nv.isLeaf' = false →
  0 ≤ sint.Z idx → r.ws[(sint.Z idx).toNat]? = some w →
  (∀ l, B.nm !! w.pgid = some l → l ≠ null) →
  (B.nm !! w.pgid = none → nodeSrcOK W B pm w.pgid p pg src) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"childAt")) (Val #idx))
  {{ (l : Loc) (B' : BRec) (st' : TxStats), RET #l;
      bktOwn W bl B' ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗
      ⌜nodeRes B bl w.pgid nl p pg src l B' st st'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
