module
public import Proof.go_etcd_io.bbolt.WriteTxLemmas

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

/-- `b.node(pgid, parent)` of the bucket at `bl` (record `B`) of the write transaction at `txl`:
the cached node `b.nodes[pgid]` if there is one; else a new node `l`, read from the inline page
or page `pgid` (`nodeSrcOK`), cached, and made the bucket's root node (no `parent`) or added to
`parent`'s children; the `NodeCount` statistic grows by one. -/
abbrev Bucket.node.spec : Prop :=
  ∀ (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (st : TxStats) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (pgid : w64) (parent : Loc) (p : Loc) (pg : List w8)
    (src : Src),
  viewOK W → B.bv.tx' = txl → (∀ l, B.nm !! pgid = some l → l ≠ null) →
  (B.nm !! pgid = none → nodeSrcOK W B pm pgid p pg src ∧
    (parent = null ∨ (B.ns !! parent).isSome)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }}
    (App (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"node")) (Val #pgid)) (Val #parent))
  {{ (l : Loc) (B' : BRec) (st' : TxStats), RET #l;
      bktOwn W bl B' ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗
      ⌜nodeRes B bl pgid parent p pg src l B' st st'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
