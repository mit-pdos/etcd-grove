module
public import Proof.go_etcd_io.bbolt.WriteTxLemmas
public import Proof.go_etcd_io.bbolt.WriteTxShape

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.node(pgid, parent)` (`Bucket.node.spec`) with the bucket's shape (`WriteTxShape.lean`):
of a clean bucket, a new node read from its root page (no `parent`, no materialized root) or
from a child its branch `parent` has not materialized (a page position). The new node takes its
position's tokens: its page's, and its children's subtrees' (a branch) or its nested buckets'
(a leaf); the keys stay a B+tree's; the entries of nested buckets stay where they are. -/
abbrev Bucket.node.sspec : Prop :=
  ∀ (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (txl : Loc) (st : TxStats)
    (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac) (pgid : w64) (parent : Loc) (p : Loc)
    (pg : List w8) (src : Src),
  viewOK W → bktClean W hwm bl B → B.bv.tx' = txl →
  (B.nm !! pgid = none → nodeSrcOK W B pm pgid p pg src ∧
    ((parent = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root') ∨
     ∃ i, pagePosAt B parent i pgid)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗ bktShape γ W B }}
    (App (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"node")) (Val #pgid)) (Val #parent))
  {{ (l : Loc) (B' : BRec) (st' : TxStats), RET #l;
      bktOwn W bl B' ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗ bktShape γ W B' ∗
      ⌜nodeRes B bl pgid parent p pg src l B' st st' ∧
        ∀ k v, entryIn W B k v → entryIn W B' k v⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
