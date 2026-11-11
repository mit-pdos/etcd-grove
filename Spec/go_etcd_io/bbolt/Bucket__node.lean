/-
`Bucket.node` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U7; used by U7 (`Cursor.node`), U8 (`node.childAt`, `node.rebalance`'s root collapse). Proof:
`Proof/go_etcd_io/bbolt/Bucket__node.lean` (a `sorry` until U7).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.node(pgid, parent)` of a live bucket `bl` of the writer (its node cache non-nil): the
cached node of `pgid` if there is one (`X` unchanged); else a new node read from the page at
position `pgid` (`matReady`: the view's page, or the inline page), cached, registered, live, and
made the root node or appended to the branch node `parent`'s children (`nodeAdded`). The
`NodeCount` statistic grows. -/
abbrev Bucket.node.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (pgid : w64)
    (parent : Loc),
  X.t.bs !! bl = some B → bl ∈ X.liveB → B.bv.nodes' ≠ null →
  (∀ l, B.nm !! pgid = some l → l ≠ null) →
  (B.nm !! pgid = none → matReady X B pgid ∧
    (parent = null ∨ ∃ rp, B.ns !! parent = some rp ∧ rp.nv.isLeaf' = false ∧ parent ∈ X.live)) →
  (B.nm !! pgid = none → B.ib.root' ≠ W64 0 → B.bv.page' = null) →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"node")) (Val #pgid))
      (Val #parent))
  {{ (l : Loc), RET #l; ∃ X' : WX, wtxW K tx r m X' ∗
      ⌜(B.nm !! pgid = some l ∧ X' = X) ∨ nodeAdded X X' bl l pgid parent⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
