/-
`Bucket.free` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U7; used by U7 (`DeleteBucket`), U9b (`Bucket.spill`'s inlineable children). Proof:
`Proof/go_etcd_io/bbolt/Bucket__free.lean` (U7e's; batch 35).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.free()` of a live bucket `bl`, the writer's database side live: nothing for an inline
bucket; else every extent of its logical tree (`X.extents`, in `forEachPageNode`'s order: a
page's, or a materialized node's page's) freed for the writer's txid, the nodes reached at page id
`0`, and its header's root `0` (`bktFreed`). Batch 35 (U7e's `spec'`): in the tree case the bucket's
logical tree is finite (`rtOK`, `Rebalance/RTreeX`: the walk's termination; `rtOK_init` from `wOK`
for `DeleteBucket`, rebalance's post for `spill`), the records' meta txid is the writer's (`Free`
takes `tx.meta.Txid()`), and no position has a page buffer (`tx.page` reads the view). -/
abbrev Bucket.free.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec),
  X.t.bs !! bl = some B → bl ∈ X.liveB →
  (B.ib.root' ≠ W64 0 → bktLocalOK X bl ∧
    (∀ pid ∈ X.positions bl, X.t.pm !! pid = none) ∧
    w.fl.canFreeAll w.wtxid (X.extents bl) ∧ rtOK X bl ∧ X.t.mv.txid' = w.wtxid) →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X.v w' ∗
      ⌜(B.ib.root' = W64 0 ∧ X' = X ∧ w' = w) ∨
       (B.ib.root' ≠ W64 0 ∧ bktFreed X X' bl ∧
         w' = w.withFl (w.fl.freeAll w.wtxid (X.extents bl)))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
