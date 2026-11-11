/-
`Bucket.pageNode_d` (bbolt, internal): `Bucket.pageNode` of a dead bucket (U7n,
`notes/bbolt-proof-plan.md`): `DeleteBucket`'s child after `child.nodes = nil`. Proved by U7n;
used by `Write/WalkDead` (`Bucket.free_dead`). Proof: `Proof/go_etcd_io/bbolt/Bucket__pageNode_d.lean`.
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

/-- `b.pageNode(id)` of a dead bucket `bl` of the writer (in `X.t.deadB`, not in `X.t.bs`) with
a root page and a nil node cache: the view's page `id` (`tx.page`), a nil node. It panics on a bad
page header: excluded by the premises. -/
abbrev Bucket.pageNode_d.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (id : w64)
    (pg : List w8),
  X.t.bs !! bl = none → X.t.deadB !! bl = some B → bl ∉ X.liveB → B.bv.tx' = tx →
  B.bv.nodes' = null → B.ib.root' ≠ W64 0 →
  X.v.pages !! id.toNat = some pg → X.t.pm !! id = none → 16 ≤ pg.length →
  pageId pg = id.toNat → (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ RET (PairV #(pageLoc X.v id.toNat) #null); wtxW K tx r m X }}

end spec

end bbolt
end EtcdGrove
end Perennial
