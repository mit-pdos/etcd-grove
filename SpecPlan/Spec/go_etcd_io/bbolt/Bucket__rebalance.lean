/-
`b.rebalance()` (`bucket.go`), on the root (`tx.root.rebalance()`, `Commit`'s first step): each
cached node with deletions merges with a sibling or is removed (`node.rebalance`), recursively for
the child buckets. (internal, mirrors the code)

**Proof sketch.** Over the node cache's abstraction relation: `node.rebalance` keeps the entries,
removes empty pages, merges below `minKeys`, collapses a root branch of one child (the old D-E: all
leaves at one depth makes the merge type-correct); freed pages pending (4d's `freelist.Free`).
**Verify-round (A11 F9).** Each `node.rebalance` keeps the abstraction relation (`repKept` in
its post), so `wtxAt … nodes` is reached at the same `T`.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) `tx.root.rebalance()`: the write transaction's nodes rebalanced, its data unchanged. -/
def Bucket.rebalance.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView),
  {{ boltTx (GF := GF) tx γ 1 T ∗ ⌜T.rw = true⌝ }}
    (App (Val ((structFieldRef go_etcd_io.bbolt.Tx go!"root" tx) @!! go.GoType.PointerType Bucket.ty @!! go!"rebalance"))
      (Val #()))
  {{ RET #(); wtxAt tx γ T CommitStage.nodes }}

end spec

end Bbolt
end EtcdGrove
end Perennial
