/-
`b.spill()` (`bucket.go`), on the root: child buckets first (inline ones written into their parent's
value, `Bucket.write`), then the root node (`node.spill`: split by `splitThreshold`, D17's bound;
each piece written to a page from `tx.allocate`, 4d's `freelist.Allocate` or past the high-water
mark with `db.grow`'s remap). (internal, mirrors the code)

**Proof sketch.** Every page written fits its extent (`node.size`, `bboltEntryMax`); the parents'
keys are exact; an `allocate` error (the mapping past `MaxSize`, a remap's `mmap` errno) leaves the
transaction to roll back.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) `tx.root.spill()`: the nodes written to fresh pages, or an error. -/
def Bucket.spill.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView),
  {{ wtxAt (GF := GF) tx γ T CommitStage.nodes }}
    (App (Val ((structFieldRef go_etcd_io.bbolt.Tx go!"root" tx) @!! go.GoType.PointerType Bucket.ty @!! go!"spill"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ wtxAt tx γ T CommitStage.spilled) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ wtxAt tx γ T CommitStage.nodes) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
