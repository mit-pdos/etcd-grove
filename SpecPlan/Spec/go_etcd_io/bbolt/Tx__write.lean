/-
`tx.write()` (`tx.go`): `pwrite` each allocated page in id order (in `MaxAllocSize` chunks), then
`fdatasync` unless `NoSync`. (internal, mirrors the code; `db.grow` before it in `Commit`)

**Proof sketch.** `sort.Sort` of the dirty pages by id (4d's `Pages.Len`/`Less`/`Swap`, every page's
bytes at one share: the writer owns them); per page, 4d's `UnsafeByteSlice(p, written, 0, sz)` chunks
of at most `MaxAllocSize - 1` bytes covering its extent in order, each `pwrite`n; after the writes, a
single-page buffer zeroed and back to the pool (so `db.allocate`'s next page has an empty header,
`node.write`'s `nodeWritable`). Each page is in the writer's share of the file beyond the current meta's
reachable pages (`boltFile γ`'s crash fact holds whatever these bytes are: the current meta does
not reach them); OsFs's `pwrite` (D9 for single pages) and `Fdatasync`. A failed sync drops every
dirty page of the file (D2), not only these: in sync mode the others are none (the last commit
synced), under `NoSync` earlier commits' pages; `Commit`'s settling update records it (`failed`,
hence `lost`; review S3).
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

/-- (internal) `tx.write()`: the transaction's pages in the file, or an error. -/
def Tx.write.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView),
  {{ wtxAt (GF := GF) tx γ T CommitStage.spilled }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ wtxAt tx γ T CommitStage.flushed) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ wtxAt tx γ T CommitStage.spilled) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
