/-
`tx.commitFreelist()` (`tx.go`): allocate pages for the freelist (4d's
`EstimatedWritePageSize`), write it (4d's `freelist.Write`), record it in the meta; on an allocation
error, `rollback`. (internal, mirrors the code; not called under `NoFreelistSync`, etcd's)

**Proof sketch.** 4d's `freelist.Write` into the allocated page (its count and ids within the
extent, the old `fileHolds`' synced-freelist clause); `tx.meta.SetFreelist`.

In 4d's terms (integration I7): `EstimatedWritePageSize` (`F.count < flMaxIds`) gives
`F.estimatedSize`; `tx.allocate(est / 4096 + 1)` (below `2 ^ 32`: `est < 2 ^ 36 * 8 + 24`) runs 4d's
`Allocate`, which only shrinks `free`, so `F'.estimatedSize ≤ F.estimatedSize < (est / 4096 + 1) *
4096` bytes, the page's extent: `Write`'s room premise; `Write` leaves `freelistPage bs F'.ids`,
which `freelistPage_read` reads back (`freelistReadable`, the ids sorted and distinct: the file's
synced-freelist clause for the next meta). The page itself was allocated, so it is neither free
nor pending; the base's freelist page, freed by `Commit` just before, is pending, so in the ids.
Every free page is then among the new page's ids: the reload invariant (`Internal.lean`, "The
freelist's side") for the meta this commit writes.
**Verify-round (A11 F9).** The allocated page's buffer comes from `Tx.allocate`'s `C.bufs`
(`freshPage`: the room `(est / 4096 + 1) * 4096`, an empty header), lent by `wtxCore_buf` to 4d's
`freelist.Write` and taken back.
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

/-- (internal) `tx.commitFreelist()`: the freelist page written, or an error and the transaction
rolled back. -/
def Tx.commitFreelist.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView),
  {{ wtxAt (GF := GF) tx γ T CommitStage.spilled }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"commitFreelist")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ wtxAt tx γ T CommitStage.spilled) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ txDone tx) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
