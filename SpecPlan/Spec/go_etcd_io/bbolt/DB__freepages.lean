/-
`db.freepages()` (`db.go`): a read transaction (the spare reader slot) walks the tree; the ids below the high-water mark it does not reach, sorted. Users: `loadFreelist` (`fl.Init`), `rollback` under `NoFreelistSync` (`NoSyncReload`).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch.** `beginTx` on the spare slot; `recursivelyCheckBucket` on the root collects the
reachable pages (no error: the file is well-formed, `fileHolds`); the loop `i := 2; i < pgid; i++`
appends the unreached ones, so the result is strictly increasing from 2 (4d's `Freelist.idsOk`,
what `Init`/`NoSyncReload` take) and a fresh slice (`append` from `nil`: its capacity owned, which
`Init` keeps); `Rollback`.

**Changes (integration I7).** The post was only `2 ≤ x < hwm`: it now gives `idsOk`, the slice's
capacity and `dbUnreached` (the ids are exactly the unreached pages), which 4d's `Init` and
`NoSyncReload` premises need (`Internal.lean`, "The freelist's side").
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

/-- (internal) the ids the current tree does not reach (strictly increasing from 2, below the
high-water mark), in a fresh slice. -/
def DB.freepages.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M ∗ ⌜M.metaOk = true⌝ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"freepages")) (Val #()))
  {{ (s : GoSlice), RET #s; dbRaw db γ M ∗
      ∃ ids : List go_etcd_io.bbolt.internal.common.Pgid, s ↦* ids ∗
        ownSliceCap go_etcd_io.bbolt.internal.common.Pgid s (DFrac.own 1) ∗ dbUnreached db γ ids ∗
        ⌜Freelist.idsOk ids ∧ ∀ x ∈ ids, uint.nat x < M.hwm⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
