/-
`tx.Commit()` (`tx.go`): rebalance, spill, free the old freelist, write the new one (unless
`NoFreelistSync`), grow the file, write the dirty pages and `fdatasync`, write the meta page and
`fdatasync` (unless `NoSync`), close.

**Users.** The backend's batch commit (`batch_tx.go:291`: a failure is fatal; `Stats()` read after
it), `ForceCommit`/`Snapshot` (`backend.go:378, 382`), defrag (`backend.go:836, 855, 916, 941`),
`Update` (`db.go`). Snippets: `ReqBackendBatch`, `ReqBank`.

**Proof sketch.** The writer holds `rwlock` (its `boltTx`). `rebalance`/`spill` (internal: node
merges and splits, `allocate` of fresh pages from 4d's freelist or past the high-water mark, every
written page within its extent; D17's `splitThreshold` bound) build the new tree for `T.cur`;
`commitFreelist` writes 4d's `freelist.Write` page; `grow` truncates (and syncs unless
`NoGrowSync`); `write` `pwrite`s every dirty page and `fdatasync`s (unless `NoSync`): none of these
pages is reachable from the current meta, so `boltFile γ`'s crash fact is untouched. Then
`writeMeta`: build the meta (txid `+1`, page `txid % 2`, 4d's `Meta.Write`/`Sum64`), take
`metalock`, and at the `pwrite`'s first step (one aligned OS page: D9, all or nothing) **fire the
commit update** with `ok` = the write's outcome, known from a prophecy resolved by the `pwrite`'s
error (a prophecy patch, `etc/proph-patches/bbolt/`): `ok` makes the new meta current for every
later reader (`metalock` keeps readers out until it is written) and every crash image's newest
valid meta the old or the new one (`BoltSt.commit`); a failing write leaves the page cache unchanged
but a crash during it may still find the new meta (`BoltSt.attempt`). Release `metalock`;
`fdatasync` unless `NoSync`; **fire the settling update** (`synced`: the sync ran and succeeded;
`failed`: it failed); `close` (the stats under `statlock`, `rwlock` released). An error before the
meta write (`spill`, `grow`, `write`: errnos, an `allocate` past `MaxSize`) rolls back (4d's
`freelist.Rollback`, `NoSyncReload` of `freepages` on the spare reader slot) with neither update
fired; after it, `rollback` keeps the commit if its meta is current (the fork's fix of
etcd-io/bbolt#1311).

**Changes.** The old spec had one update (`D' = T.base` to `T.cur`) and no durability. Now the
update has two outcomes (committed, or attempted: what a crash may still find) and a second update
settles the durable state; mutations' views on a read transaction are allowed and its `Commit`
returns `ErrTxNotWritable`, the transaction still live (was a premise `T.rw`). Managed
transactions are excluded (`Commit` panics on one).

**Margin.** `StrictMode` (a client must not set it, `isBolt`); `OnCommit` handlers (left out). The
error's identity is not described for a write transaction.
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `tx.Commit()` (not managed). A write transaction commits `T.cur` by the client's two updates:
the **commit update** fires at the meta page write with its outcome (`ok`: committed; else attempted,
the data unchanged), the **settling update** when the commit ends (`synced`: the meta page synced).
On success both fired with `ok` and, unless `NoSync`, `synced`. On an error: both fired (the commit
took effect or not, as `ok` says), or neither. A read transaction: `ErrTxNotWritable`, still live. -/
def Tx.Commit.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (Q : Bool → IProp GF)
    (S : Bool → Bool → IProp GF),
  {{ boltTx (GF := GF) tx γ 1 T ∗ ⌜T.managed = false⌝ ∗
      AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (ok : Bool), ⌜σ.data = T.base⌝ ∗
           boltState γ 1 (if ok then σ.commit T.cur T.noSync else σ.attempt T.cur T.noSync),
           COMM Q ok }> ∗
      AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (synced failed : Bool), boltState γ 1 (σ.settle synced failed),
           COMM S synced failed }> }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Commit")) (Val #()))
  {{ (err : GoInterface), RET #err;
      if T.rw then iprop(txDone tx ∗
        ((⌜err = GoInterface.nil⌝ ∗ Q true ∗ S (!T.noSync) false) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗
           ((∃ ok synced failed : Bool, Q ok ∗ S synced failed) ∨
            (AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (ok : Bool), ⌜σ.data = T.base⌝ ∗
           boltState γ 1 (if ok then σ.commit T.cur T.noSync else σ.attempt T.cur T.noSync),
           COMM Q ok }> ∗
             AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (synced failed : Bool), boltState γ 1 (σ.settle synced failed),
           COMM S synced failed }>)))))
      else iprop(boltTx tx γ 1 T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err ∗
        AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (ok : Bool), ⌜σ.data = T.base⌝ ∗
           boltState γ 1 (if ok then σ.commit T.cur T.noSync else σ.attempt T.cur T.noSync),
           COMM Q ok }> ∗
        AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (synced failed : Bool), boltState γ 1 (σ.settle synced failed),
           COMM S synced failed }>) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
