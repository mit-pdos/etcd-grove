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
the base meta's freelist page (if synced) is freed by 4d's `Interface.Free` (`canFree`: the
current meta's freelist page is never free or pending, and was allocated by an earlier commit;
`Internal.lean`, "The freelist's side");
`commitFreelist` writes 4d's `freelist.Write` page; `grow` truncates (and syncs unless
`NoGrowSync`); `write` `pwrite`s every dirty page and `fdatasync`s (unless `NoSync`): none of these
pages is reachable from the current meta, so `boltFile γ`'s crash fact is untouched. Then
`writeMeta`: build the meta (txid `+1`, page `txid % 2`, 4d's `Meta.Write`/`Sum64`), take
`metalock`, and at the `pwrite`'s first step (one aligned OS page: OsFs's D9, all or nothing in
the page cache, not in a crash image) **fire the
commit update** with `ok` = whether the page was written, known from a prophecy resolved before
`metalock.Unlock` on the mapped meta page's txid being the new one (a prophecy patch,
`etc/proph-patches/bbolt/`; not on `err == nil`: OsFs's one-page write may write the page and
report an errno, and `WriteAt`'s `EINTR` retry may fail after a first attempt wrote it, 4c-D2): `ok` makes the new meta current for every
later reader (`metalock` keeps readers out until it is written) and every crash image's newest
valid meta the old or the new one (`BoltSt.commit`; for a crash image this needs decision 4c-D1's
sector rule, the user's open decision: (a) in OsFs's crash relation or (b) a crash premise); a failing write leaves the page cache unchanged
but a crash during it may still find the new meta (`BoltSt.attempt`). Release `metalock`;
`fdatasync` unless `NoSync`; **fire the settling update** (`synced`: the sync ran and succeeded;
`failed`: it failed, or the write reported an error after writing the page; `brk` false); `close`
(the stats under `statlock`, `rwlock` released). **On every error path both updates fire**: an
error before the meta write (`spill`, `grow`, `write`: errnos, an `allocate` past `MaxSize`)
fires the commit update with `ok = false` (`attempt`: an over-approximation, the pages are
unreachable) and the settling one with `failed` = whether an `fsync`/`fdatasync` failed (`grow`'s
`file.Sync`, `write`'s: a failed sync drops every dirty page of the file, D2, so `lost` must be
recorded: review S2) and `brk` = whether the mapping was lost (a failed remap: `db.data = nil`,
after which `Begin` fails); then `rollback` (4d's `freelist.Rollback`, `NoSyncReload` of
`freepages` on the spare reader slot), which after the meta write keeps the commit if its meta is
current (the fork's fix of etcd-io/bbolt#1311).

**Changes.** The old spec had one update (`D' = T.base` to `T.cur`) and no durability. Now the
update has two outcomes (committed, or attempted: what a crash may still find) and a second update
settles the durable state; both fire on every error (round 1: the error records a failed sync and a
lost mapping). A read transaction's `Commit` needs no update and returns `ErrTxNotWritable`, still
live (was a premise `T.rw`). Managed transactions are excluded (`Commit` panics on one).

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
the data unchanged), the **settling update** when the commit ends (`synced`: the meta page synced;
`failed`: a sync failed; `brk`: the mapping was lost). On success `ok`, `synced` unless `NoSync`,
no failure; on an error both fired too, with what they record. A read transaction:
`ErrTxNotWritable`, no update, still live. -/
def Tx.Commit.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (Q : Bool → IProp GF)
    (S : Bool → Bool → Bool → IProp GF),
  {{ boltTx (GF := GF) tx γ 1 T ∗ txLive tx 1 ∗ ⌜T.managed = false⌝ ∗
      (if T.rw then iprop(
        AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (ok : Bool), ⌜σ.data = T.base⌝ ∗
           boltState γ 1 (if ok then σ.commit T.cur T.noSync else σ.attempt T.cur T.noSync),
           COMM Q ok }> ∗
        AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (synced failed brk : Bool), boltState γ 1 (σ.settle synced failed brk),
           COMM S synced failed brk }>) else emp) }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Commit")) (Val #()))
  {{ (err : GoInterface), RET #err;
      if T.rw then iprop(txDone tx ∗
        ((⌜err = GoInterface.nil⌝ ∗ Q true ∗ S (!T.noSync) false false) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ ∃ ok synced failed brk : Bool, Q ok ∗ S synced failed brk)))
      else iprop(boltTx tx γ 1 T ∗ txLive tx 1 ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
