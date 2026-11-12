/-
`db.Begin(writable)` (`db.go`: `beginTx`/`beginRWTx`).

**Users.** `backend.unsafeBegin` (`backend.go:1103`: the batch's write transaction and the shared
read transaction), `backend.Snapshot` (`:386`), defrag (`:801, 812, 869, 883, 963, 969`), `View`
and `Update` (this file's siblings). Snippets: `ReqBackendBatch`, `ReqBackendRead`.

**Proof sketch.** Read: take `metalock`, then a reader slot of `mmaplock` (lent by the pool for the
caller's `threadTok`), check `opened` and `data != nil`; copy the current meta (the linearization
point: under `metalock`, which every commit's meta write holds, the meta is the one of `σ.data`:
open the client's update, read `σ`, close it with `Q σ.data`), register the transaction, release
`metalock`. Write: take `rwlock` (held until `close`), `metalock`, check, copy the meta with its
txid incremented, free the pages pending for no reader (4d's `freelist.ReleasePendingPages`; the
reader txids from the registered transactions), release `metalock`; the view is `TxView.wr D false ns`
with `D` the committed data (`boltTx_base` thereafter); the buckets' tokens are allocated (a ghost
map of `D.bktPaths` at `none`, its authority in `wtxCore`: `tx.root.buckets` is empty). An error: the database closed (or its mapping
lost by a failed remap in a failed commit, which recorded `brk` in its settling update:
`nonissues/bbolt-failed-remap-nil-meta-panic.md`), the slot and token given back, or `rwlock`
released.

**Changes.** Unchanged in shape; `boltState` is over `BoltSt` (the update reads `σ.data`); the view
records `managed = false` and the database's mode.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** A write transaction comes
with the whole token `bktOwn … none 1` of each bucket path of its data (`Ent.bktPaths`), in place of
the view's generations (the per-path generation counter it replaces was unobservable state,
redundant with ownership).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- `db.Begin(w)`, from any goroutine.
- **Read**: the caller lends its `threadTok` (the transaction's reader slot, until `Rollback`) and
  a read update, fired at the meta copy: the transaction reads the committed data `D` of that
  moment for its whole life.
- **Write**: blocks until no other write transaction is live, then begins at the committed `D`
  (`boltTx_base` relates it to the client's state), with the whole ownership of each of its
  buckets, none looked up yet (`bktOwn … none 1` for `D.bktPaths`).
- **Error** only if the database was closed (`dbClosed`: excluded by the close right,
  `boltOpened_closed`) or a failed commit lost its mapping (`dbBroken`: the client's state then
  says `broken`, `dbBroken_state`); no transaction; the token and the update come back. -/
def DB.Begin.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns w : Bool) (Q : Data → IProp GF),
  {{ isBolt (GF := GF) db γ ns ∗
      (if w then emp else iprop(threadTok ∗
        AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅
          <{ boltState γ q σ, COMM Q σ.data }>)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err);
      (⌜err = GoInterface.nil⌝ ∗ txDB tx db ∗ txLive tx 1 ∗ ∃ D : Data,
        (if w then iprop(boltTx tx γ 1 (TxView.wr D false ns) ∗ [∗list] p ∈ D.bktPaths, bktOwn tx γ p none 1)
         else iprop(boltTx tx γ 1 (TxView.ro D false ns) ∗ Q D))) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ (dbClosed db ∨ dbBroken γ) ∗
        (if w then emp else iprop(threadTok ∗
          AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅
            <{ boltState γ q σ, COMM Q σ.data }>))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
