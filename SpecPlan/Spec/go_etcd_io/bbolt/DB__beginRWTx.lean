/-
`db.beginRWTx()` (`db.go`): `Begin(true)`: `rwlock`, the meta copy, `ReleasePendingPages`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch (the freelist, integration I7).** Under `rwlock` (`flOwn`) and `metalock`
(`flReaders fl R`, `R` the registered readers' txids), 4d's `Interface.ReleasePendingPages`:
`readersOk R` (each a committed txid, `≥ 1` by `fileHolds`, `< 2 ^ 63` by the file's bound plus
`Open`'s `2 ^ 62` receipts), `R.length < 2 ^ 62` (one per `threadTok`, `2 ^ 29`), `F.count <
flMaxIds` (ids below the high-water mark, `≤ 2 ^ 36`); every released page is `releasable` (no
registered reader's snapshot reaches it), which is what keeps every live read transaction's pages
unwritten; released pages are unreachable, so the reload invariant (`Internal.lean`, "The
freelist's side") is kept.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The buckets' whole tokens
(`bktOwn … none 1` for `D.bktPaths`), as `DB.Begin.spec`'s write arm (the per-path generation
counter it replaces was unobservable state, redundant with ownership).
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

/-- (internal) as `DB.Begin.spec` (write). -/
def DB.beginRWTx.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool),
  {{ isBolt (GF := GF) db γ ns }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"beginRWTx")) (Val #()))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); (⌜err = GoInterface.nil⌝ ∗ txDB tx db ∗ txLive tx 1 ∗ ∃ D, boltTx tx γ 1 (TxView.wr D false ns) ∗ [∗list] p ∈ D.bktPaths, bktOwn tx γ p none 1) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ (dbClosed db ∨ dbBroken γ)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
