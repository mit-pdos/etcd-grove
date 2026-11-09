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
with `D` the committed data (`boltTx_base` thereafter). An error: the database closed (or its mapping
lost by a failed remap: `nonissues/bbolt-failed-remap-nil-meta-panic.md`), the slot and token given
back, or `rwlock` released.

**Changes.** Unchanged in shape; `boltState` is over `BoltSt` (the update reads `σ.data`); the view
records `managed = false` and the database's mode.
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

/-- `db.Begin(w)`, from any goroutine.
- **Read**: the caller lends its `threadTok` (the transaction's reader slot, until `Rollback`) and
  a read update, fired at the meta copy: the transaction reads the committed data `D` of that
  moment for its whole life.
- **Write**: blocks until no other write transaction is live, then begins at the committed `D`
  (`boltTx_base` relates it to the client's state).
- **Error** (the database closed): no transaction; the token and the update come back. -/
def DB.Begin.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns w : Bool) (Q : Data → IProp GF),
  {{ isBolt (GF := GF) db γ ns ∗
      (if w then emp else iprop(threadTok ∗
        AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅
          <{ boltState γ q σ, COMM Q σ.data }>)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err);
      (⌜err = GoInterface.nil⌝ ∗ txDB tx db ∗ ∃ D : Data,
        (if w then boltTx tx γ 1 (TxView.wr D false ns)
         else iprop(boltTx tx γ 1 (TxView.ro D false ns) ∗ Q D))) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗
        (if w then emp else iprop(threadTok ∗
          AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅
            <{ boltState γ q σ, COMM Q σ.data }>))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
