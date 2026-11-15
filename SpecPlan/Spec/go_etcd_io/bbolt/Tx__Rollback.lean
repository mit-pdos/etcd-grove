/-
`tx.Rollback()` (`tx.go`): `nonPhysicalRollback`: a writer's freelist rollback, then `close`.

**Users.** The backend's read transactions (`batch_tx.go:393`, on its own goroutine after the
readers' wait group), `snapshot.Close` (`backend.go:1132`), defrag (`:807, 816, 875, 887, 967,
975`), `View` and `Update`. Snippets: `ReqBackendRead`, `ReqSnapshot`.

**Proof sketch.** Read: `removeTx` (under `mmaplock`'s read side: the slot returned to the pool,
hence the caller's `threadTok`; the transaction unregistered under `metalock`: 4d's
`RemoveReadonlyTXID`, `R.erase txid`, which keeps `readersOk`). Write: 4d's
`freelist.Rollback(txid)` (`canRollback` from `boltTx`'s invariant, `Internal.lean`, "The
freelist's side"; `FLState.rollback`: the pages it freed are no longer pending, back in the
committed tree, and its allocations are forgotten: **not** returned to free, the pages it allocated
are leaked until the freelist is next reloaded, which only costs space; free pages are unchanged,
so the reload invariant holds), `close` (`rwlock` released). The committed state is unchanged (no
update).

A finished transaction (round 1, C5): `tx.managed` and `tx.db` read through `txDone`'s share
(`close` set `db = nil`): `ErrTxClosed`.

**Changes.** `managed = false` (a managed transaction's `Rollback` panics); a finished transaction
allowed (defrag's `defer tmptx.Rollback()`, `backend.go:807`, `875`, `975`).
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

/-- `tx.Rollback()`: a live transaction (not managed) ends with no effect and a reader's token
comes back; a finished one returns `ErrTxClosed` (defrag's deferred `Rollback` after `Commit`). -/
def Tx.Rollback.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (o : Option TxView),
  {{ (match o with
      | some T => iprop(boltTx (GF := GF) tx γ 1 T ∗ txLive tx 1 ∗ ⌜T.managed = false⌝)
      | none => txDone tx) }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
  {{ (err : GoInterface), RET #err; txDone tx ∗
      (match o with
       | some T => iprop(⌜err = GoInterface.nil⌝ ∗ (if T.rw then emp else threadTok))
       | none => isErr go_etcd_io.bbolt.errors.ErrTxClosed err) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
