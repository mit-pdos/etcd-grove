/-
`tx.Rollback()` (`tx.go`): `nonPhysicalRollback`: a writer's freelist rollback, then `close`.

**Users.** The backend's read transactions (`batch_tx.go:393`, on its own goroutine after the
readers' wait group), `snapshot.Close` (`backend.go:1132`), defrag (`:807, 816, 875, 887, 967,
975`), `View` and `Update`. Snippets: `ReqBackendRead`, `ReqSnapshot`.

**Proof sketch.** Read: `removeTx` (under `mmaplock`'s read side: the slot returned to the pool,
hence the caller's `threadTok`; the transaction unregistered under `metalock`). Write: 4d's
`freelist.Rollback(txid)` (the pages this transaction allocated return to free), `close` (`rwlock`
released). The committed state is unchanged (no update).

**Changes.** Unchanged, but for `managed = false` (a managed transaction's `Rollback` panics).
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

/-- `tx.Rollback()` (not managed): the transaction ends with no effect; a reader's token comes
back. -/
def Tx.Rollback.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView),
  {{ boltTx (GF := GF) tx γ 1 T ∗ ⌜T.managed = false⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
  {{ RET #GoInterface.nil; txDone tx ∗ (if T.rw then emp else threadTok) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
