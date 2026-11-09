/-
`(*watchableStoreTxnWrite).End()` (`watchable_store_txn.go`): commits the transaction's revision,
notifying the watchers first: the `TxnWrite` interface's `End` contract (3e's `Txn.End.contract`,
two steps) at the watchable transaction.

**Users.** Every write transaction's `End` (`txn.Txn`, `Put`, `DeleteRange`, the lessor's revoke
`lessor.go:361`). Snippet: `mvccwatch/store.go` `ReqStoreWrites`.

**Proof sketch.** `Changes()` (3e's `Txn.Changes`: the events as key-values; a delete's with
`CreateRevision` `0`, its `ModRevision` written here: the changes owned, `req/`). No change: the inner
`End` (both steps fire with nothing). Else the events built at `rev = Rev() + 1` (`evOf`: a delete's
`ModRevision` patched in; every event's revision is `rev`, so `notify`'s batch check holds), then
under `s.mu`: **the first update fires** (`σ.notify pend`; `mvccLb`'s authority gains revision
`rev`), `notify(rev, evs)` (its spec: each synced watcher of an event's key gets its filtered events,
or becomes a victim with them, its `minRev` past `rev`; the responses' facts against the new notified
history), the inner `End` (3e's: **the second update fires** at the bump, `commitPending`; the reader
token back), `s.mu.Unlock`.

**Changes** from `specs-ref`'s file: the canonical instance of 3e's restated contract.

**Margin.** As the contract's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `t.End` meets `Txn.End`'s contract. -/
def watchableStoreTxnWrite.End.spec : Prop := ∀ t : Loc, Txn.End.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t

end spec

end Mvcc
end EtcdGrove
end Perennial
