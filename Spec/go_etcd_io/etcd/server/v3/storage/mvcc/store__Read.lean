/-
`(*store).Read(mode, trace)` (`kvstore_txn.go:46`): a read transaction.

**Users**: through `KV.Read` on the server's watchable store (promoted): `txn.Range`
(`txn/range.go:53`), `txn.Txn`'s read-only path (`txn/txn.go:60`, then `NewReadOnlyTxnWrite`), the
views (`readView.Range/Rev/FirstRev`), the tester's readers (`examples/mvccrand/mvccrand.go:625`).
Snippets `examples/specreq/mvcc/store.go` (`ReqReadFloor`, `ReqReadOnlyTxn`).

**Proof sketch**: `s.mu.RLock()` (a slot the reader token carries), `s.revMu.RLock()`;
`s.b.ConcurrentReadTx()`, or `s.b.ReadTx()` then `tx.RLock()` (`keyBackend`: the token's storage
slot; the snapshot `D` of `kbData`, which the store's invariant keeps at the image of the committed
history while `s.revMu` is held); read `compactMainRev`, `currentRev` and fire the caller's update at
`σ` (the invariant's state: `D` is `σ.kv`'s image, `currentRev = σ.rev`); `s.revMu.RUnlock()`;
`newMetricsTxnRead` over the `storeTxnRead` (`storeTxnR`), whose `mvccTxn t γ trace (.read σ)` keeps
`s.mu`'s read slot and `kbRead` until `End`.

**Changes** from `specs-ref`'s `store__Read.lean`: the contract `KV.Read.contract` at `*store`
(the frozen API's canonical spec), over W0's history; no certificates, revision tokens, tags or
callbacks.

**Margin**: none (the state cannot change before `End` because writers wait for `s.mu`; the
transaction's `mvccTxn` records it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Read`'s contract at `*store`. -/
def store.Read.spec : Prop :=
  ∀ s : Loc, KV.Read.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
