/-
`NewStore(lg, b, le, cfg)` (`kvstore.go:87-135`): a store without watchers over the storage `b`,
restored from what `b` holds.

**Users**: `newWatchableStore` (`watchable_store.go`, 3f: `mvcc.New`'s inner store, `server.go:366`);
etcd's tests and tools (`NewStore` is otherwise for testing). Snippets
`examples/specreq/mvcc/restore.go` (`ReqBoot`: a store over existing data, its leases re-attached, an
unfinished compaction resumed), `examples/specreq/mvcc/lease.go` (`ReqRangeDeleter`).

**Proof sketch**: `lg = nil` gives `zap.NewNop()`'s logger; the defaults of a zero `cfg`
(`storeCfgOk` kept); allocate the store, `newTreeIndex` (`ownIdxPriv`), `schedule.NewFIFOScheduler`
(`Schedule.isSched`, its open token, the tail `True`), `stopc`; `NewHashStorage`; the views; the
lessor's `SetRangeDeleter` (3c's `lessor.SetRangeDeleter.spec`: the writer token to
`{ls with rd := rd}`; `rd`'s triple is `KV.Write.contract`'s at `*store`, `mvccDeleter`, proved by
Löb once the handle exists).
`b.BatchTx()`, `LockOutsideApply` (`keyBackend`: `Pk`, `kbLocked B D` at the image), two
`UnsafeCreateBucket`s (`kbMade` of both buckets; a fresh `D` gets them, an existing one has them),
`Unlock` (`Pk` back; `kbData B D'`), `ForceCommit` (`storageReq_true`). `s.mu.Lock()`;
`s.restore()`: `setupMetricsReporter`; a shared `ReadTx` read (one of the store's reader slots,
`kbRdToks B mvccReaderN`) of the compaction keys and of the `Key` bucket in chunks
(`restoreChunk`, `restoreIntoIndex`: the private index rebuilt to the index of `h`, its revision
`h.rev` by `mvccImage D h u`, `currentRev` raised to the compaction keys'); each key's lease
`Attach`ed (`lessor.Attach.spec` on the writer token: `RestoreLs`; an `Attach` of a lease not live
fails and is logged); when `u`, `compactLockfree(scheduled)`: `updateCompactRev`'s
`SetScheduledCompact` runs the hook once (`LockInsideApply`, `hookRun Pk f Pre Q'`, then
`Q' ={⊤}=∗ Pk ∗ Post` for `Unlock`) and `ForceCommit` once (`X` to `Y`), and the job is scheduled
(`compactJobRes`, from `kbSafe B`, a reader slot and the job's receipts `⧖ (evCount h)` bound).
`idxShareC` publishes the index (`idxAt` at floor `0`); the invariants are allocated at `σ = ⟨h, []⟩` with the receipt;
the client gets `mvccState γ σ`, the open token, the whole backend share and the reader tokens
(`mvccTokN`: the store's slots but its own goroutines').

**Changes** from `specs-ref`'s `NewStore.lean` (a fresh, empty backend only, over the backend's
internal views and the store's ghost names, the watched mode `wq`, reader slots per reader):
**any image** (`mvccStorageFor B Pk h u`: a restart over existing data, an unfinished compaction
resumed), the state `⟨h, []⟩` the client's, the storage a contract (no backend names), the leases
re-attached on 3c's writer token (`RestoreLs`), the hook at any share (`nil` at boot: `server.go:409` sets it after
`mvcc.New`), no mode (clients hold only the stores the constructors return).

**Margin**: the store's metrics reporters are set (not stated); `lg`'s logging is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_uber_org.zap.Api

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

/-- **`NewStore(lg, b, le, cfg)`**: a store over the storage `B`, at the state `⟨h, []⟩` of the
image `B` holds (its open token, the whole backend share, its reader tokens, the client's state),
the lessor's writer token moved by the deleter's setting and the re-attachment, an unfinished compaction resumed (`u`: the hook once, the commit
once), and the range deleter set. -/
def NewStore.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : Loc) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (h : EtcdModel.KVHist) (u : Bool) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat)
    (ls : Lease.LessorState) (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ ⌜storeCfgOk cfg⌝ ∗
      mvccStorageFor B Pk h u ∗ ⌜MvccReachable ⟨h, []⟩⌝ ∗
      storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
      Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y ∗
      Lease.isLessor le γl c ∗ Lease.lessorState γl n ls }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(GoInterface.ok (storageVal B)))) (Val #(Lease.lessorIface le))) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : MvccName,
      isMvcc (interface.mkOk (go.GoType.PointerType store.ty) #s) γ ∗ mvccLessorIs γ γl ∗
      mvccState γ ⟨h, []⟩ ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccTokN ∗
      storageHook B dq f ∗ (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      ∃ (rd : GoFunc) (n' : Nat) (ls' : Lease.LessorState), mvccDeleter rd γ ∗
        ⌜RestoreLs { ls with rd := rd } h.store ls'⌝ ∗ Lease.lessorState γl n' ls' }}

end spec
end Mvcc
end EtcdGrove
end Perennial
