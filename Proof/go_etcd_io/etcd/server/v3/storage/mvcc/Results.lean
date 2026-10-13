/-
The trust base of every result of the mvcc KV core so far: `#print axioms` of each theorem
of `Link.lean`, and of the model's main theorem (`LogLemmas.lean`); and the backend bridge
(`BackendBridge.lean`), linked with the backend's results (`mvcc_backend_bridge`). Built with
the rest; read its output to check it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchRecv
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.StoreBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Link

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

#print axioms Perennial.EtcdGrove.mvcc.Revision.wp_GreaterThan
#print axioms Perennial.EtcdGrove.mvcc.generation.wp_isEmpty
#print axioms Perennial.EtcdGrove.mvcc.generation.wp_walk
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_Less
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_isEmpty
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_findGeneration
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_get
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_put
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_tombstone
#print axioms Perennial.EtcdGrove.mvcc.wp_newTreeIndex
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_keyIndex
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_unsafeGet
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Get
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Put
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Tombstone
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_KeyIndex
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Insert
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_unsafeVisit
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Revisions
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_CountRevisions
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Range

/-! The revision encoding (`revision.go`): bucket keys of 17 bytes, 18 for a tombstone, through
encoding/binary's `BigEndian` (the trust boundary, two axioms: `binary.bigEndian.PutUint64.wp_proof`
and `binary.bigEndian.Uint64.wp_proof`, as in the server's results). -/
#print axioms Perennial.EtcdGrove.mvcc.wp_newBucketKey
#print axioms Perennial.EtcdGrove.mvcc.wp_NewRevBytes
#print axioms Perennial.EtcdGrove.mvcc.wp_isTombstone
#print axioms Perennial.EtcdGrove.mvcc.wp_IsTombstone
#print axioms Perennial.EtcdGrove.mvcc.wp_BucketKeyToBytes
#print axioms Perennial.EtcdGrove.mvcc.wp_RevToBytes
#print axioms Perennial.EtcdGrove.mvcc.wp_BytesToBucketKey
#print axioms Perennial.EtcdGrove.mvcc.wp_BytesToRev

/-! The read transactions (`kvstore_txn.go`): `Read` opens one at the committed log's last
revision with a snapshot of the bucket, `End` closes it. -/
#print axioms Perennial.EtcdGrove.mvcc.wp_newMetricsTxnRead
#print axioms Perennial.EtcdGrove.mvcc.storeTxnCommon.wp_FirstRev
#print axioms Perennial.EtcdGrove.mvcc.storeTxnCommon.wp_Rev
#print axioms Perennial.EtcdGrove.mvcc.store.wp_Read
#print axioms Perennial.EtcdGrove.mvcc.storeTxnRead.wp_End

/-! The read transaction's range (`kvstore_txn.go`): `Range` answers from the certified log at the
requested revision, reading the index then the bucket's snapshot; the trace's `Step` and
protobuf's `Unmarshal` are the trust boundary (two axioms). -/
#print axioms Perennial.EtcdGrove.mvcc.wp_sliceCapWithLimit
#print axioms Perennial.EtcdGrove.mvcc.storeTxnCommon.wp_rangeKeys
#print axioms Perennial.EtcdGrove.mvcc.storeTxnCommon.wp_Range

/-! The wrappers (`metrics_txn.go`, `kv_view.go`): the metrics wrapper's `Range` and `End`
(the promoted methods of `txnReadWrite` and `storeTxnRead` unfolded), and the store's
`readView`, a read transaction around each read (`traceutil.TODO` is an axiom). -/
#print axioms Perennial.EtcdGrove.mvcc.metricsTxnWrite.wp_Range
#print axioms Perennial.EtcdGrove.mvcc.metricsTxnWrite.wp_End
#print axioms Perennial.EtcdGrove.mvcc.readView.wp_FirstRev
#print axioms Perennial.EtcdGrove.mvcc.readView.wp_Rev
#print axioms Perennial.EtcdGrove.mvcc.readView.wp_Range
#print axioms Perennial.EtcdGrove.mvcc.store.wp_Rev

/-! The write transactions (`kvstore_txn.go`, `metrics_txn.go`, `kv_view.go`): `Write` opens one
under the batch lock, `Put`/`DeleteRange` append to the pending revision (the index's answers,
the bucket's puts, the lessor), `End` commits it under `s.revMu` and certifies the new log;
protobuf's `Marshal` and zap's `Error` are the trust boundary (axioms). -/
#print axioms Perennial.EtcdGrove.mvcc.wp_newMetricsTxnWrite
#print axioms Perennial.EtcdGrove.mvcc.store.wp_Write
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_put
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_Put
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_delete
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_deleteRange
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_DeleteRange
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_Range
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_End
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_Rev
#print axioms Perennial.EtcdGrove.mvcc.storeTxnWrite.wp_Changes
#print axioms Perennial.EtcdGrove.mvcc.metricsTxnWrite.wp_Put
#print axioms Perennial.EtcdGrove.mvcc.metricsTxnWrite.wp_DeleteRange
#print axioms Perennial.EtcdGrove.mvcc.writeView.wp_Put
#print axioms Perennial.EtcdGrove.mvcc.writeView.wp_DeleteRange

/-! The store's constructor (`kvstore.go`) on a fresh backend: the ghost state allocated, the
batch lock's resource deposited at its first `Unlock`, the locks initialized; zap's `NewNop`,
schedule's `NewFIFOScheduler`, `NewHashStorage`, schema's `UnsafeCreateMetaBucket` and `restore`
(the identity on a fresh backend) are the trust boundary (axioms). -/
#print axioms Perennial.EtcdGrove.mvcc.wp_NewStore

/-! The post-lock hook (2026-10-12, apply unit A): the backend's batch lock has invariant `P`
and runs the hook `f` right after `LockInsideApply` (`batchTxSpec`); `NewStore` records them
(`hookIs`), `store.Write` runs the hook on the caller's `Pre` by the caller's triple and returns
its `Q`, `End` takes `P` back, `writeView.Put`/`DeleteRange` take the critical-section contract
(`csContract`) and return `Post`. The results above are stated at any `P f`; the statements
before the hook are the instance `P := True`, `f` a no-op (`csContract_noHook`). A caller's
view of the hook agrees with the store's (`hookIs_agree_lc`, a later credit spent). -/
#print axioms Perennial.EtcdGrove.mvcc.csContract_noHook
#print axioms Perennial.EtcdGrove.mvcc.hookIs_agree_lc

/-! The model: what the index answers of a key at a revision is the state's key-value, and a
reader's range answer is its certified log's. -/
#print axioms Perennial.EtcdGrove.mvcc.kiGet_indexOf
#print axioms Perennial.EtcdGrove.mvcc.reader_range

/-! The watch guarantee (unit 3c, `WatchRecv.lean`): the client's receive on a stream's channel
(`wp_watch_receive`, a lemma about the Go receive, not a function of the package) yields, per
watcher, what it knows of the responses received for it (`watchRecvOk`); against any certified
log reaching their bound, their events are the filtered segments of the range's changes from the
watcher's first revision on, in revision order (`watchRecvOk_cert`), exactly those changes for a
watcher with no filters (`watchGuarantee_unfiltered`), each response's revision at or above its
events' and a response with events carrying the watcher's id (`watchRecvOk_revs`). -/
#print axioms Perennial.EtcdGrove.mvcc.wp_watch_receive
#print axioms Perennial.EtcdGrove.mvcc.watchRecvOk_cert
#print axioms Perennial.EtcdGrove.mvcc.watchGuarantee_unfiltered
#print axioms Perennial.EtcdGrove.mvcc.watchRecvOk_revs

/-! Compaction (unit 5a, 2026-10-13, `Compact.lean`): the pure model's theorems — a compacted
key index answers as the uncompacted one at or above the compaction revision
(`kiGet_kiCompact`), one compaction empties has no answer there (`kiGet_of_kiCompact_empty`),
compactions compose (`kiCompact_kiCompact`, `kiCompact_kiCompact_le`), compaction at `-1`
changes nothing (`kiCompact_neg`), compaction commutes with the writer's next event
(`kiCompactO_step`, `IdxCRep.step`), the compacted index answers as the uncompacted one
(`IdxCRep.kiAt`, `IdxCRep.rangeAt`), and what a read at or above the compaction revision names is
kept (`kiGet_avail`, `named_not_del`: under `NoDelPutAt`,
`issues/etcd-compaction-delete-then-put.md`). -/
#print axioms Perennial.EtcdGrove.mvcc.kiGet_kiCompact
#print axioms Perennial.EtcdGrove.mvcc.kiGet_of_kiCompact_empty
#print axioms Perennial.EtcdGrove.mvcc.kiCompact_kiCompact
#print axioms Perennial.EtcdGrove.mvcc.kiCompact_kiCompact_le
#print axioms Perennial.EtcdGrove.mvcc.kiCompact_neg
#print axioms Perennial.EtcdGrove.mvcc.kiCompactO_step
#print axioms Perennial.EtcdGrove.mvcc.IdxCRep.step
#print axioms Perennial.EtcdGrove.mvcc.IdxCRep.kiAt
#print axioms Perennial.EtcdGrove.mvcc.IdxCRep.rangeAt
#print axioms Perennial.EtcdGrove.mvcc.kiGet_avail
#print axioms Perennial.EtcdGrove.mvcc.named_not_del
#print axioms Perennial.EtcdGrove.mvcc.KeyDel_prefix
#print axioms Perennial.EtcdGrove.mvcc.kiAvail_kiCompact

/-! The compaction functions' results (units 5a-5c): the meta keys, the index's side (unit 5b),
the store's side (unit 5c: `Compact`, `updateCompactRev`, `compact` scheduling the job tracked on
the FIFO scheduler, the job `scheduleCompaction`, the barriers, `compactLockfree`), over mvcc's
assumed backend (`storeCmp`). The scheduler's `NewJob`/`job.Do`/`job.Name` are pending (`sorry`:
the request path's unit 4d), so every result that schedules a job rests on them; the job's
hasher is axiomatized (`kvHasher`'s generated instance, `sorry -- axiomatized type`). -/
#print axioms Perennial.EtcdGrove.mvcc.wp_UnsafeSetFinishedCompact
#print axioms Perennial.EtcdGrove.mvcc.wp_SetFinishedCompact
#print axioms Perennial.EtcdGrove.mvcc.wp_UnsafeSetScheduledCompact
#print axioms Perennial.EtcdGrove.mvcc.wp_SetScheduledCompact
#print axioms Perennial.EtcdGrove.mvcc.wp_UnsafeReadFinishedCompact
#print axioms Perennial.EtcdGrove.mvcc.wp_UnsafeReadScheduledCompact
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_doCompact
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_compact
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_keep
#print axioms Perennial.EtcdGrove.mvcc.store.wp_checkPrevCompactionCompleted
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Compact
#print axioms Perennial.EtcdGrove.mvcc.treeIndex.wp_Keep
#print axioms Perennial.EtcdGrove.schedule.wp_NewJob
#print axioms Perennial.EtcdGrove.schedule.job.wp_Do
#print axioms Perennial.EtcdGrove.schedule.job.wp_Name
#print axioms Perennial.EtcdGrove.mvcc.store.wp_compactBarrier
#print axioms Perennial.EtcdGrove.mvcc.store.wp_updateCompactRev
#print axioms Perennial.EtcdGrove.mvcc.store.wp_scheduleCompaction
#print axioms Perennial.EtcdGrove.mvcc.store.wp_compact
#print axioms Perennial.EtcdGrove.mvcc.store.wp_Compact
#print axioms Perennial.EtcdGrove.mvcc.store.wp_compactLockfree
/-! ## The backend meets mvcc (units 4 and 5, `BackendBridge.lean`, `StoreBackend.lean`)

mvcc's contract of its backend (`isKeyBackendG`) holds of the proved backend (`isBackend`, its
results linked: `backend/Link.lean`, resting on bbolt's key-value contract), for mvcc's
parameters (`bridgeParams`) and a post-lock hook set for good; the range read of the `Key`
bucket rests on the premise `keySized` (fewer than `2^62` entries; the order half of the
safe-range discipline is the backend's invariant). The store is generic in its backend's
instance (`StoreNames.kb`): `NewStore` over the real backend (`mvcc_NewStore_backend`) makes a
store of the real instance, over which every store result holds (`store.Write` restated:
`mvcc_store_Write_backend`, its write token the backend's write-back budget). The layers above
mvcc (txn and up) are generic in the instance too (unit 6: `txn.isKV` no longer pins
`γ.kb = none`; the apply thread's KV over the real backend: the server's `server_kv_backend`);
`notes/STATUS.md`, "Unit 5", "Unit 6". -/

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section bridge
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The bridge, linked**: `mvcc.isKeyBackendG_of_backend` with the backend's results
(`backend/Link.lean`) and schema's `bucket` methods' (mvcc's `Link.lean`). -/
theorem mvcc_backend_bridge {P : backend.BParams} (hP : mvcc.bridgeParams P)
    (γ : backend.BNames) (W Pk : IProp GF) (b : Loc) (f : GoFunc)
    (hf : f ≠ func.nil) (Del : GoString → IProp GF) (Cmp : Prop) (hC : ¬ Cmp) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend γ P W Pk b ∗ backend.plHookRO γ f ∗ mvcc.keySized γ P b ⊢
      mvcc.isKeyBackendG
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b)
        (mvcc.bkView γ) (mvcc.bkRTx γ P b) (backend.wbTok γ) mvcc.keyPutOk Del W W iprop(True) Cmp
        Pk #f :=
  mvcc.isKeyBackendG_of_backend backend.backend.wp_ConcurrentReadTx backend.backend.wp_ReadTx
    backend.backend.wp_BatchTx backend.backend.wp_ForceCommit backend.backend.wp_Size
    backend.backend.wp_SizeInUse backend.concurrentReadTx.wp_RLock
    backend.concurrentReadTx.wp_RUnlock backend.concurrentReadTx.wp_UnsafeRange
    backend.readTx.wp_RLock backend.readTx.wp_RUnlock backend.readTx.wp_UnsafeRange
    backend.batchTxBuffered.wp_LockInsideApply backend.batchTxBuffered.wp_LockOutsideApply
    backend.batchTxBuffered.wp_UnsafeSeqPut backend.batchTxBuffered.wp_Unlock
    backend.batchTxBuffered.wp_UnsafeRange backend.batchTxBuffered.wp_UnsafeCreateBucket
    schema.bucket.wp_ID schema.bucket.wp_Name schema.bucket.wp_IsSafeRangeBucket
    hP γ W Pk b f hf Del Cmp hC

end bridge

section store
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`NewStore` over the real backend, linked** (`mvcc.NewStore_backend` with `NewStore`'s
proof and the backend's results). -/
theorem mvcc_NewStore_backend (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF)
    (f : GoFunc) (hf : f ≠ func.nil) (hcfg : 0 ≤ sint.Z cfg.CompactionBatchLimit') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.lateReg d.gx ∗
        backend.wbTok d.γB ∗ backend.wbTok d.γB ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d⌝ ∗
        mvcc.isStore s γ ∗ mvcc.hookIs γ Pk #f ∗
        (∃ rv wv : Loc,
          s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv s γ ∗
          s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"WriteView"] ↦
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.writeView.ty) #wv : GoInterface) ∗
          mvcc.isWriteView wv s γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.storeReaderC s γ) ∗
        ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗ mvcc.storeCloser s ∗
        mvcc.storeStop s ∗ mvcc.compactRight γ (-1) }} :=
  mvcc.NewStore_backend mvcc.wp_NewStore backend.backend.wp_ConcurrentReadTx
    backend.backend.wp_ReadTx backend.backend.wp_BatchTx backend.backend.wp_ForceCommit
    backend.backend.wp_Size backend.backend.wp_SizeInUse
    backend.concurrentReadTx.wp_RLock backend.concurrentReadTx.wp_RUnlock
    backend.concurrentReadTx.wp_UnsafeRange backend.readTx.wp_RLock backend.readTx.wp_RUnlock
    backend.readTx.wp_UnsafeRange backend.batchTxBuffered.wp_LockInsideApply
    backend.batchTxBuffered.wp_LockOutsideApply backend.batchTxBuffered.wp_UnsafeSeqPut
    backend.batchTxBuffered.wp_Unlock backend.batchTxBuffered.wp_UnsafeRange
    backend.batchTxBuffered.wp_UnsafeCreateBucket schema.bucket.wp_ID schema.bucket.wp_Name
    schema.bucket.wp_IsSafeRangeBucket lg le cfg d hP γb γl Pk f hf hcfg

/-- **`store.Write` over the real backend, linked**. -/
theorem mvcc_store_Write_backend (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal)
    (hk : γ.kb = some d) (trace : Loc) (P Pre Q : IProp GF) (f : val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ backend.wbTok d.γB ∗
        ⌜trace ≠ null⌝ ∗ mvcc.hookIs γ P f ∗ Pre ∗
        □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
      (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.store.ty @!!
        go!"Write")) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite.ty) #mw);
        (∃ ilog : mvcc.Log, mvcc.isTxnWrite mw s γ ilog [] (W64 0) (W64 0) (W64 0)) ∗ Q }} :=
  mvcc.store_Write_backend mvcc.store.wp_Write s γ d hk trace P Pre Q f

end store

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.mvcc_backend_bridge
#print axioms Perennial.EtcdGrove.mvcc_NewStore_backend
#print axioms Perennial.EtcdGrove.mvcc_store_Write_backend
#print axioms Perennial.EtcdGrove.schema.bucket.wp_ID
#print axioms Perennial.EtcdGrove.schema.bucket.wp_Name
#print axioms Perennial.EtcdGrove.schema.bucket.wp_IsSafeRangeBucket
#print axioms Perennial.EtcdGrove.schema.bucket.wp_String
/-! The pure core of the range read: a safe `Key` bucket's range in a readers' state is the
bucket's range. -/
#print axioms Perennial.EtcdGrove.mvcc.rtRange_safe

/-! ## The compaction (units 5a-5c)

`store.Compact` with the compaction right at `c` (`compactRight`: half the compaction revision's
authority and the compaction jobs' queue on the store's FIFO scheduler, whose last job hands the
next one the index compactor's token): on success, the right at `rev`, a lower bound `rev` of the
compaction revision for every reader, and the job's channel, whose receive gives `compactDone`
(the compaction finished at `rev` or later, `compactedAt`, or interrupted by the store's `Close`
or a cancelled scheduler context); `ErrCompacted` (the barrier's channel) or `ErrFutureRev`
otherwise, the right unchanged. And what it means for readers: at a compaction revision `c`, a
read at a revision at or above `c` answers as the uncompacted store (`mvcc_rangeOutcomeC_ge`: the
read path's `rangeOutcomeC` is `rangeOutcome`, the answer from the certified log; below `c`,
`ErrCompacted`), with the pure model's `IdxCRep.kiAt`/`IdxCRep.rangeAt` (the compacted index
answers as the uncompacted one there) and `named_not_del` (what such a read names is not deleted
from the bucket, under `NoDelPutAt`). -/

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section compaction
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The store's compaction, linked** (`store.Compact`'s proof with its callees'). -/
theorem mvcc_store_Compact : mvcc.store.Compact.spec (GF := GF) (hG := hG) :=
  mvcc.store.wp_Compact

/-- **A read at or above the compaction revision is unchanged by compaction**: at the compaction
revision `c`, the outcome of a range read at a revision at or above `c` (`rangeRev rev ro.Rev`,
the read's revision) is the uncompacted store's (`rangeOutcome`: the answer from the certified
log, as with no compaction). -/
theorem mvcc_rangeOutcomeC_ge (r : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (c : Int)
    (endNil : Bool) (k e : GoString) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)
    (hc : c ≤ sint.Z (mvcc.rangeRev rev ro.Rev')) :
    mvcc.rangeOutcomeC (GF := GF) r err log rev c endNil k e ro ⊢
      mvcc.rangeOutcome r err log rev endNil k e ro := by
  iintro H
  iunfold mvcc.rangeOutcomeC at H
  icases H with (⟨%Hc, -, -⟩ | ⟨-, H⟩)
  · exfalso; omega
  · iexact H

end compaction

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.mvcc_store_Compact
#print axioms Perennial.EtcdGrove.mvcc_rangeOutcomeC_ge
