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

/-! ## The backend meets mvcc (unit 4, `BackendBridge.lean`)

mvcc's contract of its backend (`isKeyBackendG`) holds of the proved backend (`isBackend`, its
results linked: `backend/Link.lean`, resting on bbolt's key-value contract), for mvcc's
parameters (`bridgeParams`) and a post-lock hook set for good; the range read of the `Key`
bucket rests on the premise `rangeSafe` (the safe-range discipline on the readers' states,
which the backend's invariant does not give). mvcc's store does not use this instance yet: it
assumes the instance without tokens (`isKeyBackend`) over its own view of the bucket
(`notes/STATUS.md`, "Unit 4"). -/

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
    (γ : backend.BNames) (W Pk : IProp GF) (b : Loc) (qo : Qp) (f : GoFunc)
    (hf : f ≠ func.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend γ P W Pk b ∗ backend.plHookRO γ f ∗ mvcc.rangeSafe γ P b ⊢
      mvcc.isKeyBackendG
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b)
        (mvcc.bkView γ) (mvcc.bkRT γ P b qo) (backend.wbTok γ) mvcc.bkPutOk W Pk #f :=
  mvcc.isKeyBackendG_of_backend backend.backend.wp_ConcurrentReadTx backend.backend.wp_ReadTx
    backend.backend.wp_BatchTx backend.backend.wp_ForceCommit backend.concurrentReadTx.wp_RLock
    backend.concurrentReadTx.wp_RUnlock backend.concurrentReadTx.wp_UnsafeRange
    backend.readTx.wp_RLock backend.readTx.wp_RUnlock backend.readTx.wp_UnsafeRange
    backend.batchTxBuffered.wp_LockInsideApply backend.batchTxBuffered.wp_LockOutsideApply
    backend.batchTxBuffered.wp_UnsafeSeqPut backend.batchTxBuffered.wp_Unlock
    backend.batchTxBuffered.wp_UnsafeRange backend.batchTxBuffered.wp_UnsafeCreateBucket
    schema.bucket.wp_ID schema.bucket.wp_Name schema.bucket.wp_IsSafeRangeBucket
    hP γ W Pk b qo f hf

end bridge

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.mvcc_backend_bridge
#print axioms Perennial.EtcdGrove.schema.bucket.wp_ID
#print axioms Perennial.EtcdGrove.schema.bucket.wp_Name
#print axioms Perennial.EtcdGrove.schema.bucket.wp_IsSafeRangeBucket
#print axioms Perennial.EtcdGrove.schema.bucket.wp_String
/-! The pure core of the range read: a safe `Key` bucket's range in a readers' state is the
bucket's range. -/
#print axioms Perennial.EtcdGrove.mvcc.rtRange_safe
