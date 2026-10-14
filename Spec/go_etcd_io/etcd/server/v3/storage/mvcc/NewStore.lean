/-
`NewStore` (`kvstore.go`), on a fresh backend. Lean-first (no Rocq counterpart); see
`InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `NewStore(lg, b, le, cfg)` on a fresh backend `b` returns a store `s` (`isStore`) at the
initial committed log `[[], []]` (revision 0 and `currentRev = 1`, both empty), with its two
views (owned: `newWatchableStore` overwrites them), all the reader slots of its locks
(`storeReaderC`, one per slot) and the revision budget (`2 ^ 63 - 5` tokens: the batch lock's
resource `writerRes` needs `ilog.length + ntok + 3 ≤ 2 ^ 63`, with the initial log of length 2),
and the index's certificate of the initial log.

* The backend is of the instance `kb` (2026-10-13, unit 5): `none`, mvcc's assumed contract over
  the store's own ghost map `γb`; `some d`, the real backend (`BackendBridge.lean`). Its contract
  is quantified over the store's ghost names and location (with that instance and bucket name),
  because the batch lock's resource `storeW s γ` is the store's (`writerRes s γ`, or the real
  backend's late-bound `lateW`, which `NewStore` registers at its first `tx.Unlock()` with the
  right `kbRegRight kb`).
* The fresh backend's view of the empty bucket `kbView kb γb 1 ∅` is *given* by the backend's
  creator (the fresh-backend assumption), as are the backend's reader tokens, one per reader
  slot (`kbRT kb`, lent to `NewStore`'s own calls and returned in the `storeReaderC`s), and two
  write tokens (`kbWT kb`: the first `Unlock` and `ForceCommit`).
* The lessor's ghost name `γl` (its granted leases) is its own: the lessor exists before the
  store.
* The backend's batch lock has invariant `P` and runs the post-lock hook `f` (`P f`, any); the
  store records them (`hookIs`, returned), for its writers.
* The contract (`storeBackend`) includes the compaction's calls where the instance supports them
  (`storeCmp`: mvcc's assumed backend; the real backend's model does not, 2026-10-13, the merge
  with the compaction), and the batch lock's deposit witness its first `Unlock` returns.
* A `nil` logger is replaced by `zap.NewNop()`'s; of the configuration `cfg`, a zero
  `CompactionBatchLimit` is replaced by the default (1000): a negative one is excluded by the
  premise `0 ≤ cfg.CompactionBatchLimit` (`NewStore` keeps it, and the compaction job would
  loop forever: `issues/etcd-compaction-negative-batch-limit.md`), so `isStore`'s limit is
  positive.
* The store's stop channel (`storeStop`) and the right to close the store once (`storeCloser`:
  the channel's close).
* Compaction (2026-10-13, unit 5a): the store starts at the compaction revision `-1`; the
  compaction right (`compactRight γ (-1)`, which `store.Compact` takes) is returned, and the
  reader slots are those of a store that may be compacted (`storeReaderC`): a caller that
  never compacts gives the right up (`compactRight_freeze`) and has the readers its
  transactions take (`storeReader_of`). -/
abbrev mvcc.NewStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val),
  0 ≤ sint.Z cfg.CompactionBatchLimit' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb⌝ → mvcc.storeBackend b s γ P f) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = kb⌝ ∗
      mvcc.isStore s γ ∗ mvcc.hookIs γ P f ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        mvcc.isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.storeReaderC s γ) ∗
      ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗ mvcc.storeCloser s ∗
      mvcc.storeStop s ∗ mvcc.compactRight γ (-1) }}

end spec

end EtcdGrove
end Perennial
