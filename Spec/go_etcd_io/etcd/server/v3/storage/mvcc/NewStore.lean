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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
and the index's certificate of the initial log. The caller says whether the store is a
watchable store's (`wq`, `γ.watchQ`, unit W-K); if so, it gets the outer quarter of the committed
log's authority (`logQ`), which the watchable store's `s.mu` keeps. The index's names `γi` and
the certificate map's `γok` are the caller's (fresh: `mvcc.idxFresh`, an empty map's authority,
handed back; 2026-10-16, D13a: the etcd server chooses them before `newRaftNode`).

* The backend is of the instance `kb` (2026-10-13, unit 5): `none`, mvcc's assumed contract over
  the store's own ghost map `γb`; `some d`, the real backend (`BackendBridge.lean`). Its contract
  is quantified over the store's ghost names and location (with that instance and bucket name),
  because the batch lock's resource `storeW s γ` is the store's (`writerRes s γ`, or the real
  backend's late-bound `lateW`, which `NewStore` registers at its first `tx.Unlock()` with the
  right `kbRegRight kb`).
* The fresh backend's view of the empty bucket `kbView kb γb 1 ∅` is *given* by the backend's
  creator (the fresh-backend assumption), as are the backend's reader tokens, one per reader
  slot (`kbRT kb`, lent to `NewStore`'s own calls and put in the readers' pool), and two
  write tokens (`kbWT kb`: the first `Unlock` and `ForceCommit`).
* The lessor's ghost name `γl` (its granted leases) is its own: the lessor exists before the
  store.
* The backend's batch lock has invariant `P`; the store records it (`hookInit`, returned) and,
  over mvcc's assumed backend, the post-lock hook `f` (any). Over the real backend the hook is
  the backend's slot, frozen when the etcd server installs it (`hookIs_of_init`; unit N4, D14b):
  the contract (`storeBackend`) names the slot, not the hook.
* The contract (`storeBackend`) includes the compaction's calls where the instance supports them
  (`storeCmp`: mvcc's assumed backend; the real backend's model does not, 2026-10-13, the merge
  with the compaction), and the batch lock's deposit witness its first `Unlock` returns.
* A `nil` logger is replaced by `zap.NewNop()`'s; of the configuration `cfg`, a zero
  `CompactionBatchLimit` is replaced by the default (1000): a negative one is excluded by the
  premise `0 ≤ cfg.CompactionBatchLimit` (`NewStore` keeps it, and the compaction job would
  loop forever: `issues/etcd-compaction-negative-batch-limit.md`), so `isStore`'s limit is
  positive.
* A quarter of the four fields `store.Restore` writes (`fieldShare`; D22 receiver epochs, S3,
  2026-10-22: until then `isStore` held them `↦□`, and `NewStore` returned the stop channel's,
  `storeStop`): the watchable store's share (`newWatchableStore` keeps it under its `s.mu`), and
  the right to close the store once (`storeCloser`, with another quarter:
  the channel's close, the scheduler's stop token and the compaction jobs' queue; D19m (C),
  2026-10-18: until then `NewStore` gave the stop token up for good, `isStore` holding
  `schedLive`, and `Close`'s contract was false). The caller that will not close the store gives
  the token up for the compaction right (`compactRight_of_closer`).
* (D22 receiver epochs, S5a) The backend's reader tokens are in the readers' pool with the slots of
  the index's lock (`idxSlot`), not in the readers' handles; the watchable store's deposit ghost
  (`wsDep`) is returned for the watchable store's lock (`wsFields`).
* (D22 receiver epochs, S5b) The writer's fragment (`writerFrag`: an eighth of the store's current
  objects and physical names, at `γ`'s), for its sole writer (`hookIs`).
* The backend records no compaction (`kbNoCmp`, consumed by `restore`: D19l (v) (A), D22 S-g,
  2026-10-19; until then the opaque premise `backendNoCompaction`), so `restore` schedules none.
* Compaction (2026-10-13, unit 5a): the store starts at the compaction revision `-1`; the
  compaction right's half of that revision's authority is returned (`crevUB γ.idx ½ (-1)`; with
  the closer's queue and the stop token given up it is the compaction right `compactRight γ (-1)`
  that `store.Compact` takes, `compactRight_of_closer`), and the reader slots are those of a
  store that may be compacted (`storeReaderC`): a caller that never compacts gives the half up
  (`crevFrozen_alloc`) and has the readers its transactions take (`storeReader_of`).
* (D22 receiver epochs, S8d, W7, 2026-10-25) The readers' pool's retired count, `0`
  (`retiredAt`): its creator counts the readers it retires, so that a restore returns exactly the
  old backend's tokens. -/
abbrev mvcc.NewStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (wq : Bool) (γi : mvcc.IdxNames) (γok : GName),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb⌝ → mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
      ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = kb ∧ γ.watchQ = wq ∧ γ.idx = γi ∧ γ.cok = γok⌝ ∗
      mvcc.isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookInit γ P f ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        mvcc.isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.storeReaderC s γ) ∗
      ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗
      (if wq then mvcc.logQ γ [[], []] else iprop(True)) ∗ mvcc.storeCloser s γ ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗ mvcc.writerFrag γ ∗
      mvcc.crevUB γ.idx (1 : Qp).half (-1) ∗ mvcc.retiredAt γ 0 }}

end spec

end EtcdGrove
end Perennial
