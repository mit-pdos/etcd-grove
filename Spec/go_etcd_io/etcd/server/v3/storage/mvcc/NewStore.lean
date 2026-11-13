/-
`NewStore` (`kvstore.go`), on a real backend holding an image (B3; mvccfull's Freeze, 2026-11-10;
until then on a fresh backend). Lean-first (no Rocq counterpart); see
`InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RdCalls
public import Perennial.ProgramLogic.Bounds
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreSess

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

/-- **`NewStore(lg, b, le, cfg)` over a real backend `d` holding the image of `L' = [[], []] ++ R`
at the compaction records `r`** (B3; mvccfull's Freeze, 2026-11-10). Changes from the fresh spec, clause by clause:

* **The instance**: the real backend only (`kb = some d`): no caller uses mvcc's assumed backend
  (`StoreBackend.lean`'s `NewStore_backend` and `NewStoreApi.lean` are at `some _`; the server and
  the tester reach `NewStore` through the API). The hook value `f` is gone with it (`hookInit γ P f`
  ignores `f` at `some _`): the post has `hookP γ P`.
* **The backend's contracts** (`store.Restore`'s pattern, R1's restatement, 2026-11-09):
  - for the batch session, a contract at some deletable keys (`storeSessT`, deposit witness `True`);
  - at the records, behind the fix of the deletable keys' registration
    (`restoreFixM d γ -∗ storeBackendTR … r`).

  At `r = empty`, `storeBackendTR` is `storeBackendT` (`storeBackendTR_empty`). The registration is
  unfixed in the pre (`restoreRegM d`: on, `dlInit`; off, `True`), and `NewStore` fixes it itself.
  `γi` is the caller's.
* **The clean read** (`store.restore`'s `ns = false`): `keyCleanReadR` of the bucket's clean view at
  the records, lent a reader's token and the unfixed registration (`storeRT γ ∗ restoreRegM d`, as in
  `store.Restore`). `restore` gives the token back, and the registration is then fixed. Until R1's
  restatement, it was lent the caller's `RC` instead, the registration already fixed.
* **The image** (`restoreImageM d γb L' r`, `Restore`'s): in place of `kbView kb γb 1 ∅ ∗ kbNoCmp kb γb`.
  Off, the clean view of the whole log's bucket and no record; on, the clean view of the cut entries,
  the records with the compaction-key write right, the tracked values, the keys well formed.
* **The receipt** (`restoreRcptM d L'`, `Restore`'s): on, `⧖ (logCh L')` (the rebuild of a cut
  bucket cannot refill the writer's receipts); off, nothing.
* **The compaction permit** of the records (`crevPermAt`'s shape over the caller's `Perm`, which
  names the store's permit): the restored revisions are permitted.
* **The certificate of `L'`** (`certOk`'s shape over the caller's map `γok`, at any `M`, given back):
  a log longer than two is certified (or the map is free). Fresh: `L'.length ≤ 2`, `M = ∅`.
* **The lessor's owner part** (`restore`'s `ns = false`): `leaseOwn γl Ls ∅`, each restored item's
  lease live and its key short; back at `pendItems L' []`.
* **The resumed compaction** (`resumeCtxM`, `Restore`'s, with the write-back supply when it resumes).
* **Index and readers** unchanged in form: `idxFresh γi` (the proof grows its authorities to `L'`
  and `r.crev`), `nReaders` backend tokens in, `nReaders - nJobRd` reader slots out.

**Post**: `idxCert γ.idx L'`, `logQ γ L'`, `newClient γ.api L' r.crev`; the right to close by the mode
at the restored revision (`storeCloserM s γ r.crev`: on, the restorable compaction right, its queue
holding the resumed job if any; off, the closer) with, off, the compaction revision's half
(`crevUB γ.idx ½ (-1)`; off, `r = empty`); the lessor's owner part at `pendItems L' []`; the
resumed compaction's results (`resumeBackM`). Everything else as the fresh spec.

**The fresh spec** (until the Freeze; its statement at commit `ae30739dde`), whose clauses
the above changes: `NewStore(lg, b, le, cfg)` on a fresh backend `b` returns a store `s` (`isStore`) at the
initial committed log `[[], []]` (revision 0 and `currentRev = 1`, both empty), with its two
views (owned: `newWatchableStore` overwrites them), all the reader slots of its locks
(`storeReaderC`, one per slot) and the index's certificate of the initial log. The caller says whether the store is a
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
  (`storeCmp`: mvcc's assumed backend, and a real backend in compaction mode, `KBReal.cm`;
  question 5's core stage, part (4), 2026-10-29: until then the assumed backend only), and the batch lock's deposit witness its first `Unlock` returns.
* A `nil` logger is replaced by `zap.NewNop()`'s; of the configuration `cfg`, a zero
  `CompactionBatchLimit` is replaced by the default (1000): a negative one is excluded by the
  premise `0 ≤ cfg.CompactionBatchLimit` (`NewStore` keeps it, and the compaction job would
  loop forever: `nonissues/etcd-compaction-negative-batch-limit.md`), so `isStore`'s limit is
  positive.
* A quarter of the four fields `store.Restore` writes (`fieldShare`; D22 receiver epochs, S3,
  2026-10-22: until then `isStore` held them `↦□`, and `NewStore` returned the stop channel's,
  `storeStop`): the watchable store's share (`newWatchableStore` keeps it under its `s.mu`), and
  the right to close the store once (`storeCloser`, with another quarter:
  the channel's close, the scheduler's stop token and the compaction jobs' queue; D19m (C),
  2026-10-18: until then `NewStore` gave the stop token up for good, `isStore` holding
  `schedLive`, and `Close`'s contract was false). A compacting store's caller splits it into the
  restorable compaction right (`compactRightR_of_closer`; M2, the storage side, item 24).
* (D22 receiver epochs, S5a) The backend's reader tokens are in the readers' pool with the slots of
  the index's lock (`idxSlot`), not in the readers' handles; the watchable store's deposit ghost
  (`wsDep`) is returned for the watchable store's lock (`wsFields`).
* (D22 receiver epochs, S5b) The writer's fragment (`writerFrag`: an eighth of the store's current
  objects and physical names, at `γ`'s), for its sole writer (`hookIs`).
* (M2's item 37, 2026-11-02) The writer's pin at the initial log (`writerPin γ [[], []]`: its
  quarter of the bucket's view and, for a store that does not compact, the backend's
  no-compaction token, which `restore` gives back, and its nothing-deletable fact, the premise
  `kbNoDelOff kb`), for its sole writer's observations of a backend snapshot. (2026-11-06) It and
  the revision budget (`2 ^ 63 - 5` tokens) stay in the store, for both kinds (`wrState`, `wrPin`):
  a writer finds them after its checkout.
* The backend records no compaction (`kbNoCmp`, consumed by `restore`: D19l (v) (A), D22 S-g,
  2026-10-19; until then the opaque premise `backendNoCompaction`), so `restore` schedules none.
* Compaction (2026-10-13, unit 5a): the store starts at the compaction revision `-1`; the
  compaction right's half of that revision's authority is returned (`crevUB γ.idx ½ (-1)`; with
  the closer it makes the restorable compaction right `compactRightR s γ (-1)` that
  `store.Compact` takes, `compactRightR_of_closer`), and the reader slots are those of a
  store that may be compacted (`storeReaderC`): a caller that never compacts gives the half up
  (`crevFrozen_alloc`) and has the readers its transactions take (`storeReader_of`).
* (D22 receiver epochs, S8d, W7, 2026-10-25) The readers' pool's retired count (`retiredAt`): its
  creator counts the readers it retires, so that a restore returns exactly the old backend's tokens.
* (Question 5's wiring, the core stage, part (1), 2026-10-29; `notes/backend-cmp-plan.md`) The
  compaction mode is the instance's (`kbCmpM kb`: `KBReal.cm` for the real backend). A compacting
  real store keeps one of the backend's reader tokens back for its compaction job (`nJobRd kb`,
  out of the readers' pool: the pool's retired count starts there, and the caller gets that many
  fewer readers), and takes the backend's safe-range slot (`kbSRM`, from the backend's creation);
  the job's budgets travel in the compaction token
  (`compactTok`). For any other store they are `True` and nothing is kept back (`cmOff_res`). The
  contract is needed only at the index's names `γi` (F4: a compacting store's backend registers
  that index's deletable keys). (M2, the storage side, Q1 (a), 2026-10-30: the write-back supply
  `kbWTSupplyM` is no longer taken here: `store.Compact` takes it per compaction.)
* (M2, the storage side, item 26) The store's logical compaction mode (`γ.cm`) is the instance's
  (`decide (kbCmpM kb)`); a restore keeps it. 
The store's compaction permit is the caller's `Perm` (`crevPermIs`, C3's store law, 2026-11-02):
every compaction revision the store holds satisfies it. (M3, 2026-11-06) The store's registration in
its backend's batch lock (`writerReg`) and the client's parts of the API's ghost state
(`api.newClient`: the API's constructors' `mvccState`, `mvccOpen`'s quarter, the share token, the
location), and a later credit (the API's constructor retires a reader with it).
(the backend-auth-split stage, 2026-11-02) The backend's reader tokens it takes are the backend's
counted stock less the opener's two (`nReaders`, past the backend's pool), the readers it gives counted from it;
until then all `actualMaxReaders` of them. -/
abbrev mvcc.NewStore.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc) (wq : Bool)
    (γi : mvcc.IdxNames) (γok : GName) (M : GMap w64 mvcc.Log) (Perm : Int → IProp GF)
    (R : mvcc.Log) (r : mvcc.CmpRecs) (Ls : List w64)
    (hk : Option val) (Pre Q Post X Y : IProp GF) (dq : DFrac),
  {{ ⌜mvcc.batchLimitOk cfg.CompactionBatchLimit' ∧ mvcc.restoreLogOk R⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeSessT b s γ P) ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.restoreFixM d γ -∗ mvcc.storeBackendTR b s γ P r) ∗
      (∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanReadR b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d)
          (mvcc.kbRecs γ.kb γ.bucket r) r) ∗ mvcc.restoreRegM d ∗
      mvcc.restoreImageM d γb ([[], []] ++ R) r ∗ mvcc.restoreRcptM d ([[], []] ++ R) ∗
      mvcc.kbNoDelOff (some d) ∗ mvcc.kbRegRight (some d) ∗
      mvcc.kbWT (some d) ∗ mvcc.kbWT (some d) ∗ mvcc.kbSRM (some d) ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d)) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl Ls ∅ ∗
      ⌜∀ it lid, (mvcc.pendItems ([[], []] ++ R) []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 M ∗
      (⌜([[], []] ++ R).length ≤ 2⌝ ∨ (W64 (([[], []] ++ R).length : Int)) ↪[γok]□ ([[], []] ++ R) ∨
        (W64 0) ↪[γok]□ ([] : mvcc.Log)) ∗
      (⌜r.finRev = -1⌝ ∨ □ Perm r.finRev) ∗ (⌜r.crev = -1⌝ ∨ □ Perm r.crev) ∗
      mvcc.resumeCtxM d r P hk Pre Q Post dq X Y ∗
      (if r.resumes then mvcc.kbWTSupplyM (some d) else iprop(True)) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
      ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d ∧ γ.watchQ = wq ∧ γ.idx = γi ∧ γ.cok = γok ∧
        γ.cm = d.cm⌝ ∗
      mvcc.isStore s γ ∗
      (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdCalls rd (go.GoType.PointerType store.ty) #s) ∗
      ghostMapAuth γ.cok 1 M ∗ mvcc.hookP γ P ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        mvcc.isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - mvcc.nJobRd (some d)) (),
        mvcc.storeReaderC s γ) ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      (if wq then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      mvcc.storeCloserM s γ r.crev ∗
      (if d.cm then iprop(True) else mvcc.crevUB γ.idx (1 : Qp).half (-1)) ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗ mvcc.writerFrag γ ∗
      mvcc.retiredAt γ (mvcc.nJobRd (some d)) ∗
      mvcc.crevPermIs γ Perm ∗ mvcc.writerReg s γ ∗
      (∃ pr : Qp, ⌜mvcc.pndW γ + pr = 1⌝ ∗ mvcc.api.newClient γ.api ([[], []] ++ R) r.crev pr s) ∗
      lease.leaseOwn γl Ls (mvcc.pendItems ([[], []] ++ R) []) ∗
      mvcc.resumeBackM d r hk dq Post Y ∗ £ 1 }}

end spec

end EtcdGrove
end Perennial
