/-
**DRAFT (B3, mvccfull's F1): the internal `NewStore` on a backend that already holds data.**
Candidate restatement of `mvcc.NewStore.spec` (`NewStore.lean`), side by side with it, from the
fresh backend (`kbView kb γb 1 ∅ ∗ kbNoCmp kb γb`, `[[], []]`, `-1`) to any image `L' = [[], []] ++ R`
at compaction records `r`, in the vocabulary of `store.Restore`'s internal spec
(`restoreImageM`, `restoreRcptM`, `resumeCtxM`/`resumeBackM`, `storeCloserM`, `kbRecs`) and of
`store.restore.spec`'s `ns = false` branch (`keyCleanReadR`, the lessor's items). Go: `NewStore`
runs the same `s.restore()` as `store.Restore` (`kvstore.go:127-132`), after its own batch session
(`BatchTx`, `UnsafeCreateBucket`, `Unlock`, `ForceCommit`). Scratch: not imported, not linked,
not proved (`sorry`).

**NOT TO FREEZE BEFORE R1's LEMMA** (review round 1's F2.1). As written, the pre takes `RC` on its
own, the clean read lending `storeRT γ ∗ RC`, and the whole `restoreImageM d γb L' r`; but the only
`RC` its caller (`NewR.lean`'s glue, step 4) can supply is the evidence that nothing was deleted
since the open, the client's half `backend.dlsOwn d.γB ∅`, which is *inside* `restoreImageM` (on:
its `kbVals … ∅`). The caller cannot give both. What the bridge lemma must say (stated in
`NewR.lean` as `mvcc.NewStore.cleanRead_of_image`, `sorry`, Probe's target):

```
theorem mvcc.NewStore.cleanRead_of_image (hRT hrRL hrRU hrUR hID hName hSafe : backend's specs)
    (d : KBReal) (hP : bridgeParams d.P) (hcm : d.cm = true) (Pk) (γb) (γi) (r) (hpos : recsSign r) :
    isPkgInit backend ∗ isPkgInit schema ∗ isBackend d.γB d.P (lateW d.gx) Pk d.be ∗
      keySized d.γB d.P d.be ∗ storeDlReg d.γB γi ⊢
      ∀ γ : StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        keyCleanReadR (iface d.be) (bucketViewC γ) iprop(storeRT γ ∗ backend.dlsOwn d.γB ∅)
          (kbRecs γ.kb γ.bucket r) r
```

i.e. `keyCleanRead_of_backendC` with the registration already fixed (`storeDlReg`, which
`NewStore`'s batch session needs before `restore()`) and the client's deleted-entries half at `∅`
lent in place of the unfixed `dlInit`. Once it is proved, the restatement (the review's option (a)):
`RC` is no longer a parameter: the clean read's lent token is `storeRT γ ∗ (if d.cm then
backend.dlsOwn d.γB ∅ else True)`, the separate `RC ∗` leaves the pre and the post, and the proof
of `NewStore` splits the `dlsOwn` half off `restoreImageM` to lend it to `restore()`'s reads and
puts it back (the post's `storeCloserM`, on, takes the image's parts back as today). Off, nothing
changes (`keyCleanRead_of_backend` with `dlNoDel`, `r = empty`). If the lemma fails, the review's
option (b): the text is fixed to what Probe finds. `newWatchableStoreR.lean` and `NewR.lean` follow.
The API candidate (`ApiNewRestoring.lean`) is unaffected.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab

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
at the compaction records `r`** (DRAFT, B3). Changes from `mvcc.NewStore.spec`, clause by clause:

* **The instance**: the real backend only (`kb = some d`): no caller uses mvcc's assumed backend
  (`StoreBackend.lean`'s `NewStore_backend` and `NewStoreApi.lean` are at `some _`; the server and
  the tester reach `NewStore` through the API). The hook value `f` is gone with it (`hookInit γ P f`
  ignores `f` at `some _`): the post has `hookP γ P`.
* **The backend's contract** at the records (`isKeyBackendGR … (kbRecs γ.kb γ.bucket r) r …`, some
  deposit witness, at the store's names): at `r = empty` it is `storeBackend` (`isKeyBackendGR_empty`,
  `kbRecs_empty`). The deletable keys' registration is the caller's, fixed before the call (as today:
  `γi` is the caller's), not `Restore`'s `restoreFixM -∗` (see the clean read).
* **The clean read** (`store.restore`'s `ns = false`): `keyCleanReadR` of the bucket's clean view at
  the records, lent a reader's token and the caller's `RC`, which `restore` gives back (`RC` comes
  back in the post). Not `Restore`'s `storeRT ∗ restoreRegM d`: `NewStore` uses the contract (its
  batch session) *before* `restore()`, so the registration is fixed by then and the unfixed `dlInit`
  that `keyCleanRead_of_backendC` lends is gone (risk R1 of the report).
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
(`crevUB γ.idx ½ (-1)`; off, `r = empty`); the lessor's owner part at `pendItems L' []`; `RC`; the
resumed compaction's results (`resumeBackM`). Everything else as `mvcc.NewStore.spec`. -/
abbrev mvcc.NewStore.specR : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc) (wq : Bool)
    (γi : mvcc.IdxNames) (γok : GName) (M : GMap w64 mvcc.Log) (Perm : Int → IProp GF)
    (R : mvcc.Log) (r : mvcc.CmpRecs) (RC : IProp GF) (Ls : List w64)
    (hk : Option val) (Pre Q Post X Y : IProp GF) (dq : DFrac),
  {{ ⌜mvcc.batchLimitOk cfg.CompactionBatchLimit' ∧ mvcc.restoreLogOk R⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        ∃ Dep : IProp GF, mvcc.isKeyBackendGR b (mvcc.bucketView γ) (mvcc.storeRT γ)
          (mvcc.storeWT γ) (mvcc.kbRecs γ.kb γ.bucket r) r (mvcc.storePutOk γ) (mvcc.delKey γ)
          (mvcc.storeW s γ) (mvcc.kbWi γ.kb) Dep (mvcc.storeCmp γ) P (mvcc.hookFn γ)
          (mvcc.storeReq γ) (mvcc.storeRb γ) (mvcc.storeBt γ) (mvcc.kbSR γ.kb) (mvcc.kbSRh γ.kb)
          (mvcc.kbMWv γ.kb γ.bucket) (mvcc.kbHookNilAt γ.kb)) ∗
      (∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanReadR b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ RC)
          (mvcc.kbRecs γ.kb γ.bucket r) r) ∗ RC ∗
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
      lease.leaseOwn γl Ls (mvcc.pendItems ([[], []] ++ R) []) ∗ RC ∗
      mvcc.resumeBackM d r hk dq Post Y ∗ £ 1 }}

/-- **Today's `NewStore.spec` as an instance** (`R = []`, `r = empty`, `M = ∅`, `hk = none`, the
lessor's part at `[]`), at the real backend, for the callers that hold what the general spec takes
more than the fresh one: NOT exact. The fresh pre lacks (i) the clean view (`kbView` there; a fresh
real backend's creator has it clean: `NewStoreApi` builds `bkView` from `bView … true`), (ii) the
clean read and its `RC` (from `keyCleanRead_of_backendC`, which needs `dlInit`: R1), (iii) the
lessor's owner part (`leaseOwn γl [] ∅`: the API's callers hold it, `NewLessor`'s post), (iv) the
compaction keys' tracked values and well-formedness of `restoreImageM` on (`kbVals`, `fkVM`: the
open's `fkCl` gives them, `bkNoCmp_fkV_of_fkCl`); and `kb = none` is not covered. The fresh post is
recovered off exactly (`storeCloserM_off`); on, the closer comes as the compaction right at `-1`
(`storeCloserM_on`) in place of `storeCloser ∗ crevUB ½ (-1)`, which every on-caller turns into that
right at once (`compactRightR_of_closer`: `NewStoreApi`, `NewApi`). So the instance is stated with
those premises added and that post: the callers migrate to it (or to `specR`). -/
theorem mvcc.NewStore.spec_of_specR (h : mvcc.NewStore.specR (GF := GF) (hG := hG))
    [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc) (wq : Bool)
    (γi : mvcc.IdxNames) (γok : GName) (Perm : Int → IProp GF) (RC : IProp GF)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit') :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      -- (added) the clean read, lent `RC`
      (∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanRead b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ RC)
          (mvcc.kbNoCmpF γ.kb γ.bucket)) ∗ RC ∗
      -- (changed) the clean view of the empty bucket, no record (`restoreImageM` at the empty log)
      mvcc.restoreImageM d γb [[], []] mvcc.CmpRecs.empty ∗
      mvcc.kbNoDelOff (some d) ∗ mvcc.kbRegRight (some d) ∗ mvcc.kbWT (some d) ∗
      mvcc.kbWT (some d) ∗ mvcc.kbSRM (some d) ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d)) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      -- (added) the lessor's owner part, lent
      lease.leaseOwn γl [] ∅ ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
      ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d ∧ γ.watchQ = wq ∧ γ.idx = γi ∧ γ.cok = γok ∧
        γ.cm = decide (mvcc.kbCmpM (some d))⌝ ∗
      mvcc.isStore s γ ∗
      (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdCalls rd (go.GoType.PointerType store.ty) #s) ∗
      ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookInit γ P #func.nil ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        mvcc.isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - mvcc.nJobRd (some d)) (),
        mvcc.storeReaderC s γ) ∗
      mvcc.idxCert γ.idx [[], []] ∗
      (if wq then mvcc.logQ γ [[], []] else iprop(True)) ∗
      -- (changed) by the mode: off, `storeCloser ∗ crevUB ½ (-1)` exactly; on, the right at `-1`
      mvcc.storeCloserM s γ (-1) ∗
      (if d.cm then iprop(True) else mvcc.crevUB γ.idx (1 : Qp).half (-1)) ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗ mvcc.writerFrag γ ∗
      mvcc.retiredAt γ (mvcc.nJobRd (some d)) ∗
      mvcc.crevPermIs γ Perm ∗ mvcc.writerReg s γ ∗
      (∃ pr : Qp, ⌜mvcc.pndW γ + pr = 1⌝ ∗ mvcc.api.newClient γ.api [[], []] (-1) pr s) ∗
      lease.leaseOwn γl [] ∅ ∗ RC ∗ £ 1 }} := by
  -- `h … d γb γl P rd0 wq γi γok ∅ Perm [] CmpRecs.empty RC [] none …`: `isKeyBackendGR_empty`,
  -- `kbRecs_empty` for the contract and `keyCleanReadR_empty` for the clean read; `restoreRcptM` of
  -- `[[], []]` is `⧖ 0` (`preceipt_zero`); `pendItems [[], []] [] = ∅` (`pendItems_start`);
  -- `CmpRecs.crev_empty`, `finRev = -1`, `resumes = false` (`resumeCtxM_no`, `resumeBackM_no`); the
  -- certificate's first disjunct; `hookP γ P ⊢ hookInit γ P _` at `γ.kb = some d`.
  sorry

end spec

end EtcdGrove
end Perennial
