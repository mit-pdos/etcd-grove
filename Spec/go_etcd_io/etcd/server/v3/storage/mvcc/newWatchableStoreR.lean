/-
**DRAFT (B3, mvccfull's F1): the internal `newWatchableStore` on a backend that already holds
data.** Candidate restatement of `mvcc.newWatchableStore.spec` (`newWatchableStore.lean`), over
`NewStore.specR`'s premises (`NewStoreR.lean`). Scratch: not imported, not linked, not proved.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
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

/-- **`newWatchableStore(lg, b, le, cfg)` over a real backend `d` holding the image of
`L' = [[], []] ++ R` at the records `r`** (DRAFT, B3). The pre is `NewStore.specR`'s (the call
`NewStore(lg, b, le, cfg)` at `wq = true`); the post is `mvcc.newWatchableStore.spec`'s with:
* the inner store's closer and the compaction revision's half by the mode
  (`storeCloser st γ.st ∗ crevRightM γ.st` → `storeCloserM st γ.st r.crev`: on, the restorable right
  at the restored revision, with the resumed job if any; off, the closer, `crevRightM` being `True`);
* the API's client parts at the restored state (`newClient γ.st.api L' r.crev ½ st`); the watchable
  store's lock holds the notified log `L'` (inside `isWatchableStore`, as the inner store's `logQ`);
* the certificate map at the caller's `M`, the hook's invariant `hookP` (no `f`), and, from
  `NewStore`, the lessor's owner part at `pendItems L' []` and `resumeBackM` (the registration
  fixed inside, R1's restatement: the pre is `NewStore.specR`'s).
The watchers' structures start empty as today (`synced`/`unsynced` empty at any `L'`: Go's
`newWatchableStore` makes them empty and only `restore()` has run). -/
abbrev mvcc.newWatchableStore.specR : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc)
    (γi : mvcc.IdxNames) (γok γtag : GName) (M : GMap w64 mvcc.Log) (Perm : Int → IProp GF)
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
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧
        γ.st.kb = some d ∧ γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧ γ.st.cm = d.cm⌝ ∗
      mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ ∗
        mvcc.rdCalls rd (go.GoType.PointerType watchableStore.ty) #s) ∗ mvcc.hookP γ.st P ∗
      mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 M ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - mvcc.nJobRd (some d)) (),
        mvcc.watchReader s st γ) ∗
      (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc) ∗
      mvcc.storeCloserM st γ.st r.crev ∗
      mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd (some d)) ∗
      mvcc.crevPermIs γ.st Perm ∗
      typedPointsto (mvcc.wsWgAddr s) (zero_val sync.WaitGroup) (DFrac.own 1) ∗
      mvcc.writerReg st γ.st ∗
      mvcc.api.newClient γ.st.api ([[], []] ++ R) r.crev (1 : Qp).half st ∗
      lease.leaseOwn γl Ls (mvcc.pendItems ([[], []] ++ R) []) ∗
      mvcc.resumeBackM d r hk dq Post Y ∗ £ 1 }}

/-- **Today's `newWatchableStore.spec` as an instance**: as `NewStore.spec_of_specR`, not exact, for
the same reasons (the real backend only; the clean view; the backend in `specR`'s form, review
round 2's T2: the session contract, the contract at the witness `True` behind the fix, the clean
read lent the unfixed registration and that registration; the lessor's part lent; the image's
tracked values); the post exactly today's off (`storeCloserM_off`, `crevRightM_off`),
on with the compaction right at `-1` in place of `storeCloser ∗ crevRightM` (`NewApi` makes that
right at once). Stated as the corollary the callers would use; its proof is `h` at `R = []`,
`r = empty`, `M = ∅`, `Ls = []`, `hk = none`. **Its callers**: none outside the chain; `New` calls
`newWatchableStore` with its own pre's backend part unchanged (`New.lean`), so `New.spec_of_specR`'s
callers' glue (`NewStoreRCallers.lean`'s `backendC_newStoreR_pre`) is this one's. -/
theorem mvcc.newWatchableStore.spec_of_specR
    (h : mvcc.newWatchableStore.specR (GF := GF) (hG := hG))
    [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc)
    (γi : mvcc.IdxNames) (γok γtag : GName) (Perm : Int → IProp GF)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit') :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeSessT b s γ P) ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.restoreFixM d γ -∗ mvcc.storeBackendT b s γ P) ∗
      (∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanRead b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d)
          (mvcc.kbNoCmpF γ.kb γ.bucket)) ∗ mvcc.restoreRegM d ∗
      mvcc.restoreImageM d γb [[], []] mvcc.CmpRecs.empty ∗
      mvcc.kbNoDelOff (some d) ∗ mvcc.kbRegRight (some d) ∗ mvcc.kbWT (some d) ∗
      mvcc.kbWT (some d) ∗ mvcc.kbSRM (some d) ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d)) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl [] ∅ ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧
        γ.st.kb = some d ∧ γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧
        γ.st.cm = decide (mvcc.kbCmpM (some d))⌝ ∗
      mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ ∗
        mvcc.rdCalls rd (go.GoType.PointerType watchableStore.ty) #s) ∗
      mvcc.hookInit γ.st P #func.nil ∗
      mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - mvcc.nJobRd (some d)) (),
        mvcc.watchReader s st γ) ∗
      (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc) ∗
      mvcc.storeCloserM st γ.st (-1) ∗
      mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd (some d)) ∗
      mvcc.crevPermIs γ.st Perm ∗
      typedPointsto (mvcc.wsWgAddr s) (zero_val sync.WaitGroup) (DFrac.own 1) ∗
      mvcc.writerReg st γ.st ∗ mvcc.api.newClient γ.st.api [[], []] (-1) (1 : Qp).half st ∗
      lease.leaseOwn γl [] ∅ ∗ £ 1 }} := by
  sorry

end spec

end EtcdGrove
end Perennial
