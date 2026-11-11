/-
`newWatchableStore` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`, `Spec/.../NewStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
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

/-- **`newWatchableStore(lg, b, le, cfg)` over a real backend `d` holding the image of
`L' = [[], []] ++ R` at the records `r`** (B3; mvccfull's Freeze, 2026-11-10). The pre is `NewStore.spec`'s (the call
`NewStore(lg, b, le, cfg)` at `wq = true`); the post is the fresh spec's with:
* the inner store's closer and the compaction revision's half by the mode
  (`storeCloser st γ.st ∗ crevRightM γ.st` → `storeCloserM st γ.st r.crev`: on, the restorable right
  at the restored revision, with the resumed job if any; off, the closer, `crevRightM` being `True`);
* the API's client parts at the restored state (`newClient γ.st.api L' r.crev ½ st`); the watchable
  store's lock holds the notified log `L'` (inside `isWatchableStore`, as the inner store's `logQ`);
* the certificate map at the caller's `M`, the hook's invariant `hookP` (no `f`), and, from
  `NewStore`, the lessor's owner part at `pendItems L' []` and `resumeBackM` (the registration
  fixed inside, R1's restatement: the pre is `NewStore.spec`'s).
The watchers' structures start empty as today (`synced`/`unsynced` empty at any `L'`: Go's
`newWatchableStore` makes them empty and only `restore()` has run).

**The fresh spec** (until the Freeze; its statement at commit `ae30739dde`), whose clauses
the above changes: `newWatchableStore(lg, b, le, cfg)` on a fresh backend (`NewStore`'s premises: the backend's
contract at any of the store's names with the bucket `γb`, the empty bucket's view, the lessor):
a watchable store (`isWatchableStore`: the inner store with its read view pointed at the
watchable store, the lock's guard with its invariant at the initial log `[[], []]`, no watcher,
the victims' wake-up channel, the stop channel), the post-lock hook recorded (2026-11-06: no sole
writer; the inner store keeps the revision tokens and the pin, the lock the whole notified log),
every watch token (`watchToks`: a registration costs one), every reader slot of the two stores' locks (`watchReader`), the right to close the
stop channel (`stopCloser`) and the inner store (`storeCloser`), and the zero wait group (for
`New`). The backend records no compaction (`kbNoCmp`, `NewStore`'s; D19l (v) (A), D22 S-g), and the inner store's closer holds its scheduler's stop token (D19m (C), 2026-10-18). The lessor's `SetRangeDeleter` takes the deleter closure as an opaque value (its later
calls of it are outside the model, as in `NewStore`). The index's names `γi` and the
certificate map's `γok` are the caller's, fresh, and the map's authority is handed back
(2026-10-16, D13a: the etcd server chooses them before `newRaftNode`, and its KV certificates'
invariant takes the authority). (M2, the storage side, P3, 2026-10-30) The inner store's compaction
revision is frozen only when the store does not compact (`isWatchableStore`'s `wsFrozenM`); in
compaction mode the caller gets the compaction right's half of the revision's authority
(`crevRightM γ.st`, `True` otherwise) beside the closer; the store's logical mode is the
instance's (`γ.st.cm`); and the write-back supply is no longer taken here (Q1 (a): `store.Compact`
takes it). (C3's store law, 2026-11-02) The store's compaction permit is the caller's `Perm`
(`crevPermIs`). (Track A, `New.spec`, 2026-11-06) `NewStore`'s write resource's registration, the
API's client parts but the lock's quarter of the pending revision (`newClient` at half: the client's
`mvccState` takes it) and a later credit.
(the backend-auth-split stage, 2026-11-02) The backend's reader tokens it takes are the backend's
counted stock less the opener's two (`nReaders`, past the backend's pool), the readers it gives counted from it;
until then all `actualMaxReaders` of them. -/
abbrev mvcc.newWatchableStore.spec : Prop :=
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

end spec

end EtcdGrove
end Perennial
