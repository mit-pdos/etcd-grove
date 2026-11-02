/-
**M2, the storage side, step 2: restore in compaction mode (Draft)** (`notes/m2-storage-plan.md`,
"Step 2: restore in compaction mode"; the user's decisions after `lean`'s Stage P: three members, so
a lagging follower installs a snapshot while compaction runs). Imported by nothing but the server's
Draft of this step (`etcdserver/M2StorageDraftRestore.lean`); no `axiom`, no `sorry`; nothing
switched.

**Why today's statements exclude it** (the Probe's P4, `notes/spec-first-study/backend-probe.md`):
`compactRight_of_closer` *discards* the closer's share of the four fields `Restore` writes
(`storeStop`: `↦□`, the current objects' `curAt` and the restoring flag discarded) and the
scheduler's stop token (`schedLive`), because the compaction jobs read those fields without a lock
and the barrier jobs schedule untracked. `store.Restore` needs the fields whole and the stop token.

**The design drafted here: a compacting store keeps its closer.** What Go guarantees
(`kvstore.go:292-314`, `pkg/schedule/schedule.go:150-184`): `Restore` holds `s.mu`, closes `stopc`,
then `fifoSched.Stop()` returns only after the worker goroutine has run every pending job and exited
(`<-f.donec`); only then does `Restore` write `s.b`, `s.kvindex`, `s.fifoSched`, `s.stopc`. So a
job's reads of the fields only need a share that comes back when `Stop` returns:

- **The jobs' share of the fields** (`storeStopR`, persistent, in place of `storeStop` in
  `compactJobPre`): an invariant holding an eighth of the fields at the current objects, *or* the
  scheduler's run token (`schedDoneD`). A job runs with the run token (`schedule.jobIs`: `Do` with
  `schedRunning`), so while it runs the invariant holds the share and the job reads through it.
  `Scheduler.Stop` returns the run token (`schedule.Scheduler.Stop.specD`, drafted in
  `pkg/v3/schedule/M2StorageDraft.lean`: its post gains `schedDoneD γ`, the worker has exited), and the stopper swaps it in for the share (`storeStopR_reclaim`): the fields' share comes
  back without any job's cooperation, untracked barrier jobs included.
- **The compaction right keeps the closer** (`compactRightR`): the compaction revision's half, the
  jobs' queue, the closer's other eighth of the fields with the stop channel's close and the
  scheduler's stop token (`storeCloserR`), and the jobs' invariant. Made from today's closer by a
  split, not a discard (`compactRightR_of_closer`, in place of `compactRight_of_closer` /
  `compactRight_of_wsCloser`, which step 1's Draft no longer has); after `Stop`, the two eighths make the closer's quarter again
  (`fieldShare_reclaim`), so `Restore` (and `Close`) proceed as over today's closer, with the queue
  and the revision at `c` instead of `-1`.
- **No `schedLive`**: of the two untracked `Schedule`s, `updateCompactRev`'s `ErrCompacted` barrier
  runs inside `Compact`, which holds the right, hence the queue: it becomes a tracked job (passing
  the queue's token through). The barrier's re-schedule in `compactBarrier` (a cancelled context
  with `stopc` open) is dead: `Restore` and `Close` close `stopc` before `Stop` cancels the context
  (etcd PR 11817's order); `Scheduler.Stop` takes the scheduler's payload, which a job finding its
  context cancelled learns (review round 3's F2: `schedule/M2StorageDraft.lean`, the payload
  `schedPayIs`/`schedPay` and the job contract `jobDoSpecD`; the store's payload, its stop channel
  closed: `stopPayD`). (Not half the stop token in `s.mu`'s resource: `store.Close` does not take
  `s.mu`.)

**The statements** (`store.Restore.specM`, `watchableStore.Restore.specM`): the mode survives the
install (`d'.cm = d.cm`); by the mode, the store's right (`restoreRightM`: today's closer and
`crevFrozen` off; `compactRightR` at the revision `c` on), the received image (`restoreImageM`:
today's full bucket and no compaction record off; on, a bucket thinned at the revision `r.crev`
that `restore()` computes from the image's compaction records `r`, with the records' write right
`kbRecs`, `c ≤ r.crev`: review round 3's F1), the new job's budgets, the write-back supply and the
hook's contract for the compaction `restore()` resumes (`kbSRM`, `kbWTSupplyM` of `d'`,
`resumeHookM`: the new backend's unset hook, lent), the old job's budgets back
(`compactJobResM γ.kb`, for the old backend's `Close`), the new store's right
(`storeCloserM`). Also drafted: the generalized `store.restore` (`store.restore.specR`, item
18: switched and proved, 2026-10-30) and `store.Close` by the mode (`store.Close.specM`). At `cm = false` each reads as today: `store.Restore.spec_of_specM` and
`watchableStore.Restore.spec_of_specM` derive today's specs from the drafted ones.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InstanceLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/- (The jobs' share of the fields, `storeStopR` with its lease, `storeCloserR`, the restorable right
`compactRightR`, `compactRightR_of_closer` and `fieldShare_reclaim` are switched: `InvCompact.lean`,
the approval's items 17 and 24, 2026-10-30, with the lease of `notes/decisions.md`, "M2's storage
side: the jobs' share of the fields, leased".) -/

/-! ## By the mode -/

/- (`restoreRightM` and its laws are switched: `RestoreVocab.lean`, M2's item 15, step A3.) -/

/- (Round 3's `bucketThinnedAt`, any deletable subset missing, is replaced by the job's shape
`entsCutAt`, `M2StorageDraftIndex.lean`: `bucketThinnedAt_counterexample`, review round 4.) -/

/-! ## The compaction records (review round 3, F1) -/

/- (`CmpRecs` and its revision `crev`, `recsOk`, `recsPos`, `recsOk_crev_lt`, `recsPos_crev` are
switched: `CmpRecs.lean`, the approval's items 29 and 35.) -/

/- (`recBytes`, the merged compaction-key ghost `backend.fkVD`/`fkVM`/`fkOpenD`, `kbRecs` and its laws
are switched: `RestoreVocab.lean`, M2's item 15, step A3.) -/

/- (`CmpRecs.at` and the reader under records, `metaReadSpecR`, now over an optional record set, are
switched: `CmpRecs.lean`, item 28 with review round 5's S1. The drafts below read it at `some r`.) -/

/-! ## The backend vocabulary with the records (review round 4, A1 (a))

(`keyReadLockedR`, `keyReadSnapR`, `keyReadSnapCR`, `keyCleanReadR`, `isKeyBackendGR`, `restoreViewR`
are switched, the approval's item 27 with item 18, 2026-10-30: `RestoreRecs.lean`, beside today's;
`restoreViewR` over the records' resource `NC`, here `kbRecs … r`. `storeBackendTR` stays here: it
names `kbRecs`, the backend's part of item 29.) -/

/- (`storeBackendTR` is switched: `RestoreVocab.lean`, M2's item 15, step A3.) -/

/- (`bucketOfEnts` and `restoreViewR` are switched: `RestoreCut.lean`, `RestoreRecs.lean`.) -/

/-- At a real instance the records' resource is the backend's (`bkRecs`, `BackendRecs.lean`; the
Draft's `fkOpenD` of the records' bytes is `fkOpen … (recsVals r)` by definition). -/
theorem mvcc.kbRecs_some (d : mvcc.KBReal) (γb : GName) (r : mvcc.CmpRecs) :
    mvcc.kbRecs (GF := GF) (some d) γb r = mvcc.bkRecs d.γB r := by
  unfold mvcc.kbRecs mvcc.bkRecs
  split
  · rfl
  · rfl

/-- **The records' clean read of a compacting real backend** (the statement of the bridge law the
walk needs, A1 (a); restated after the plan's item 30 repairs and **proved**, 2026-10-30:
`mvcc.keyCleanRead_of_backendC`, `BackendRecs.lean`): `keyCleanRead_of_backend`'s, with the new
backend's registration not yet fixed (`dlInit`, lent with the reader's token: D1, the read's
exactness from `dlInit_noDel`; until then over `storeDlReg`, refutable) and the records being
revisions (`recsSign`, from `restoreImageM`'s `recsOk`: D2), the clean read at the records `r` its
client's flag stands at since the open (`kbRecs`). -/
def mvcc.keyCleanRead_of_backendC_stmt : Prop :=
  ∀ (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (Pk : IProp GF) (γb : GName)
    (r : mvcc.CmpRecs), mvcc.recsSign r →
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ⊢
      ∀ (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d⌝ →
        mvcc.keyCleanReadR
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ backend.dlInit d.γB)
          (mvcc.kbRecs γ.kb γ.bucket r) r

theorem mvcc.keyCleanRead_of_backendC_holds :
    mvcc.keyCleanRead_of_backendC_stmt (GF := GF) (hG := hG) := by
  intro hRT hrRL hrRU hrUR hID hName hSafe d hP Pk γb r hpos
  iintro H %γ %hγ
  rw [hγ.2, mvcc.kbRecs_some]
  iapply mvcc.keyCleanRead_of_backendC hRT hrRL hrRU hrUR hID hName hSafe d hP Pk γb r hpos $$ H
  ipureintro; exact hγ

/- (`restoreRegM`, `restoreFixM` and their laws are switched: `RestoreVocab.lean`, M2's item 15,
step A3.) -/

/- (`keyImageM` and `keyImageM_off` moved to `RestoreImageOpen.lean`, M2's item 15, stage B2a.) -/

/- (`restoreImageM` is switched: `RestoreVocab.lean`, M2's item 15, step A3.) -/

/-- **A compacted image's receipts** (draft, review round 4: a premise the evidence of A1 found):
on, the restored log's changes below the receipts' bound. `restore()` rebuilds the index in one
step per *surviving* entry (`revProt`'s `⧗ ents.length`), fewer than the log's changes once a
compaction deleted some, so the index writer's receipt per change (`idxWriter`'s
`⧗ (logCh ilog)`, D19b) cannot be refilled by the rebuild: the bound must come from the caller (the
apply side: the committed log's), and the writer's handle count receipts from it (internal; Q8). -/
def mvcc.restoreBoundM (d' : mvcc.KBReal) (L : mvcc.Log) : Prop :=
  d'.cm = true → mvcc.logCh L < receiptBound GF

/-! ## The resumed compaction's lock: the new backend's hook is not set yet (review round 4, A2)

`restore()` resumes a scheduled compaction (`compactLockfree` → `updateCompactRev` →
`SetScheduledCompact`, whose `LockInsideApply` runs the post-lock hook if one is set) inside
`kv.Restore`, and the server sets the new backend's hook only after `Restore` returns
(`server.go:1089-1093`; the walk: `hRst` at `SnapApplyWalk.lean:400`, `hSTP` at `:428`). So the
resumed lock runs no hook (`batch_tx.go:111-122`): the backend spec's nil arm
(`batchTxBuffered.LockInsideApply.spec`: `f = func.nil ∗ (Pk ∗ Pre -∗ Q)`). The caller lends the
client's half of the unset hook (`kbHookNil`, the walk's `plHook γB func.nil` until `hSTP`), given
back: no contract with the server's apply is needed, the batch lock's invariant `P` passes through
the critical section unchanged (`lockNilSpec`: `LockInsideApply` gives `P` itself, which the
`Unlock` takes back). -/

/- (`kbHookNil` (`InvStore.lean`), `lockNilSpec` as `batchTxSpecG`'s clause with `HN := kbHookNil kb`
(`InvStore.lean`), and `bt_lockInNil` (`BackendBridge.lean`, the bridge's proof of the clause) are
switched, item 31's rest, 2026-10-30.) -/

/- (`resumeHookM` is switched, item 31's rest, 2026-10-30: `RestoreRecs.lean`.) -/

/-- A real backend's mode is its record's. -/
theorem mvcc.kbCmpM_some_iff (d : mvcc.KBReal) : mvcc.kbCmpM (some d) ↔ d.cm = true := Iff.rfl

/-! ## `store.Restore` in either mode -/

/- (`store.Restore.specM` and `spec_of_specM` are superseded by the switched `store.Restore.spec`,
M2's item 15, step A3, which is `specM` with the receipt `restoreRcptM` and the two permits; off, it
reads as before, `r = CmpRecs.empty`.) -/

/- (`cmOff_true` is switched: `RestoreVocab.lean`.) -/

/-! ## `watchableStore.Restore` in either mode -/

/- (`watchableStore.Restore.specM` is switched: `watchableStore.Restore.spec`, with the receipt and the
permits as `store.Restore`'s, M2's item 15, step A3; `spec_of_specM` is `specOff_of_spec`,
`RestoreOff.lean`.) -/

/-! ## The watchable store's closer in compaction mode -/

/- (`wsCloserR` and `wsCloserR_of_wsCloser` are switched: `WsCloserR.lean`, the approval's item 20.) -/

/-- **The watchable store's closer and the inner store's restore right, by the mode** (draft): what
`watchableStore.Restore.specM` takes besides the store (`restoreRightM`) and what the watchable store
keeps (its stop channel's close, its waiter), split. -/
theorem mvcc.wsCloserR_split (s st : Loc) (γs : mvcc.StoreNames) (c : Int) (h : mvcc.kbCmpM γs.kb) :
    mvcc.wsCloserR (GF := GF) s st γs c ⊢
      mvcc.restoreRightM st γs c ∗
        (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s) := by
  iintro Hcl
  icases (mvcc.wsCloserR_iff s st γs c).1 $$ Hcl with ⟨%stc, #Hstc, Hsc, Hw, Hr⟩
  isplitl [Hr]
  · iapply (mvcc.restoreRightM_on st γs c h).2; iexact Hr
  iexists stc
  iframe Hstc Hsc Hw

/-- And back, after `Restore` (at the new names). -/
theorem mvcc.wsCloserR_join (s st : Loc) (γs : mvcc.StoreNames) (c : Int) (h : mvcc.kbCmpM γs.kb) :
    mvcc.storeCloserM (GF := GF) st γs c ∗
        (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s) ⊢
      mvcc.wsCloserR s st γs c := by
  iintro ⟨Hr, ⟨%stc, #Hstc, Hsc, Hw⟩⟩
  ihave Hr := (mvcc.storeCloserM_on st γs c h).1 $$ Hr
  iapply (mvcc.wsCloserR_iff s st γs c).2
  iexists stc
  iframe Hstc Hsc Hw Hr

/- (The store's payload for its scheduler, `stopPay`/`stopPayAt`/`stopPayAt_done`, and the logical
mode `StoreNames.cm` with `physOk`'s tie are switched: `InvStore.lean`, the approval's items 34 and
26, 2026-10-30. `restoreRightM`/`storeCloserM` below still read `kbCmpM γ.kb`, as drafted: at
their switch, with item 15, they read the logical mode `γ.cm`, equal under `physOk`'s tie.) -/

/- (The records reads, `UnsafeReadFinishedCompact`/`UnsafeReadScheduledCompact` over the records,
are switched as one spec each over an optional record set: item 28, review round 5's S1.) -/

/-! ## `store.restore`, generalized (item 18)

Switched and proved (2026-10-30, `notes/m2-storage-plan.md`, "The restore chain, mvcc part"):
`store.restore.spec` is the drafted `specR` (over the records' resource `NC` in place of `kbRecs`, the
lock's ghost part at the restored level `idxLockGAt` in place of `idxLockG ∗ crevLb`), proved in
`store__restore.lean`; `revFinW`, `restoreDone`, `resumeK` are in `RestoreRecs.lean`, today's text is
`store.restore.specNC` (`RestoreNC.lean`, `specNC_of_spec`). -/

/- (`store.Close.specM` is switched: `store.Close.spec`, the approval's item 23.) -/

end draft

end EtcdGrove
end Perennial
