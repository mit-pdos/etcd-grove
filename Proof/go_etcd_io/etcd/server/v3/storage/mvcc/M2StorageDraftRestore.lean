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
  `Scheduler.Stop` returns the run token (drafted: its post gains `schedDoneD γ`, the worker has
  exited), and the stopper swaps it in for the share (`storeStopR_reclaim`): the fields' share comes
  back without any job's cooperation, untracked barrier jobs included.
- **The compaction right keeps the closer** (`compactRightR`): the compaction revision's half, the
  jobs' queue, the closer's other eighth of the fields with the stop channel's close and the
  scheduler's stop token (`storeCloserR`), and the jobs' invariant. Made from today's closer by a
  split, not a discard (`compactRightR_of_closer`, in place of `compactRight_of_closer` /
  `compactRight_of_wsCloser`); after `Stop`, the two eighths make the closer's quarter again
  (`fieldShare_reclaim`), so `Restore` (and `Close`) proceed as over today's closer, with the queue
  and the revision at `c` instead of `-1`.
- **No `schedLive`**: of the two untracked `Schedule`s, `updateCompactRev`'s `ErrCompacted` barrier
  runs inside `Compact`, which holds the right, hence the queue: it becomes a tracked job (passing
  the queue's token through). The barrier's re-schedule in `compactBarrier` (a cancelled context
  with `stopc` open) is dead: `Restore` and `Close` close `stopc` before `Stop` cancels the context
  (etcd PR 11817's order); drafted, `Scheduler.Stop` takes a persistent payload that a job finding
  its context cancelled learns (the store's: its stop channel closed). Not written in Lean here
  (internal to mvcc and `schedule`); listed in the plan. (Not half the stop token in `s.mu`'s
  resource: `store.Close` does not take `s.mu`.)

**The statements** (`store.Restore.specM`, `watchableStore.Restore.specM`): the mode survives the
install (`d'.cm = d.cm`); by the mode, the store's right (`restoreRightM`: today's closer and
`crevFrozen` off; `compactRightR` at the revision `c` on), the received image (`restoreImageM`:
today's full bucket and no compaction record off; a bucket thinned at the image's compaction
revision `c'` on, `c ≤ c'`), the new job's budgets and the write-back supply for the compaction
`restore()` resumes (`kbSRM`, `kbWTSupplyM` of `d'`), the old job's budgets back
(`compactJobResM γ.kb`, for the old backend's `Close`), the new store's right
(`restoreRightPostM`). At `cm = false` each reads as today: `store.Restore.spec_of_specM` and
`watchableStore.Restore.spec_of_specM` derive today's specs from the drafted ones.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraft

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

/-! ## The scheduler's exit -/

/-- **The worker has exited** (drafted for `schedule`, exclusive): the scheduler's run token's ghost
part (`schedRunning`'s `dghostVar γ.run 1 ()`, without the worker's thread token). Drafted:
`Scheduler.Stop.spec`'s post gains it (`<-f.donec` returns after `run`'s deferred `close(f.donec)`,
once no job runs or will run: `schedule.go:150-184`; the worker gives it up there). -/
def schedule.schedDoneD (γ : schedule.SchedNames) : IProp GF := dghostVar γ.run (DFrac.own 1) ()

/-- Two run tokens are one too many. -/
theorem schedule.schedDoneD_excl (γ : schedule.SchedNames) :
    schedule.schedDoneD (GF := GF) γ ∗ schedule.schedDoneD γ ⊢ False := by
  iintro ⟨H1, H2⟩
  iunfold schedule.schedDoneD at H1 H2
  icombine H1 H2 gives %Hv
  obtain ⟨Hv, -⟩ := Hv
  exact absurd (DFrac.valid_own.1 Hv) (Qp_one_add_not_le 1)

/-! ## The jobs' share of the fields -/

/-- The jobs' invariant's name. -/
abbrev mvcc.jobFieldsN : Namespace := nroot.@"mvcc_jobFields"

/-- An eighth (the closer's quarter, halved). -/
abbrev mvcc.q8 : Qp := (1 : Qp).half.half.half

/-- **The compaction jobs' share of the fields** (persistent; draft, in place of `storeStop` in
`compactJobPre`): an eighth of the four fields `Restore` writes at the current objects and names
(`fieldShareAt`: the points-to, the objects' `curAt`, the restoring flag down, what they are), or the
scheduler's run token. A running job holds the run token, so it finds the share; once `Stop` has
returned the run token, the stopper takes the share out (`storeStopR_reclaim`). -/
def mvcc.storeStopR (s : Loc) (γ : mvcc.StoreNames) : IProp GF :=
  inv mvcc.jobFieldsN iprop((∃ o : mvcc.StoreObjs, mvcc.fieldShareAt s γ mvcc.q8 o) ∨
    schedule.schedDoneD γ.sch)

instance mvcc.storeStopR_persistent (s : Loc) (γ : mvcc.StoreNames) :
    Persistent (mvcc.storeStopR (GF := GF) s γ) := by
  unfold mvcc.storeStopR; infer_instance

/-- **The jobs' share back** (`Restore`/`Close`, after `Stop`): with the run token, the share. -/
theorem mvcc.storeStopR_reclaim (s : Loc) (γ : mvcc.StoreNames) :
    ⊢ mvcc.storeStopR (GF := GF) s γ -∗ schedule.schedDoneD γ.sch -∗ £ 1 ={⊤}=∗
      ∃ o : mvcc.StoreObjs, mvcc.fieldShareAt s γ mvcc.q8 o := by
  iintro #Hi Hd Hlc
  iunfold mvcc.storeStopR at Hi
  iinv Hi with Hb Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑mvcc.jobFieldsN) $$ Hlc Hb with Hb
  icases Hb with (⟨%o, Ho⟩ | Hd')
  · imod Hclose $$ [Hd] with -
    · inext; iright; iexact Hd
    imodintro
    iexists o; iexact Ho
  · iexfalso
    iapply schedule.schedDoneD_excl γ.sch $$ [$Hd $Hd']

/-! ## The compaction right that survives `Restore` -/

/-- **The closer's half kept by a compacting store** (draft): an eighth of the fields at the current
objects, the stop channel and its close, the scheduler's stop token (today's `storeCloser` with an
eighth in place of the quarter and without the queue, which the right holds at its revision). -/
def mvcc.storeCloserR (s : Loc) (γ : mvcc.StoreNames) : IProp GF :=
  iprop(∃ o : mvcc.StoreObjs, mvcc.fieldShareAt s γ mvcc.q8 o ∗ mvcc.isStopChan o.sstop ∗
    mvcc.stopCloser o.sstop ∗ schedule.schedStopTok γ.sch)

/-- **The compaction right at `c`, restorable** (draft of `compactRight`; P4's root cause removed):
the compaction revision's half of the authority, the jobs' queue at `c` (as today), the closer's
half (`storeCloserR`) and the jobs' share of the fields (`storeStopR`). Nothing is discarded, so
`store.Restore` (and `Close`) take it back. -/
def mvcc.compactRightR (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
  iprop(mvcc.crevUB γ.idx (1 : Qp).half c ∗ mvcc.compactQueue γ c ∗ mvcc.storeCloserR s γ ∗
    mvcc.storeStopR s γ)

/-- `q8 + q8` is the closer's quarter. -/
theorem mvcc.q8_add : mvcc.q8 + mvcc.q8 = (1 : Qp).half.half := Qp.half_add_half _

/-- **The right from the closer** (draft, in place of `compactRight_of_closer`, which discards): the
closer's quarter split, one eighth into the jobs' invariant; the stop token and the stop channel's
close kept. -/
theorem mvcc.compactRightR_of_closer (s : Loc) (γ : mvcc.StoreNames) (E : CoPset) :
    ⊢ mvcc.storeCloser (GF := GF) s γ -∗ mvcc.crevUB γ.idx (1 : Qp).half (-1) ={E}=∗
      mvcc.compactRightR s γ (-1) := by
  iintro Hcl Hcu
  iunfold mvcc.storeCloser at Hcl
  icases Hcl with ⟨%o, Hf, #Hsc, Hstc, Htok, Hq⟩
  have hs := (mvcc.fieldShareAt_split (GF := GF) s γ mvcc.q8 mvcc.q8 o).1
  rw [mvcc.q8_add] at hs
  icases hs $$ Hf with ⟨Hf1, Hf2⟩
  imod inv_alloc mvcc.jobFieldsN E
    iprop((∃ o : mvcc.StoreObjs, mvcc.fieldShareAt s γ mvcc.q8 o) ∨ schedule.schedDoneD γ.sch)
    $$ [Hf2] with #Hi
  · inext; ileft; iexists o; iexact Hf2
  imodintro
  iunfold mvcc.compactRightR
  iframe Hcu Hq
  isplitl [Hf1 Hstc Htok]
  · iunfold mvcc.storeCloserR
    iexists o
    iframe Hf1 Hsc Hstc Htok
  iunfold mvcc.storeStopR
  iexact Hi

/-- **The closer's quarter again** (`Restore`/`Close` after `Stop`): the closer's eighth and the
jobs' eighth, reclaimed with the run token, are at the same current objects (`curAt`) and make the
quarter today's `storeCloser` holds. -/
theorem mvcc.fieldShare_reclaim (s : Loc) (γ : mvcc.StoreNames) (o : mvcc.StoreObjs) :
    ⊢ mvcc.fieldShareAt (GF := GF) s γ mvcc.q8 o -∗ mvcc.storeStopR s γ -∗
      schedule.schedDoneD γ.sch -∗ £ 1 ={⊤}=∗ mvcc.fieldShareAt s γ (1 : Qp).half.half o := by
  iintro Hf #Hi Hd Hlc
  imod mvcc.storeStopR_reclaim s γ $$ Hi Hd Hlc with ⟨%o', Hf'⟩
  ihave %Hv : ⌜o = o'⌝ $$ [Hf Hf']
  · iunfold mvcc.fieldShareAt at Hf Hf'
    iNamedSuffix Hf "1"
    iNamedSuffix Hf' "2"
    ihave %H := mvcc.curAt_agree γ γ rfl _ _ o o' $$ [$Hcur1 $Hcur2]
    ipureintro; exact H.1
  subst Hv
  have hs := (mvcc.fieldShareAt_split (GF := GF) s γ mvcc.q8 mvcc.q8 o).2
  rw [mvcc.q8_add] at hs
  imodintro
  iapply hs
  iframe Hf Hf'

/-! ## By the mode -/

/-- **What `Restore` takes of the store's right, by the mode** (draft; the pre's
`storeCloser s γ ∗ crevFrozen γ` today): off, today's closer and the frozen revision, at `c = -1`;
on, the restorable compaction right at the store's compaction revision `c`. -/
def mvcc.restoreRightM (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
  if mvcc.kbCmpM γ.kb then mvcc.compactRightR s γ c
  else iprop(mvcc.storeCloser s γ ∗ mvcc.crevFrozen γ ∗ ⌜c = -1⌝)

/-- **What `Restore` hands back, by the mode** (draft; the post's `storeCloser s γ'` today): off,
the closer at the new names; on, the compaction right at the new names and the restored compaction
revision `c'` (its queue holding the job `restore()` resumed, if any). -/
def mvcc.restoreRightPostM (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
  if mvcc.kbCmpM γ.kb then mvcc.compactRightR s γ c else mvcc.storeCloser s γ

theorem mvcc.restoreRightM_off (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : ¬ mvcc.kbCmpM γ.kb) :
    mvcc.restoreRightM (GF := GF) s γ c ⊣⊢
      mvcc.storeCloser s γ ∗ mvcc.crevFrozen γ ∗ ⌜c = -1⌝ := by
  unfold mvcc.restoreRightM; simp only [h, ↓reduceIte]; exact .rfl

theorem mvcc.restoreRightM_on (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : mvcc.kbCmpM γ.kb) :
    mvcc.restoreRightM (GF := GF) s γ c ⊣⊢ mvcc.compactRightR s γ c := by
  unfold mvcc.restoreRightM; simp only [h, ↓reduceIte]; exact .rfl

theorem mvcc.restoreRightPostM_off (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : ¬ mvcc.kbCmpM γ.kb) :
    mvcc.restoreRightPostM (GF := GF) s γ c ⊣⊢ mvcc.storeCloser s γ := by
  unfold mvcc.restoreRightPostM; simp only [h, ↓reduceIte]; exact .rfl

theorem mvcc.restoreRightPostM_on (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : mvcc.kbCmpM γ.kb) :
    mvcc.restoreRightPostM (GF := GF) s γ c ⊣⊢ mvcc.compactRightR s γ c := by
  unfold mvcc.restoreRightPostM; simp only [h, ↓reduceIte]; exact .rfl

/-- **A bucket thinned at the compaction revision `c`** (pure; draft): every entry of `m` is the
log's (`bucketMap`), and every entry of the log missing from `m` is one compaction at `c` may
delete (`KeyDel`, `Compact.lean`). A leader's bucket mid-compaction (its job deleted some of the
keys of the compaction at `c`, `scheduledCompactRev = c`) is one; so is a finished one. -/
def mvcc.imageAt (L : mvcc.Log) (c : Int) (m : mvcc.Bucket) : Prop :=
  (∀ k v, m.lookup k = some v → (mvcc.bucketMap L).lookup k = some v) ∧
  (∀ k, (mvcc.bucketMap L).lookup k ≠ none → m.lookup k = none → mvcc.KeyDel L c k)

/-- The full bucket is thinned at any revision. -/
theorem mvcc.imageAt_full (L : mvcc.Log) (c : Int) : mvcc.imageAt L c (mvcc.bucketMap L) :=
  ⟨fun _ _ h => h, fun _ h1 h2 => absurd h2 h1⟩

/-- **The received backend's image, by the mode** (draft; the pre's
`kbViewC (some d') γb' 1 (bucketMap L') ∗ kbNoCmp (some d') γb'` today): off, the whole `Key`
bucket at the log `L'` and no compaction record, `c' = -1`; on, a view of the `Key` bucket thinned at
the image's compaction revision `c'` (the larger of its `scheduledCompactRev` and
`finishedCompactRev`, which `restore()` reads: `compactMainRev` from the finished one, then the
scheduled one resumed), safe for readers (`NoDelPutAt`, as `store.Compact`'s caller asserts), with
the compaction keys well formed (`fkV`, `OpenBackend`'s). (`store.restore.spec`'s generalization,
the trust boundary's, reads the two records and rebuilds the index over the thinned bucket: drafted
in the plan, not here.) -/
def mvcc.restoreImageM (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (c' : Int) : IProp GF :=
  if d'.cm then
    iprop(∃ m : mvcc.Bucket, mvcc.kbViewC (some d') γb' 1 m ∗ backend.fkV d'.γB true ∗
      ⌜mvcc.imageAt L c' m ∧ -1 ≤ c' ∧ c' < L.length ∧ mvcc.NoDelPutAt L c'⌝)
  else iprop(mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
    ⌜c' = -1⌝)

theorem mvcc.restoreImageM_off (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (c' : Int)
    (h : d'.cm = false) :
    mvcc.restoreImageM (GF := GF) d' γb' L c' ⊣⊢
      mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗ ⌜c' = -1⌝ := by
  unfold mvcc.restoreImageM; simp only [h, Bool.false_eq_true, ↓reduceIte]; exact .rfl

/-- **The clean read's "no compaction" resource, by the mode** (draft; `keyCleanRead`'s `NC` in the
pre, `kbNoCmp` today): off, today's; on, nothing (the meta keys hold the records; what the reads of
them give is `store.restore`'s generalization's). -/
def mvcc.restoreNCM (γ : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM γ.kb then iprop(True) else mvcc.kbNoCmp γ.kb γ.bucket

theorem mvcc.restoreNCM_off (γ : mvcc.StoreNames) (h : ¬ mvcc.kbCmpM γ.kb) :
    mvcc.restoreNCM (GF := GF) γ = mvcc.kbNoCmp γ.kb γ.bucket := by
  unfold mvcc.restoreNCM; simp only [h, ↓reduceIte]

/-- A real backend's mode is its record's. -/
theorem mvcc.kbCmpM_some_iff (d : mvcc.KBReal) : mvcc.kbCmpM (some d) ↔ d.cm = true := Iff.rfl

/-! ## `store.Restore` in either mode -/

/-- **Draft of `store.Restore.spec`, in either mode** (step 2). Today's text but for the marked
changes:
* the two `cm = false` premises become `d'.cm = d.cm` (the mode survives the install; `envAgree`'s
  mode clause, N1/S5', stays true of the new names);
* `storeCloser s γ ∗ crevFrozen γ` becomes `restoreRightM s γ c` (on: the compaction right at the
  store's revision `c`, which `Restore` takes back: the stop channel's close, the stop token and the
  queue for `Stop`, whose post returns the last job's token with the old job's budgets
  `compactJobResM γ.kb`, and the run token, with which the jobs' share of the fields comes back);
* the received image `restoreImageM d' γb' L' c'` with `c ≤ c'` (the compaction revision of the
  image is the log's, which only grows along it: the apply side's obligation, as `L <+: L'`), and
  `keyCleanRead`'s `NC` by the mode (`restoreNCM`);
* new in the pre, both `True` off: the new job's slot `kbSRM (some d')` (the new job's reader is one
  of the `nReaders` tokens: the pool is refilled with `nJobRd` fewer) and the write-back supply of
  the new backend `kbWTSupplyM (some d')` (for the compaction `restore()` resumes when the image's
  `scheduledCompactRev` is past its `finishedCompactRev`: `updateCompactRev`'s `SetScheduledCompact`
  and `ForceCommit`, Q1 (a)'s premise; the server's from its write budget's stock of `d'`,
  `etcdserver/M2StorageDraftRestore.lean`);
* the post: `restoreRightPostM s γ' c'` in place of `storeCloser s γ'`, the old job's budgets
  `compactJobResM γ.kb` (for the old backend's `Close`: a reader's token and the safe-range slot), and
  the old pool's readers `nReaders - 1 - nJobRd γ.kb` (the job's reader came back in the budgets). -/
abbrev mvcc.store.Restore.specM : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c c' : Int),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ c' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ ⌜∃ d, γ.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM s γ c ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗
      mvcc.idxCert γ.idx L ∗ ownToks γ.revs (2 ^ 63 - 3 - L.length) ∗
      (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
      mvcc.certOk γ ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendT b' s (γ.withPhys p) P') ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanRead b' (mvcc.bucketViewC (γ.withPhys p)) (mvcc.storeRT (γ.withPhys p))
          (mvcc.restoreNCM (γ.withPhys p))) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) c' ∗ mvcc.kbRegRight (some d') ∗
      mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.restoreRightPostM s (γ.withPhys p') c' ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
      mvcc.hookP (γ.withPhys p') P' ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      mvcc.compactJobResM γ.kb ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - mvcc.nJobRd γ.kb) (), mvcc.storeRT γ) ∗
      mvcc.storeRT (γ.withPhys p') }}

/-- A real backend that does not compact: its supply, slot and budgets are `True`, its job keeps no
reader. -/
theorem mvcc.cmOff_true (d : mvcc.KBReal) (hcm : d.cm = false) :
    ¬ mvcc.kbCmpM (some d) ∧ mvcc.nJobRd (some d) = 0 ∧
      mvcc.kbSRM (GF := GF) (some d) = iprop(True) ∧ mvcc.kbWTSupplyM (GF := GF) (some d) = iprop(True) ∧
      mvcc.compactJobResM (GF := GF) (some d) = iprop(True) := by
  have h : ¬ mvcc.kbCmpM (some d) := by simp [mvcc.kbCmpM, hcm]
  refine ⟨h, by simp [mvcc.nJobRd, hcm], ?_, ?_, ?_⟩
  · unfold mvcc.kbSRM; simp only [h, ↓reduceIte]
  · unfold mvcc.kbWTSupplyM; simp only [h, ↓reduceIte]
  · unfold mvcc.compactJobResM; simp only [h, ↓reduceIte]

/-- **At `cm = false` the drafted `Restore` reads as today** (the off-mode law): today's spec follows
from the drafted one at `c = c' = -1`. -/
theorem mvcc.store.Restore.spec_of_specM (h : mvcc.store.Restore.specM (GF := GF) (hG := hG)) :
    mvcc.store.Restore.spec (GF := GF) (hG := hG) := by
  intro s γ b' d' γb' P' L R hpre hR
  iintro %Φ ⟨#Hpkg, #Hs, %Hd, %Hd', Hcl, Hfs, Hwd, Hwf, Hwo, #Hfrz, Hcert, Htoks, Hq, #Hok,
    Hbk, Hkc, Hv, Hnc, Hrr, Hrts⟩ HΦ
  obtain ⟨d, hγd, hdcm⟩ := Hd
  obtain ⟨hoff, hj0, hsr, hws, -⟩ := mvcc.cmOff_true (GF := GF) d' Hd'
  obtain ⟨hoffd, hj0d, -, -, hjr⟩ := mvcc.cmOff_true (GF := GF) d hdcm
  have hoffγ : ¬ mvcc.kbCmpM γ.kb := by rw [hγd]; exact hoffd
  iapply (h s γ b' d' γb' P' L R (-1) (-1) hpre hR (Int.le_refl _)) $$
    [Hcl Hfs Hwd Hwf Hwo Hcert Htoks Hq Hbk Hkc Hv Hnc Hrr Hrts]
  · iframe Hpkg Hs Hfs Hwd Hwf Hwo Hcert Htoks Hq Hok Hbk Hrr Hrts
    isplitr
    · ipureintro; exact ⟨d, hγd, by rw [Hd', hdcm]⟩
    isplitl [Hcl]
    · iapply (mvcc.restoreRightM_off s γ (-1) hoffγ).2
      iframe Hcl Hfrz; ipureintro; rfl
    isplitl [Hkc]
    · iintro %p %hp
      ihave Hk := Hkc $$ %p %hp
      have hoffp : ¬ mvcc.kbCmpM (γ.withPhys p).kb := by
        rw [StoreNames.withPhys_kb, hp.2]; exact hoff
      rw [mvcc.restoreNCM_off _ hoffp]
      iexact Hk
    isplitl [Hv Hnc]
    · iapply (mvcc.restoreImageM_off d' γb' _ (-1) Hd').2
      iframe Hv Hnc; ipureintro; rfl
    rw [hsr, hws]
    isplitr <;> itrivial
  have hr : mvcc.nReaders - 1 - mvcc.nJobRd γ.kb = mvcc.nReaders - 1 := by rw [hγd, hj0d]; rfl
  rw [hr]
  iintro !> ⟨%p', %hp', Hcl', Hfs, Hwd, Hwf, Hwo, #Hhook, #Hcert', Htoks, Hq, -, Hrd, Hrt⟩
  iapply HΦ
  iexists p'
  have hoffp : ¬ mvcc.kbCmpM (γ.withPhys p').kb := by
    rw [StoreNames.withPhys_kb, hp'.2]; exact hoff
  ihave Hcl' := (mvcc.restoreRightPostM_off s (γ.withPhys p') (-1) hoffp).1 $$ Hcl'
  iframe Hcl' Hfs Hwd Hwf Hwo Hhook Hcert' Htoks Hq Hrd Hrt
  ipureintro; exact hp'

/-! ## `watchableStore.Restore` in either mode -/

/-- **Draft of `watchableStore.Restore.spec`, in either mode** (step 2): today's text with
`store.Restore.specM`'s changes (the mode surviving the install, `restoreRightM`, the image by the
mode with `c ≤ c'`, `restoreNCM`, the new job's slot and supply, `restoreRightPostM` at the new
names, the old job's budgets back and `nReaders - 1 - nJobRd` old readers). Watchers stay excluded
in compaction mode (N1), so its `syncWatchers` part is unchanged. -/
abbrev mvcc.watchableStore.Restore.specM : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c c' : Int),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ c' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ ⌜∃ d, γ.st.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM st γ.st c ∗ mvcc.writerFrag γ.st ∗ mvcc.writerOwn γ.st ∗
      mvcc.watchWriter γ L ∗
      mvcc.certOk γ.st ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendT b' st (γ.st.withPhys p) P') ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanRead b' (mvcc.bucketViewC (γ.st.withPhys p)) (mvcc.storeRT (γ.st.withPhys p))
          (mvcc.restoreNCM (γ.st.withPhys p))) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) c' ∗ mvcc.kbRegRight (some d') ∗
      mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.restoreRightPostM st (γ.st.withPhys p') c' ∗
      mvcc.writerFrag (γ.st.withPhys p') ∗ mvcc.writerOwn (γ.st.withPhys p') ∗
      mvcc.hookP (γ.st.withPhys p') P' ∗
      mvcc.watchWriter γ ([[], []] ++ R) ∗
      mvcc.compactJobResM γ.st.kb ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - mvcc.nJobRd γ.st.kb) (), mvcc.storeRT γ.st) ∗
      mvcc.storeRT (γ.st.withPhys p') }}

/-- **At `cm = false` the drafted watchable `Restore` reads as today** (the off-mode law). -/
theorem mvcc.watchableStore.Restore.spec_of_specM
    (h : mvcc.watchableStore.Restore.specM (GF := GF) (hG := hG)) :
    mvcc.watchableStore.Restore.spec (GF := GF) (hG := hG) := by
  intro s st γ b' d' γb' P' L R hpre hR
  iintro %Φ ⟨#Hpkg, #Hws, %Hd, %Hd', Hcl, Hwf, Hwo, #Hfrz, Hww, #Hok, Hbk, Hkc, Hv, Hnc, Hrr,
    Hrts⟩ HΦ
  obtain ⟨d, hγd, hdcm⟩ := Hd
  obtain ⟨hoff, -, hsr, hws, -⟩ := mvcc.cmOff_true (GF := GF) d' Hd'
  obtain ⟨hoffd, hj0d, -, -, -⟩ := mvcc.cmOff_true (GF := GF) d hdcm
  have hoffγ : ¬ mvcc.kbCmpM γ.st.kb := by rw [hγd]; exact hoffd
  iapply (h s st γ b' d' γb' P' L R (-1) (-1) hpre hR (Int.le_refl _)) $$
    [Hcl Hwf Hwo Hww Hbk Hkc Hv Hnc Hrr Hrts]
  · iframe Hpkg Hws Hwf Hwo Hww Hok Hbk Hrr Hrts
    isplitr
    · ipureintro; exact ⟨d, hγd, by rw [Hd', hdcm]⟩
    isplitl [Hcl]
    · iapply (mvcc.restoreRightM_off st γ.st (-1) hoffγ).2
      iframe Hcl Hfrz; ipureintro; rfl
    isplitl [Hkc]
    · iintro %p %hp
      ihave Hk := Hkc $$ %p %hp
      have hoffp : ¬ mvcc.kbCmpM (γ.st.withPhys p).kb := by
        rw [StoreNames.withPhys_kb, hp.2]; exact hoff
      rw [mvcc.restoreNCM_off _ hoffp]
      iexact Hk
    isplitl [Hv Hnc]
    · iapply (mvcc.restoreImageM_off d' γb' _ (-1) Hd').2
      iframe Hv Hnc; ipureintro; rfl
    rw [hsr, hws]
    isplitr <;> itrivial
  have hr : mvcc.nReaders - 1 - mvcc.nJobRd γ.st.kb = mvcc.nReaders - 1 := by rw [hγd, hj0d]; rfl
  rw [hr]
  iintro !> ⟨%p', %hp', Hcl', Hwf, Hwo, #Hhook, Hww, -, Hrd, Hrt⟩
  iapply HΦ
  iexists p'
  have hoffp : ¬ mvcc.kbCmpM (γ.st.withPhys p').kb := by
    rw [StoreNames.withPhys_kb, hp'.2]; exact hoff
  ihave Hcl' := (mvcc.restoreRightPostM_off st (γ.st.withPhys p') (-1) hoffp).1 $$ Hcl'
  iframe Hcl' Hwf Hwo Hhook Hww Hrd Hrt
  ipureintro; exact hp'

/-! ## The watchable store's closer in compaction mode -/

/-- **The watchable store's closer, a compacting store's** (draft; what the server keeps in compaction
mode, D22's `srvKVCloser` by the mode): the watchable store's own stop channel's close and waiter
(as `wsCloser`), and the inner store's restorable compaction right at `c` in place of its closer. -/
def mvcc.wsCloserR (s st : Loc) (γs : mvcc.StoreNames) (c : Int) : IProp GF :=
  iprop(∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s ∗
    mvcc.compactRightR st γs c)

/-- **The compaction right from the watchable store's closer** (draft, in place of
`compactRight_of_wsCloser`: the closer is kept, not discarded; the step after `NewServer`'s last
error return): the inner closer and the authority's half (`crevRightM`, on) make the restorable
right at `-1`; the watchable store's own parts are kept. -/
theorem mvcc.wsCloserR_of_wsCloser (s st : Loc) (γs : mvcc.StoreNames) (h : mvcc.kbCmpM γs.kb)
    (E : CoPset) :
    ⊢ mvcc.wsCloser (GF := GF) s st γs -∗ mvcc.crevRightM γs ={E}=∗ mvcc.wsCloserR s st γs (-1) := by
  unfold mvcc.crevRightM
  simp only [h, ↓reduceIte]
  iintro Hcl Hcr
  iunfold mvcc.wsCloser at Hcl
  icases Hcl with ⟨%stc, #Hstc, Hsc, Hw, Hcl⟩
  imod mvcc.compactRightR_of_closer st γs E $$ Hcl Hcr with Hr
  imodintro
  iunfold mvcc.wsCloserR
  iexists stc
  iframe Hstc Hsc Hw Hr

/-- **The watchable store's closer and the inner store's restore right, by the mode** (draft): what
`watchableStore.Restore.specM` takes besides the store (`restoreRightM`) and what the watchable store
keeps (its stop channel's close, its waiter), split. -/
theorem mvcc.wsCloserR_split (s st : Loc) (γs : mvcc.StoreNames) (c : Int) (h : mvcc.kbCmpM γs.kb) :
    mvcc.wsCloserR (GF := GF) s st γs c ⊢
      mvcc.restoreRightM st γs c ∗
        (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s) := by
  iintro Hcl
  iunfold mvcc.wsCloserR at Hcl
  icases Hcl with ⟨%stc, #Hstc, Hsc, Hw, Hr⟩
  isplitl [Hr]
  · iapply (mvcc.restoreRightM_on st γs c h).2; iexact Hr
  iexists stc
  iframe Hstc Hsc Hw

/-- And back, after `Restore` (at the new names). -/
theorem mvcc.wsCloserR_join (s st : Loc) (γs : mvcc.StoreNames) (c : Int) (h : mvcc.kbCmpM γs.kb) :
    mvcc.restoreRightPostM (GF := GF) st γs c ∗
        (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s) ⊢
      mvcc.wsCloserR s st γs c := by
  iintro ⟨Hr, ⟨%stc, #Hstc, Hsc, Hw⟩⟩
  ihave Hr := (mvcc.restoreRightPostM_on st γs c h).1 $$ Hr
  iunfold mvcc.wsCloserR
  iexists stc
  iframe Hstc Hsc Hw Hr

end draft

end EtcdGrove
end Perennial
