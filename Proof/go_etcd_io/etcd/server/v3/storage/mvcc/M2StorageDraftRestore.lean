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
`resumeCsM`), the old job's budgets back
(`compactJobResM γ.kb`, for the old backend's `Close`), the new store's right
(`storeCloserM`). Also drafted: the generalized `store.restore` (`store.restore.specR`, item
18) and `store.Close` by the mode (`store.Close.specM`). At `cm = false` each reads as today: `store.Restore.spec_of_specM` and
`watchableStore.Restore.spec_of_specM` derive today's specs from the drafted ones.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraft
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.M2StorageDraft
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev

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

/-! ## The jobs' share of the fields -/

/-- The jobs' invariant's name. -/
abbrev mvcc.jobFieldsN : Namespace := nroot.@"mvcc_jobFields"

/-- An eighth (the closer's quarter, halved). -/
abbrev mvcc.q8 : Qp := (1 : Qp).half.half.half

/-- **The compaction jobs' share of the fields at the objects `o`** (persistent; draft, in place of
`storeStop` in `compactJobPre`, which carries `∃ o, storeStopR s γ o`): an eighth of the four
fields `Restore` writes at the objects `o` (`fieldShareAt`: the points-to, the objects' `curAt`,
the restoring flag down, what they are), or the scheduler's run token. A running job holds the run
token, so it finds the share; once `Stop` has returned the run token, the stopper takes the share
out (`storeStopR_reclaim`). The objects are fixed in the invariant (review round 3's S4): while the
eighth is in it no one writes the fields, and `Restore` reclaims it only after `Stop`, then moves to
fresh names (`withPhys`, whose scheduler is new); so a job reads every field at the same `o`, as
today's discarded `curAt` gives it, without holding a fraction. -/
@[no_expose] def mvcc.storeStopR (s : Loc) (γ : mvcc.StoreNames) (o : mvcc.StoreObjs) : IProp GF :=
  inv mvcc.jobFieldsN iprop(mvcc.fieldShareAt s γ mvcc.q8 o ∨ schedule.schedDoneD γ.sch)

instance mvcc.storeStopR_persistent (s : Loc) (γ : mvcc.StoreNames) (o : mvcc.StoreObjs) :
    Persistent (mvcc.storeStopR (GF := GF) s γ o) := by
  unfold mvcc.storeStopR; infer_instance

/-- **The jobs' share back** (`Restore`/`Close`, after `Stop`): with the run token, the share. -/
theorem mvcc.storeStopR_reclaim (s : Loc) (γ : mvcc.StoreNames) (o : mvcc.StoreObjs) :
    ⊢ mvcc.storeStopR (GF := GF) s γ o -∗ schedule.schedDoneD γ.sch -∗ £ 1 ={⊤}=∗
      mvcc.fieldShareAt s γ mvcc.q8 o := by
  iintro #Hi Hd Hlc
  iunfold mvcc.storeStopR at Hi
  iinv Hi with Hb Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑mvcc.jobFieldsN) $$ Hlc Hb with Hb
  icases Hb with (Ho | Hd')
  · imod Hclose $$ [Hd] with -
    · inext; iright; iexact Hd
    imodintro
    iexact Ho
  · iexfalso
    iapply schedule.schedDoneD_excl γ.sch $$ [$Hd $Hd']

/-! ## The compaction right that survives `Restore` -/

/-- **The closer's half kept by a compacting store** (draft): an eighth of the fields at the objects
`o`, the stop channel and its close, the scheduler's stop token (today's `storeCloser` with an
eighth in place of the quarter and without the queue, which the right holds at its revision). -/
@[no_expose] def mvcc.storeCloserR (s : Loc) (γ : mvcc.StoreNames) (o : mvcc.StoreObjs) : IProp GF :=
  iprop(mvcc.fieldShareAt s γ mvcc.q8 o ∗ mvcc.isStopChan o.sstop ∗
    mvcc.stopCloser o.sstop ∗ schedule.schedStopTok γ.sch)

/-- **The compaction right at `c`, restorable** (draft of `compactRight`; P4's root cause removed):
the compaction revision's half of the authority, the jobs' queue at `c` (as today), the closer's
half (`storeCloserR`) and the jobs' share of the fields (`storeStopR`), at the same objects. Nothing
is discarded, so `store.Restore` (and `Close`) take it back. -/
@[no_expose] def mvcc.compactRightR (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
  iprop(mvcc.crevUB γ.idx (1 : Qp).half c ∗ mvcc.compactQueue γ c ∗
    ∃ o : mvcc.StoreObjs, mvcc.storeCloserR s γ o ∗ mvcc.storeStopR s γ o)

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
    iprop(mvcc.fieldShareAt s γ mvcc.q8 o ∨ schedule.schedDoneD γ.sch)
    $$ [Hf2] with #Hi
  · inext; ileft; iexact Hf2
  imodintro
  iunfold mvcc.compactRightR
  iframe Hcu Hq
  iexists o
  isplitl [Hf1 Hstc Htok]
  · iunfold mvcc.storeCloserR
    iframe Hf1 Hsc Hstc Htok
  iunfold mvcc.storeStopR
  iexact Hi

/-- **The closer's quarter again** (`Restore`/`Close` after `Stop`): the closer's eighth and the
jobs' eighth, reclaimed with the run token, are at the same objects and make the quarter today's
`storeCloser` holds. -/
theorem mvcc.fieldShare_reclaim (s : Loc) (γ : mvcc.StoreNames) (o : mvcc.StoreObjs) :
    ⊢ mvcc.fieldShareAt (GF := GF) s γ mvcc.q8 o -∗ mvcc.storeStopR s γ o -∗
      schedule.schedDoneD γ.sch -∗ £ 1 ={⊤}=∗ mvcc.fieldShareAt s γ (1 : Qp).half.half o := by
  iintro Hf #Hi Hd Hlc
  imod mvcc.storeStopR_reclaim s γ o $$ Hi Hd Hlc with Hf'
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

/-- **The store's right to close, by the mode** (draft; renamed from `restoreRightPostM`, review
round 4's S4: it is `Restore.specM`'s post and `Close.specM`'s pre): off, today's closer; on, the
restorable compaction right at the store's compaction revision `c` (after `Restore`, at the new
names and the restored revision, its queue holding the job `restore()` resumed, if any).
`restoreRightM` is it with, off, `crevFrozen ∗ ⌜c = -1⌝`. -/
def mvcc.storeCloserM (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
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

theorem mvcc.storeCloserM_off (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : ¬ mvcc.kbCmpM γ.kb) :
    mvcc.storeCloserM (GF := GF) s γ c ⊣⊢ mvcc.storeCloser s γ := by
  unfold mvcc.storeCloserM; simp only [h, ↓reduceIte]; exact .rfl

theorem mvcc.storeCloserM_on (s : Loc) (γ : mvcc.StoreNames) (c : Int)
    (h : mvcc.kbCmpM γ.kb) :
    mvcc.storeCloserM (GF := GF) s γ c ⊣⊢ mvcc.compactRightR s γ c := by
  unfold mvcc.storeCloserM; simp only [h, ↓reduceIte]; exact .rfl

/- (Round 3's `bucketThinnedAt`, any deletable subset missing, is replaced by the job's shape
`entsCutAt`, `M2StorageDraftIndex.lean`: `bucketThinnedAt_counterexample`, review round 4.) -/

/-! ## The compaction records (review round 3, F1) -/

/-- **A backend image's compaction records** (draft; `Meta`'s `finishedCompactRev` and
`scheduledCompactRev`: absent, or a revision), what `restore()` reads (`kvstore.go:330-342`). -/
structure mvcc.CmpRecs where
  fin : Option w64
  sched : Option w64
  deriving DecidableEq

/-- No record (today's received images, `kbNoCmp`). -/
def mvcc.CmpRecs.empty : mvcc.CmpRecs := ⟨none, none⟩

/-- The finished record, `-1` if absent (`restore()`'s first `compactMainRev`). -/
def mvcc.CmpRecs.finRev (r : mvcc.CmpRecs) : Int := (r.fin.map sint.Z).getD (-1)

/-- The scheduled record as `restore()` reads it: `0` if absent (`UnsafeReadScheduledCompact`'s
`(0, false)`, whose found flag `restore()` drops). -/
def mvcc.CmpRecs.schedRev (r : mvcc.CmpRecs) : Int := (r.sched.map sint.Z).getD 0

/-- **`restore()` resumes the scheduled compaction**: the scheduled record (read as above) is not
`0` and is past the finished one (`kvstore.go:389-391`, `:411`). A scheduled record of `0` is never
resumed (`issues/etcd-restore-scheduled-compact-zero.md`). -/
def mvcc.CmpRecs.resumes (r : mvcc.CmpRecs) : Bool := decide (r.schedRev ≠ 0 ∧ r.finRev < r.schedRev)

/-- **The compaction revision `restore()` leaves** (`compactMainRev` after it): the scheduled one if
it is resumed (`compactLockfree` → `updateCompactRev`, which succeeds: past the finished one, and
`currentRev` was raised to it), else the finished one, else `-1`. -/
def mvcc.CmpRecs.crev (r : mvcc.CmpRecs) : Int := if r.resumes then r.schedRev else r.finRev

theorem mvcc.CmpRecs.crev_empty : mvcc.CmpRecs.empty.crev = -1 := by decide

theorem mvcc.CmpRecs.resumes_empty : mvcc.CmpRecs.empty.resumes = false := by decide

/-- **The records are of the log `L`** (pure): each a revision of `L` (`metaRevVal`'s `0 ≤`; below
`|L|`, so `restore()`'s raise of `currentRev` to the scheduled one leaves `|L| - 1`). -/
def mvcc.recsOk (L : mvcc.Log) (r : mvcc.CmpRecs) : Prop :=
  (∀ x, r.fin = some x → 0 ≤ sint.Z x ∧ sint.Z x < L.length) ∧
  (∀ x, r.sched = some x → 0 ≤ sint.Z x ∧ sint.Z x < L.length)

/-- The restored revision is a revision of the log (or `-1`): `recsOk` and the log's two first
revisions make round 3's `r.crev < L.length` conjunct redundant (review round 4, S4). -/
theorem mvcc.recsOk_crev_lt (L : mvcc.Log) (r : mvcc.CmpRecs) (h : mvcc.recsOk L r)
    (hL : 2 ≤ L.length) : r.crev < L.length := by
  have hf : ∀ x, r.fin = some x → sint.Z x < L.length := fun x hx => (h.1 x hx).2
  have hs : ∀ x, r.sched = some x → sint.Z x < L.length := fun x hx => (h.2 x hx).2
  unfold mvcc.CmpRecs.crev mvcc.CmpRecs.schedRev mvcc.CmpRecs.finRev
  rcases r with ⟨_ | x, _ | y⟩ <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hf hs ⊢
  · split <;> omega
  · have := hs y rfl; split <;> omega
  · have := hf x rfl; split <;> omega
  · have := hf x rfl; have := hs y rfl; split <;> omega

/-- **The records are past revision `0`** (pure; M2's scope restriction, Q7 (a): every committed
compaction is at a revision `≥ 1`, `CompactScope`'s `compactPropOkD`, so the image's records,
written by applying them, are; `issues/etcd-restore-scheduled-compact-zero.md`). -/
def mvcc.recsPos (r : mvcc.CmpRecs) : Prop :=
  (∀ x, r.fin = some x → 1 ≤ sint.Z x) ∧ (∀ x, r.sched = some x → 1 ≤ sint.Z x)

/-- **Under the scope restriction the restored revision is none or a compaction's** (`-1` or
`≥ 1`): the corner of Q7 (a scheduled compaction at `0`, never resumed) cannot arise, so the
apply side's `c ≤ r.crev` is `crevOf_mono` without exception. -/
theorem mvcc.recsPos_crev (r : mvcc.CmpRecs) (h : mvcc.recsPos r) : r.crev = -1 ∨ 1 ≤ r.crev := by
  have hf : ∀ x, r.fin = some x → 1 ≤ sint.Z x := h.1
  have hs : ∀ x, r.sched = some x → 1 ≤ sint.Z x := h.2
  unfold mvcc.CmpRecs.crev mvcc.CmpRecs.resumes mvcc.CmpRecs.schedRev mvcc.CmpRecs.finRev
  rcases r with ⟨_ | x, _ | y⟩ <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hf hs ⊢
  · left; simp
  · have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    have h1 : (-1 : Int) < sint.Z y := by omega
    right; simp [h0, h1]; omega
  · have := hf x rfl
    right; simp; omega
  · have := hf x rfl; have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    right
    by_cases hc : sint.Z x < sint.Z y <;> simp [h0, hc] <;> omega

/-- The bytes stored at a record (`RevToBytes(Revision{Main: x})`). -/
def mvcc.recBytes (x : Option w64) : Option GoString := x.map (fun x => mvcc.revBytes ⟨x, W64 0⟩ false)

/-- **The backend's compaction-key ghost, merged** (draft; review round 4's S4: one name `γ.fkv`
at one type, in place of today's `fkV γ w` and round 3's `fkOpenD` beside it at another type): the
well-formedness bit `w` and the client's flag `n` at the open over data whose compaction keys hold
`v`. At the switch `OpenBackend`/`New` over bbolt's `D` give it at
`(fkWInit P D, fkInit D, (dget D meta fin, dget D meta sched))` beside the client's half of the flag,
a put of a compaction key raises the flag strictly (`fkPut`: `f` to `f + 1`), and the batch lock's
and the readers' clause (`fkOk`) gains `f = n → the state's keys are v`: so while the client holds
its half at `n`, every read of the keys returns `v` (`metaReadSpecR`). Rests on bbolt's data as the
backend's proofs already read it (no new axiom expected). -/
def backend.fkVD (γ : backend.BNames) (w : Bool) (n : Nat) (v : Option GoString × Option GoString) :
    IProp GF :=
  dghostVar γ.fkv DFrac.discard (w, n, v)

instance backend.fkVD_persistent (γ : backend.BNames) (w : Bool) (n : Nat)
    (v : Option GoString × Option GoString) : Persistent (backend.fkVD (GF := GF) γ w n v) := by
  unfold backend.fkVD; infer_instance

/-- **Today's `fkV γ w`, over the merged ghost** (the bit alone). -/
def backend.fkVM (γ : backend.BNames) (w : Bool) : IProp GF :=
  iprop(∃ (n : Nat) (v : Option GoString × Option GoString), backend.fkVD γ w n v)

/-- **The compaction keys as opened** (persistent; draft): the client's flag stood at `n` when the
backend was opened over data whose two compaction keys hold `v` (finished, scheduled). -/
def backend.fkOpenD (γ : backend.BNames) (n : Nat) (v : Option GoString × Option GoString) :
    IProp GF :=
  iprop(∃ w : Bool, backend.fkVD γ w n v)

instance backend.fkOpenD_persistent (γ : backend.BNames) (n : Nat)
    (v : Option GoString × Option GoString) : Persistent (backend.fkOpenD (GF := GF) γ n v) := by
  unfold backend.fkOpenD; infer_instance

/-- **The records of the instance `kb`, with the right to write them** (draft; generalizes
`kbNoCmp`, which is its value at no record, `kbRecs_empty`): for the real backend, the client's
half of its compaction-key flag at the value it had when opened over records `r`. It is the
compaction-key write right (`kbRecs_MW`: a compacting store's `mwInv` keeps it, `restore()`'s
resumed `updateCompactRev` writes through it) and, held unmoved, the license to read the records
(`metaReadSpecR`). mvcc's assumed backend has no records vocabulary: only `r = empty`. -/
def mvcc.kbRecs (kb : Option mvcc.KBReal) (γb : GName) (r : mvcc.CmpRecs) : IProp GF :=
  if r = mvcc.CmpRecs.empty then mvcc.kbNoCmp kb γb
  else match kb with
    | none => iprop(False)
    | some d => iprop(∃ n : Nat, backend.fkOwn d.γB n ∗
        backend.fkOpenD d.γB n (mvcc.recBytes r.fin, mvcc.recBytes r.sched))

/-- No record is today's no-compaction token. -/
theorem mvcc.kbRecs_empty (kb : Option mvcc.KBReal) (γb : GName) :
    mvcc.kbRecs (GF := GF) kb γb mvcc.CmpRecs.empty = mvcc.kbNoCmp kb γb := by
  unfold mvcc.kbRecs; simp

/-- **The records are the write right** (`restore` gives it back as `kbMW`, as today's
`kbNoCmp_MW`). -/
theorem mvcc.kbRecs_MW (kb : Option mvcc.KBReal) (γb : GName) (r : mvcc.CmpRecs) :
    mvcc.kbRecs (GF := GF) kb γb r ⊢ mvcc.kbMW kb γb := by
  unfold mvcc.kbRecs
  split
  · exact mvcc.kbNoCmp_MW kb γb
  · cases kb with
    | none => iintro H; iexfalso; iexact H
    | some d =>
      unfold mvcc.kbMW
      iintro ⟨%n, H, -⟩
      iexists n
      iexact H

/-- The record a compaction key holds. -/
def mvcc.CmpRecs.at (r : mvcc.CmpRecs) (kn : GoString) : Option w64 :=
  if kn = mvcc.finKeyBytes then r.fin else r.sched

/-- **A read of a compaction key under the records `r`** (draft; `metaReadSpec`'s generalization):
at no record, today's `metaReadSpec rt true` (nothing is found; `metaReadSpecR_empty` is `rfl`);
else the key's record, exactly: nothing if absent, else the key and the record's bytes, a
non-negative revision (`recsOk`). `keyReadLockedR`'s meta clause gives it (review round 4, A1 (a));
`UnsafeReadFinishedCompact`/`UnsafeReadScheduledCompact` return the record (`specR`, proved below). -/
def mvcc.metaReadSpecR (rt : GoInterfaceOk) (r : mvcc.CmpRecs) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) : IProp GF :=
  if r = mvcc.CmpRecs.empty then mvcc.metaReadSpec rt true Rd Tok
  else iprop(∀ (b : GoInterface) (key : GoSlice) (kn : GoString) (dq : DFrac),
    ⌜mvcc.metaCompactKey kn⌝ →
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ Tok ∗ key ↦*{dq} kn }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); Tok ∗ key ↦*{dq} kn ∗
        ((⌜r.at kn = none⌝ ∗ ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice)) ∨
          ∃ (ksl vsl : GoSlice) (x : w64), ⌜r.at kn = some x ∧ 0 ≤ sint.Z x⌝ ∗ ks ↦*□ [ksl] ∗
            Rd ksl kn ∗ vs ↦*□ [vsl] ∗ Rd vsl (mvcc.revBytes ⟨x, W64 0⟩ false)) }})

instance mvcc.metaReadSpecR_persistent (rt : GoInterfaceOk) (r : mvcc.CmpRecs)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    Persistent (mvcc.metaReadSpecR (GF := GF) rt r Rd Tok) := by
  unfold mvcc.metaReadSpecR; split <;> infer_instance

/-- At no record, today's. -/
theorem mvcc.metaReadSpecR_empty (rt : GoInterfaceOk) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) :
    mvcc.metaReadSpecR (GF := GF) rt mvcc.CmpRecs.empty Rd Tok = mvcc.metaReadSpec rt true Rd Tok := by
  unfold mvcc.metaReadSpecR; simp

/-! ## The backend vocabulary with the records (review round 4, A1 (a))

Each is today's text with the meta clause at `metaReadSpecR rt r` in place of `metaReadSpec rt true`
(`keyReadLocked`'s), the records `r` passed down; at `r = empty` each *is* today's (`…_empty`, by
`metaReadSpecR_empty`). At the switch they replace today's, with `r` a parameter of default
`empty`: every existing use reads as today. -/

/-- **Draft of `keyReadLocked`** with the records `r` (its meta clause: with `NC`, the reads of
the compaction keys find the records). -/
def mvcc.keyReadLockedR (RT NC : IProp GF) (r : mvcc.CmpRecs) (rng : Bool) (rt : GoInterfaceOk)
    (m : mvcc.Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    IProp GF :=
  iprop(□ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); RT }}) ∗
    □ mvcc.keyRangeSpec rt m Rd Tok ∗
    (if rng then iprop(□ mvcc.keyRangeReadSpec rt m Rd Tok ∗ □ mvcc.keyRangeLimSpec rt m Rd Tok cl ∗
      □ mvcc.rdSplit rt m Rd Tok cl ∗ □ (NC -∗ NC ∗ □ mvcc.metaReadSpecR rt r Rd Tok))
     else iprop(True)) ∗
    mvcc.rdCap Rd Tok)

theorem mvcc.keyReadLockedR_empty (RT NC : IProp GF) (rng : Bool) (rt : GoInterfaceOk)
    (m : mvcc.Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool) :
    mvcc.keyReadLockedR RT NC mvcc.CmpRecs.empty rng rt m Rd Tok cl =
      mvcc.keyReadLocked RT NC rng rt m Rd Tok cl := by
  unfold mvcc.keyReadLockedR mvcc.keyReadLocked; rw [mvcc.metaReadSpecR_empty]

/-- **Draft of `keyReadSnap`** with the records. -/
def mvcc.keyReadSnapR (View : Qp → mvcc.Bucket → IProp GF) (RT NC : IProp GF) (r : mvcc.CmpRecs)
    (Del : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : mvcc.Bucket) (L : IProp GF) :
    IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (m' : mvcc.Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
        Tok ∗ mvcc.keyReadLockedR RT NC r rng rt m' Rd Tok ∗ mvcc.snapThin m m' Del }}))

theorem mvcc.keyReadSnapR_empty (View : Qp → mvcc.Bucket → IProp GF) (RT NC : IProp GF)
    (Del : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : mvcc.Bucket) (L : IProp GF) :
    mvcc.keyReadSnapR View RT NC mvcc.CmpRecs.empty Del rng rt m L =
      mvcc.keyReadSnap View RT NC Del rng rt m L := by
  unfold mvcc.keyReadSnapR mvcc.keyReadSnap; simp only [mvcc.keyReadLockedR_empty]

/-- **Draft of `keyReadSnapC`** with the records. -/
def mvcc.keyReadSnapCR (View : Qp → mvcc.Bucket → IProp GF) (RT NC : IProp GF) (r : mvcc.CmpRecs)
    (rt : GoInterfaceOk) (m : mvcc.Bucket) (L : IProp GF) : IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
        Tok ∗ mvcc.keyReadLockedR RT NC r true rt m Rd Tok true }}))

theorem mvcc.keyReadSnapCR_empty (View : Qp → mvcc.Bucket → IProp GF) (RT NC : IProp GF)
    (rt : GoInterfaceOk) (m : mvcc.Bucket) (L : IProp GF) :
    mvcc.keyReadSnapCR View RT NC mvcc.CmpRecs.empty rt m L = mvcc.keyReadSnapC View RT NC rt m L := by
  unfold mvcc.keyReadSnapCR mvcc.keyReadSnapC; simp only [mvcc.keyReadLockedR_empty]

/-- **Draft of `keyCleanRead`** with the records (what `store.restore` takes of a backend holding
data, its `NC` the records' `kbRecs … r`; D22's walk builds it from `keyCleanRead_of_backendC`). -/
def mvcc.keyCleanReadR (b : GoInterface) (View : Qp → mvcc.Bucket → IProp GF) (RT NC : IProp GF)
    (r : mvcc.CmpRecs) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : mvcc.Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ mvcc.keyReadSnapCR View RT NC r rt m L }}))

instance mvcc.keyCleanReadR_persistent (b : GoInterface) (View : Qp → mvcc.Bucket → IProp GF)
    (RT NC : IProp GF) (r : mvcc.CmpRecs) : Persistent (mvcc.keyCleanReadR (GF := GF) b View RT NC r) := by
  unfold mvcc.keyCleanReadR; infer_instance

theorem mvcc.keyCleanReadR_empty (b : GoInterface) (View : Qp → mvcc.Bucket → IProp GF)
    (RT NC : IProp GF) :
    mvcc.keyCleanReadR (GF := GF) b View RT NC mvcc.CmpRecs.empty = mvcc.keyCleanRead b View RT NC := by
  unfold mvcc.keyCleanReadR mvcc.keyCleanRead; simp only [mvcc.keyReadSnapCR_empty]

/-- **Draft of `isKeyBackendG`** with the records (its two `ReadTx`s' snapshots at `r`). -/
def mvcc.isKeyBackendGR (b : GoInterface) (View : Qp → mvcc.Bucket → IProp GF) (RT WT NC : IProp GF)
    (r : mvcc.CmpRecs) (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF)
    (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF := fun X Y => iprop(□ (X -∗ Y)))
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (Bt : GoInterfaceOk → IProp GF := fun _ => iprop(True))
    (SR SRh : IProp GF := iprop(True)) (MW : IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : mvcc.Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ConcurrentReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ mvcc.keyReadSnapR View RT NC r Del false rt m L }}) ∗
    □ (∀ (q : Qp) (m : mvcc.Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ mvcc.keyReadSnapR View RT NC r Del true rt m L }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (bt : GoInterfaceOk), RET #(GoInterface.ok bt);
          mvcc.isBatchTxG bt View RT WT PutOk Del W Wi Dep Cmp P HF Rb Bt MW }}) ∗
    □ (∀ (X Y : IProp GF),
      {{ RT ∗ WT ∗ X ∗ Req X Y }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      {{ RET #(); RT ∗ Y }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"Size" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"SizeInUse" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ (⌜Cmp⌝ -∗
      □ ({{ SR }} (App (Val #(methods bi.ty go!"LockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); SRh }}) ∗
      □ ({{ SRh }} (App (Val #(methods bi.ty go!"UnlockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); SR }}) ∗
      □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); mvcc.metaReadTx rt RT }})))

theorem mvcc.isKeyBackendGR_empty (b : GoInterface) (View : Qp → mvcc.Bucket → IProp GF)
    (RT WT NC : IProp GF) (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF)
    (HF : val → IProp GF) (Req : IProp GF → IProp GF → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (SR SRh MW : IProp GF) :
    mvcc.isKeyBackendGR b View RT WT NC mvcc.CmpRecs.empty PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh
        MW =
      mvcc.isKeyBackendG b View RT WT NC PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW := by
  unfold mvcc.isKeyBackendGR mvcc.isKeyBackendG; simp only [mvcc.keyReadSnapR_empty]

/-- **Draft of `storeBackendT`** with the records: `NC` the records' `kbRecs … r`. -/
def mvcc.storeBackendTR (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF)
    (r : mvcc.CmpRecs) : IProp GF :=
  mvcc.isKeyBackendGR b (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
    (mvcc.kbRecs γ.kb γ.bucket r) r (mvcc.storePutOk γ) (mvcc.delKey γ) (mvcc.storeW s γ)
    (mvcc.kbWi γ.kb) iprop(True) (mvcc.storeCmp γ) P (mvcc.hookFn γ) (mvcc.storeReq γ) (mvcc.storeRb γ)
    (mvcc.storeBt γ) (mvcc.kbSR γ.kb) (mvcc.kbSRh γ.kb) (mvcc.kbMW γ.kb γ.bucket)

theorem mvcc.storeBackendTR_empty (b : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) :
    mvcc.storeBackendTR (GF := GF) b s γ P mvcc.CmpRecs.empty = mvcc.storeBackendT b s γ P := by
  unfold mvcc.storeBackendTR mvcc.storeBackendT
  rw [mvcc.kbRecs_empty, mvcc.isKeyBackendGR_empty]

/-- The `Key` bucket of the entries `ents` (`bucketMap`'s fold over them). -/
def mvcc.bucketOfEnts (ents : List mvcc.KvEnt) : mvcc.Bucket :=
  (ents.map mvcc.KvEnt.pair).foldl (fun m p => GMap.insert p.1 p.2 m) GMap.empty

/-- **Draft of `restoreView`, over the image's bucket `m` and records `r`**: `NewStore`'s empty
bucket (no record), or the bucket `m` over a clean read buffer with the records' clean read. -/
def mvcc.restoreViewR (b : GoInterface) (γ : mvcc.StoreNames) (RT : IProp GF) (q : Qp) (R : mvcc.Log)
    (m : mvcc.Bucket) (r : mvcc.CmpRecs) : IProp GF :=
  if R = [] then iprop(mvcc.bucketView γ q ∅ ∗ ⌜m = ∅ ∧ r = mvcc.CmpRecs.empty⌝)
  else iprop(mvcc.bucketViewC γ q m ∗
    mvcc.keyCleanReadR b (mvcc.bucketViewC γ) RT (mvcc.kbRecs γ.kb γ.bucket r) r)

set_option linter.unusedVariables false in
/-- **The records' clean read of a compacting real backend** (the statement of the bridge law the
walk needs, A1 (a); **not proved**): `keyCleanRead_of_backend`'s, over the deletable keys' registration
in place of `dlNoDel` (`storeDlReg`, as `storeBackendT_of_backendC`; the new backend's job has not
started, so nothing is deleted while `restore()` reads), the clean read at the records `r` its
client's flag stands at since the open (`kbRecs`'s `fkOpenD`). Missing for its proof (backend-internal,
over bbolt's data at the open as `fkCl` already is: no new axiom expected; if the re-proof needs a
new bbolt fact, it is an axiom, for the `axiom` skill): the backend's `fkOk` clause
`f = n → the state's compaction keys are v` (`fkOpenD`), kept by every operation but a compaction-key
put, which raises the flag. -/
def mvcc.keyCleanRead_of_backendC_stmt : Prop :=
  ∀ (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (Pk : IProp GF) (γb : GName) (γi : mvcc.IdxNames)
    (r : mvcc.CmpRecs),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
        mvcc.storeDlReg d.γB γi ⊢
      ∀ (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanReadR
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) (mvcc.bucketViewC γ) (mvcc.storeRT γ) (mvcc.kbRecs γ.kb γ.bucket r) r

/-- **A received image's `Key` entries and compaction records, by the mode** (draft of
`keyImage`'s use in `specSnap`, D22's `hkI`; review round 4): off, today's `keyImage` (the whole
bucket at `L`, no record); on, the `Key` bucket the entries `ents` of the job's shape at the
records' revision `r.crev` (`entsCutAt`: per key, a prefix of its entries deletable there removed;
a finished compaction or a leader's bucket mid-job), the `Meta` bucket's two compaction keys
holding the records' bytes, the records of `L` and past revision `0` (`recsPos`: M2's scope, Q7
(a)), `r.crev` safe for readers (`NoDelPutAt`) and each key changed once per revision up to it
(`KeyOnceAt`: etcd's `checkIntervals`). The apply side's obligations (S-j1's), as `L <+: L'` is
today. The walk's `restoreImageM` and the clean read's records come from it with the backend's
`fkOpenD`. -/
def mvcc.keyImageM (cm : Bool) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) : Prop :=
  if cm then ∃ ents : List mvcc.KvEnt,
      (∀ k, backend.dget D mvcc.keyName k = (mvcc.bucketOfEnts ents).lookup k) ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes =
        mvcc.recBytes r.fin ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes =
        mvcc.recBytes r.sched ∧
      mvcc.recsOk L r ∧ mvcc.recsPos r ∧ mvcc.entsCutAt L r.crev ents ∧
      mvcc.NoDelPutAt L r.crev ∧ (∀ x : Nat, (x : Int) ≤ r.crev → mvcc.KeyOnceAt L x)
  else mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty

theorem mvcc.keyImageM_off (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) :
    mvcc.keyImageM false L r D ↔ mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty := by
  unfold mvcc.keyImageM; simp

/-- **The received backend's image, by the mode** (draft; the pre's
`kbViewC (some d') γb' 1 (bucketMap L') ∗ kbNoCmp (some d') γb'` today): off, the whole `Key`
bucket at the log `L'` and no record; on, a view of the image's entries `ents` of the job's shape
at the records' revision `r.crev`, the records with the write right (`kbRecs`: the client's half of
the compaction-key flag, which the walk holds from `OpenBackend`'s `fkCl`), the compaction keys
well formed (`fkVM`, the merged ghost), and `keyImageM`'s pure facts. -/
def mvcc.restoreImageM (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (r : mvcc.CmpRecs) :
    IProp GF :=
  if d'.cm then
    iprop(∃ ents : List mvcc.KvEnt, mvcc.kbViewC (some d') γb' 1 (mvcc.bucketOfEnts ents) ∗
      mvcc.kbRecs (some d') γb' r ∗ backend.fkVM d'.γB true ∗
      ⌜mvcc.recsOk L r ∧ mvcc.recsPos r ∧ mvcc.entsCutAt L r.crev ents ∧ mvcc.NoDelPutAt L r.crev ∧
        (∀ x : Nat, (x : Int) ≤ r.crev → mvcc.KeyOnceAt L x)⌝)
  else iprop(mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
    ⌜r = mvcc.CmpRecs.empty⌝)

theorem mvcc.restoreImageM_off (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (r : mvcc.CmpRecs)
    (h : d'.cm = false) :
    mvcc.restoreImageM (GF := GF) d' γb' L r ⊣⊢
      mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
        ⌜r = mvcc.CmpRecs.empty⌝ := by
  unfold mvcc.restoreImageM; simp only [h, Bool.false_eq_true, ↓reduceIte]; exact .rfl

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

/-- **The new backend's post-lock hook, unset** (draft): the client's half of the real backend's
hook variable at `nil` (what `SetTxPostLockInsideApplyHook` later takes); none over mvcc's assumed
backend, which `restore()` never resumes over. -/
def mvcc.kbHookNil (kb : Option mvcc.KBReal) : IProp GF :=
  match kb with
  | none => iprop(False)
  | some d => backend.plHook d.γB func.nil

/-- **`LockInsideApply` with no hook set** (draft of the clause `batchTxSpecG` gains at the switch,
with `HN := kbHookNil kb`; the store-level nil-hook law of the approval list): from the session's
tokens and the unset hook, the lock, its resource `W` and the batch lock's invariant `P` itself
(no hook ran). -/
def mvcc.lockNilSpec (bt : GoInterfaceOk) (RT WT W P HN : IProp GF) (Locked : mvcc.Puts → IProp GF) :
    IProp GF :=
  iprop(□ (∀ Pre : IProp GF,
    {{ Pre ∗ RT ∗ WT ∗ HN }} (App (Val #(methods bt.ty go!"LockInsideApply" bt.v)) (Val #()))
    {{ RET #(); Locked [] ∗ W ∗ P ∗ Pre ∗ RT ∗ HN }}))

/-- **The real backend gives it** (proved, from the backend spec's nil arm, as `bt_lockIn` from its
hook arm): the bridge's instance of `lockNilSpec`, the store's `batchTxSpecG` clause at the switch
(`isKeyBackendG_of_backendC` passes it through). -/
theorem mvcc.bt_lockInNil (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    {P : backend.BParams} (hP : mvcc.bridgeParams P) (γ : backend.BNames) (W Pk : IProp GF) (b t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W Pk b ∗ backend.bF go!"batchTx" b ↦□ t ⊢
      mvcc.lockNilSpec ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty, #t⟩
        (mvcc.bkRTx γ P b) (backend.wbTok γ) W Pk (backend.plHook γ func.nil) (mvcc.bkLocked γ P b) := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩
  iunfold mvcc.lockNilSpec
  iintro !> %Pre %Φ !> ⟨Hpre, Hrt, Hwb, Hhk⟩ HΦ
  iunfold mvcc.bkRTx at Hrt
  icases Hrt with ⟨Hrd, Ho⟩
  wp_apply (hLI γ P W Pk b t backend.rdOpen (DFrac.own (1 : Qp).half) func.nil Pre iprop(Pk ∗ Pre))
      $$ [$Hb $Ht $Ho $Hhk $Hpre]
    as ⟨%st, Hl, %Hfree, HW, HQ, Ho, Hhk⟩
  · ileft
    isplitr
    · ipureintro; rfl
    iintro H; iexact H
  iapply HΦ
  icases HQ with ⟨HPk, Hpre⟩
  iframe HW HPk Hpre Hhk
  isplitl [Hl Hwb]
  · iunfold mvcc.bkLocked
    iexists st
    iunfold mvcc.bkLockedAt
    iframe
    ipureintro; exact mvcc.sessPuts_free hP Hfree
  iunfold mvcc.bkRTx
  iframe Hrd
  iexact Ho

/-- **What `Restore` lends for the compaction `restore()` resumes** (draft, in place of round 3's
`resumeCsM`, A2): on, when the records resume a compaction, the new backend's unset hook (lent,
given back: `Restore.specM`'s post has it again); else nothing. -/
def mvcc.resumeHookM (d' : mvcc.KBReal) (r : mvcc.CmpRecs) : IProp GF :=
  if d'.cm = true ∧ r.resumes = true then mvcc.kbHookNil (some d') else iprop(True)

theorem mvcc.resumeHookM_no (d' : mvcc.KBReal) (r : mvcc.CmpRecs) (h : r.resumes = false) :
    mvcc.resumeHookM (GF := GF) d' r = iprop(True) := by
  unfold mvcc.resumeHookM; simp [h]

/-- A real backend's mode is its record's. -/
theorem mvcc.kbCmpM_some_iff (d : mvcc.KBReal) : mvcc.kbCmpM (some d) ↔ d.cm = true := Iff.rfl

/-! ## `store.Restore` in either mode -/

/-- **Draft of `store.Restore.spec`, in either mode** (step 2; repaired after review rounds 3
and 4). Today's text but for the marked changes:
* the two `cm = false` premises become `d'.cm = d.cm` (the mode survives the install);
* `storeCloser s γ ∗ crevFrozen γ` becomes `restoreRightM s γ c` (on: the compaction right at the
  store's revision `c`, which `Restore` takes back: the stop channel's close, the stop token and the
  queue for `Stop`, whose post returns the last job's token with the old job's budgets
  `compactJobResM γ.kb`, and the run token, with which the jobs' share of the fields comes back);
* the received image by the mode at its compaction records `r` (`restoreImageM d' γb' L' r`: on,
  the entries of the job's shape at `r.crev`, the records with the compaction-key write right), the
  restored revision being what `restore()` computes from them, `r.crev`, with `c ≤ r.crev` (Q5 (a);
  the corner of Q7 excluded by M2's scope, `recsPos`), and the new backend's contract and clean read
  at the records (`storeBackendTR … r`, `keyCleanReadR … (kbRecs … r) r`: off, `r = empty`, today's,
  `storeBackendTR_empty`, `keyCleanReadR_empty`);
* on, the restored log's changes below the receipts' bound (`restoreBoundM`, Q8);
* new in the pre, all `True` off: the new job's slot `kbSRM (some d')`, the write-back supply of
  the new backend `kbWTSupplyM (some d')`, and, when the records resume a compaction, the new
  backend's unset hook (`resumeHookM`, A2: lent, given back);
* the post: `storeCloserM s γ' r.crev` in place of `storeCloser s γ'`, the unset hook back
  (`resumeHookM`), the old job's budgets `compactJobResM γ.kb` (for the old backend's `Close`: a
  reader's token and the safe-range slot), and the old pool's readers `nReaders - 1 - nJobRd γ.kb`
  (the job's reader came back in the budgets). -/
abbrev mvcc.store.Restore.specM : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ r.crev →
    mvcc.restoreBoundM (GF := GF) d' ([[], []] ++ R) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ ⌜∃ d, γ.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM s γ c ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗
      mvcc.idxCert γ.idx L ∗ ownToks γ.revs (2 ^ 63 - 3 - L.length) ∗
      (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
      mvcc.certOk γ ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendTR b' s (γ.withPhys p) P' r) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanReadR b' (mvcc.bucketViewC (γ.withPhys p)) (mvcc.storeRT (γ.withPhys p))
          (mvcc.kbRecs (γ.withPhys p).kb (γ.withPhys p).bucket r) r) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbRegRight (some d') ∗
      mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗ mvcc.resumeHookM d' r ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloserM s (γ.withPhys p') r.crev ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
      mvcc.hookP (γ.withPhys p') P' ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      mvcc.resumeHookM d' r ∗
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
from the drafted one at `c = -1` and no records (`r.crev = -1`). -/
theorem mvcc.store.Restore.spec_of_specM (h : mvcc.store.Restore.specM (GF := GF) (hG := hG)) :
    mvcc.store.Restore.spec (GF := GF) (hG := hG) := by
  intro s γ b' d' γb' P' L R hpre hR
  iintro %Φ ⟨#Hpkg, #Hs, %Hd, %Hd', Hcl, Hfs, Hwd, Hwf, Hwo, #Hfrz, Hcert, Htoks, Hq, #Hok,
    Hbk, Hkc, Hv, Hnc, Hrr, Hrts⟩ HΦ
  obtain ⟨d, hγd, hdcm⟩ := Hd
  obtain ⟨hoff, hj0, hsr, hws, -⟩ := mvcc.cmOff_true (GF := GF) d' Hd'
  obtain ⟨hoffd, hj0d, -, -, hjr⟩ := mvcc.cmOff_true (GF := GF) d hdcm
  have hoffγ : ¬ mvcc.kbCmpM γ.kb := by rw [hγd]; exact hoffd
  have hc : (-1 : Int) ≤ mvcc.CmpRecs.empty.crev := by rw [mvcc.CmpRecs.crev_empty]; exact Int.le_refl _
  have hb : mvcc.restoreBoundM (GF := GF) d' ([[], []] ++ R) := fun h => by rw [Hd'] at h; cases h
  iapply (h s γ b' d' γb' P' L R (-1) mvcc.CmpRecs.empty hpre hR hc hb) $$
    [Hcl Hfs Hwd Hwf Hwo Hcert Htoks Hq Hbk Hkc Hv Hnc Hrr Hrts]
  · iframe Hpkg Hs Hfs Hwd Hwf Hwo Hcert Htoks Hq Hok Hrr Hrts
    isplitr
    · ipureintro; exact ⟨d, hγd, by rw [Hd', hdcm]⟩
    isplitl [Hcl]
    · iapply (mvcc.restoreRightM_off s γ (-1) hoffγ).2
      iframe Hcl Hfrz; ipureintro; rfl
    isplitl [Hbk]
    · iintro %p %hp
      ihave Hk := Hbk $$ %p %hp
      rw [mvcc.storeBackendTR_empty]
      iexact Hk
    isplitl [Hkc]
    · iintro %p %hp
      ihave Hk := Hkc $$ %p %hp
      rw [mvcc.kbRecs_empty, mvcc.keyCleanReadR_empty]
      iexact Hk
    isplitl [Hv Hnc]
    · iapply (mvcc.restoreImageM_off d' γb' _ mvcc.CmpRecs.empty Hd').2
      iframe Hv Hnc; ipureintro; rfl
    rw [hsr, hws, mvcc.resumeHookM_no _ _ mvcc.CmpRecs.resumes_empty]
    isplitr <;> try isplitr
    all_goals itrivial
  have hr : mvcc.nReaders - 1 - mvcc.nJobRd γ.kb = mvcc.nReaders - 1 := by rw [hγd, hj0d]; rfl
  rw [hr]
  iintro !> ⟨%p', %hp', Hcl', Hfs, Hwd, Hwf, Hwo, #Hhook, #Hcert', Htoks, Hq, -, -, Hrd, Hrt⟩
  iapply HΦ
  iexists p'
  have hoffp : ¬ mvcc.kbCmpM (γ.withPhys p').kb := by
    rw [StoreNames.withPhys_kb, hp'.2]; exact hoff
  ihave Hcl' := (mvcc.storeCloserM_off s (γ.withPhys p') _ hoffp).1 $$ Hcl'
  iframe Hcl' Hfs Hwd Hwf Hwo Hhook Hcert' Htoks Hq Hrd Hrt
  ipureintro; exact hp'

/-! ## `watchableStore.Restore` in either mode -/

/-- **Draft of `watchableStore.Restore.spec`, in either mode** (step 2): today's text with
`store.Restore.specM`'s changes (the mode surviving the install, `restoreRightM`, the image by the
mode at its records `r` with `c ≤ r.crev`, the backend's contract and clean read at the records, the
receipts' bound on, the new job's slot and supply, the unset hook lent, `storeCloserM` at the new
names and `r.crev`, the old job's budgets back and `nReaders - 1 - nJobRd` old readers). Watchers
stay excluded in compaction mode (N1), so its `syncWatchers` part is unchanged. -/
abbrev mvcc.watchableStore.Restore.specM : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ r.crev →
    mvcc.restoreBoundM (GF := GF) d' ([[], []] ++ R) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ ⌜∃ d, γ.st.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM st γ.st c ∗ mvcc.writerFrag γ.st ∗ mvcc.writerOwn γ.st ∗
      mvcc.watchWriter γ L ∗
      mvcc.certOk γ.st ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendTR b' st (γ.st.withPhys p) P' r) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanReadR b' (mvcc.bucketViewC (γ.st.withPhys p)) (mvcc.storeRT (γ.st.withPhys p))
          (mvcc.kbRecs (γ.st.withPhys p).kb (γ.st.withPhys p).bucket r) r) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbRegRight (some d') ∗
      mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗ mvcc.resumeHookM d' r ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloserM st (γ.st.withPhys p') r.crev ∗
      mvcc.writerFrag (γ.st.withPhys p') ∗ mvcc.writerOwn (γ.st.withPhys p') ∗
      mvcc.hookP (γ.st.withPhys p') P' ∗
      mvcc.watchWriter γ ([[], []] ++ R) ∗
      mvcc.resumeHookM d' r ∗
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
  have hc : (-1 : Int) ≤ mvcc.CmpRecs.empty.crev := by rw [mvcc.CmpRecs.crev_empty]; exact Int.le_refl _
  have hb : mvcc.restoreBoundM (GF := GF) d' ([[], []] ++ R) := fun h => by rw [Hd'] at h; cases h
  iapply (h s st γ b' d' γb' P' L R (-1) mvcc.CmpRecs.empty hpre hR hc hb) $$
    [Hcl Hwf Hwo Hww Hbk Hkc Hv Hnc Hrr Hrts]
  · iframe Hpkg Hws Hwf Hwo Hww Hok Hrr Hrts
    isplitr
    · ipureintro; exact ⟨d, hγd, by rw [Hd', hdcm]⟩
    isplitl [Hcl]
    · iapply (mvcc.restoreRightM_off st γ.st (-1) hoffγ).2
      iframe Hcl Hfrz; ipureintro; rfl
    isplitl [Hbk]
    · iintro %p %hp
      ihave Hk := Hbk $$ %p %hp
      rw [mvcc.storeBackendTR_empty]
      iexact Hk
    isplitl [Hkc]
    · iintro %p %hp
      ihave Hk := Hkc $$ %p %hp
      rw [mvcc.kbRecs_empty, mvcc.keyCleanReadR_empty]
      iexact Hk
    isplitl [Hv Hnc]
    · iapply (mvcc.restoreImageM_off d' γb' _ mvcc.CmpRecs.empty Hd').2
      iframe Hv Hnc; ipureintro; rfl
    rw [hsr, hws, mvcc.resumeHookM_no _ _ mvcc.CmpRecs.resumes_empty]
    isplitr <;> try isplitr
    all_goals itrivial
  have hr : mvcc.nReaders - 1 - mvcc.nJobRd γ.st.kb = mvcc.nReaders - 1 := by rw [hγd, hj0d]; rfl
  rw [hr]
  iintro !> ⟨%p', %hp', Hcl', Hwf, Hwo, #Hhook, Hww, -, -, Hrd, Hrt⟩
  iapply HΦ
  iexists p'
  have hoffp : ¬ mvcc.kbCmpM (γ.st.withPhys p').kb := by
    rw [StoreNames.withPhys_kb, hp'.2]; exact hoff
  ihave Hcl' := (mvcc.storeCloserM_off st (γ.st.withPhys p') _ hoffp).1 $$ Hcl'
  iframe Hcl' Hwf Hwo Hhook Hww Hrd Hrt
  ipureintro; exact hp'

/-! ## The watchable store's closer in compaction mode -/

/-- **The watchable store's closer, a compacting store's** (draft; what the server keeps in compaction
mode, D22's `srvKVCloser` by the mode): the watchable store's own stop channel's close and waiter
(as `wsCloser`), and the inner store's restorable compaction right at `c` in place of its closer. -/
@[no_expose] def mvcc.wsCloserR (s st : Loc) (γs : mvcc.StoreNames) (c : Int) : IProp GF :=
  iprop(∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s ∗
    mvcc.compactRightR st γs c)

/-- **The compaction right from the watchable store's closer** (draft, in place of
today's discarding `compactRight_of_closer`: the closer is kept, not discarded; the step after `NewServer`'s last
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
    mvcc.storeCloserM (GF := GF) st γs c ∗
        (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s) ⊢
      mvcc.wsCloserR s st γs c := by
  iintro ⟨Hr, ⟨%stc, #Hstc, Hsc, Hw⟩⟩
  ihave Hr := (mvcc.storeCloserM_on st γs c h).1 $$ Hr
  iunfold mvcc.wsCloserR
  iexists stc
  iframe Hstc Hsc Hw Hr

/-! ## The store's payload for its scheduler (F2) -/

/-- **The store's stop channel is closed** (persistent; draft): the payload mvcc's store gives its
scheduler (`schedule.NewFIFOScheduler.specD`'s `Pay`). `NewStore`/`store.Restore` make the scheduler
before the stop channel (`kvstore.go:309-310`), so the payload names the channel through an
agreement name `γx` the store allocates first and fixes (discarded) once the channel is made; the
channel's broadcast is then `Done`. `Restore`/`Close` close `stopc` before `Stop`, so they have it
for `Scheduler.Stop.specD`; a job finding its context cancelled learns it
(`schedule.schedPay_elim`), and `compactBarrier`'s nonblocking receive on a `Done` broadcast needs no
proof of the not-ready branch (`ownBroadcastChan_nonblocking_receive`): the re-schedule branch is
dead, and no `schedLive` is needed. -/
def mvcc.stopPayD (γx : GName) : IProp GF :=
  iprop(∃ c : Loc, dghostVar γx DFrac.discard c ∗
    ∃ γc : ChanNames, ownBroadcastChan c γc iprop(True) Broadcast.Done)

instance mvcc.stopPayD_persistent (γx : GName) : Persistent (mvcc.stopPayD (GF := GF) γx) := by
  unfold mvcc.stopPayD; infer_instance

/-! ## The records read (`restore()`'s two reads of the compaction keys; proved) -/

/-- **Draft of `UnsafeReadFinishedCompact.spec` over the records' reader**: the finished record,
exactly (found and its revision, or `0` and not found). At no record it is today's at `nc = true`. -/
abbrev mvcc.UnsafeReadFinishedCompact.specR : Prop :=
  ∀ (rt : GoInterfaceOk) (r : mvcc.CmpRecs) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ mvcc.metaReadSpecR rt r Rd Tok ∗ mvcc.rdCap Rd Tok ∗ Tok }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact))
      (Val #(GoInterface.ok rt)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found); Tok ∗
      ⌜(found = true ∧ r.fin = some x) ∨ (found = false ∧ r.fin = none ∧ x = W64 0)⌝ }}

/-- **Draft of `UnsafeReadScheduledCompact.spec` over the records' reader**: the scheduled
record, exactly. -/
abbrev mvcc.UnsafeReadScheduledCompact.specR : Prop :=
  ∀ (rt : GoInterfaceOk) (r : mvcc.CmpRecs) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ mvcc.metaReadSpecR rt r Rd Tok ∗ mvcc.rdCap Rd Tok ∗ Tok }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact))
      (Val #(GoInterface.ok rt)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found); Tok ∗
      ⌜(found = true ∧ r.sched = some x) ∨ (found = false ∧ r.sched = none ∧ x = W64 0)⌝ }}

theorem mvcc.CmpRecs.at_fin (r : mvcc.CmpRecs) : r.at mvcc.finKeyBytes = r.fin := by
  unfold mvcc.CmpRecs.at; simp [mvcc.finKeyBytes, mvcc.schedKeyBytes]

set_option maxHeartbeats 800000 in
/-- **The records' fin read** (proved: today's proof over the records' reader; at no record,
today's spec at `nc = true`). -/
theorem mvcc.UnsafeReadFinishedCompact.wp_proofR
    (h0 : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (hT : mvcc.UnsafeReadFinishedCompact.spec (GF := GF) (hG := hG)) :
    mvcc.UnsafeReadFinishedCompact.specR (GF := GF) (hG := hG) := by
  intro rt r Rd Tok
  by_cases hr : r = mvcc.CmpRecs.empty
  · subst hr
    rw [mvcc.metaReadSpecR_empty]
    iintro %Φ ⟨#Hpkg, #Hrd, #Hcap, Htok⟩ HΦ
    iapply (hT rt true Rd Tok) $$ [$Htok]
    · iframe #
    iintro !> %x %found ⟨Htok, %Hf⟩
    iapply HΦ
    iframe Htok
    ipureintro
    obtain ⟨-, h1, h2⟩ := Hf
    right; exact ⟨h2 rfl, rfl, h1 (h2 rfl)⟩
  wp_start as ⟨#Hrd, #Hcap, Htok⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%skn, #Hskn, #Hsknv⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨⟨%bM, #HMetaG, -⟩, -⟩
  unfold mvcc.metaReadSpecR
  simp only [hr, ↓reduceIte]
  (try wp_auto)
  wp_bind (App (App (App (App (Val #(methods rt.ty _ rt.v)) (Val #bM)) (Val #skn)) (Val #(slice.nil)))
    (Val #(W64 0)))
  ihave #Hrd' := Hrd $$ %bM %skn %mvcc.finKeyBytes %DFrac.discard []
  · ipureintro; exact Or.inr rfl
  iapply Hrd' $$ [Htok]
  · iframe HMetaG Htok
    unfold mvcc.finKeyBytes
    iexact Hsknv
  inext
  iintro %ks %vs ⟨Htok, -, Hr⟩
  rw [mvcc.CmpRecs.at_fin]
  icases Hr with (⟨%Hnone, #Hks, #Hvs⟩ | ⟨%ksl, %vsl, %x, %Hx, #Hks, -, #Hvs, Hvsl⟩)
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl0 : vs.len = W64 0 := by
      simp only [List.length_nil] at h1; unfold sint.nat at h1; word
    wp_if_destruct
    all_goals try (exfalso; exact Hif hl0)
    (try wp_auto)
    iapply HΦ
    iframe Htok
    ipureintro
    right; exact ⟨by trivial, Hnone, by trivial⟩
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    obtain ⟨hxr, hx0⟩ := Hx
    iunfold mvcc.rdCap at Hcap
    icases Hcap $$ %vsl %(mvcc.revBytes ⟨x, W64 0⟩ false) Hvsl Htok with ⟨%dqv, Hvb, Hback⟩
    ihave Hvsl' : vsl ↦*{dqv} (mvcc.revBytes ⟨x, W64 0⟩ false ++ []) $$ [Hvb]
    · rw [List.append_nil]; iexact Hvb
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl1 : vs.len ≠ W64 0 := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1; intro h; rw [h] at h1
      simp at h1
    wp_if_destruct
    all_goals try (exfalso; exact hl1 Hif)
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vs.len := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1
      refine ⟨by decide, ?_⟩
      rw [show sint.Z (W64 0) = 0 by decide]
      have h3 : (sint.Z vs.len).toNat = 1 := h1.symm
      omega
    simp only [Hb0, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index vs (sint.Z (W64 0)) _ DFrac.discard vsl (by decide) $$ [$Hvs] as -
    · ipureintro; rfl
    wp_apply (h0 vsl ⟨x, W64 0⟩ [] dqv (by simp) hx0 (show (0 : Int) ≤ sint.Z (W64 0) by decide)) $$ [$Hvsl'] as Hvsl'
    (try wp_auto)
    iapply HΦ
    isplitl [Hvsl' Hback]
    · iapply Hback
      rw [List.append_nil] at *
      iexact Hvsl'
    ipureintro
    try simp only [mvcc.revVal_main]
    left; exact ⟨trivial, hxr⟩

theorem mvcc.CmpRecs.at_sched (r : mvcc.CmpRecs) : r.at mvcc.schedKeyBytes = r.sched := by
  unfold mvcc.CmpRecs.at; simp [mvcc.finKeyBytes, mvcc.schedKeyBytes]

set_option maxHeartbeats 800000 in
/-- **The records' sched read** (proved: today's proof over the records' reader; at no record,
today's spec at `nc = true`). -/
theorem mvcc.UnsafeReadScheduledCompact.wp_proofR
    (h0 : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (hT : mvcc.UnsafeReadScheduledCompact.spec (GF := GF) (hG := hG)) :
    mvcc.UnsafeReadScheduledCompact.specR (GF := GF) (hG := hG) := by
  intro rt r Rd Tok
  by_cases hr : r = mvcc.CmpRecs.empty
  · subst hr
    rw [mvcc.metaReadSpecR_empty]
    iintro %Φ ⟨#Hpkg, #Hrd, #Hcap, Htok⟩ HΦ
    iapply (hT rt true Rd Tok) $$ [$Htok]
    · iframe #
    iintro !> %x %found ⟨Htok, %Hf⟩
    iapply HΦ
    iframe Htok
    ipureintro
    obtain ⟨-, h1, h2⟩ := Hf
    right; exact ⟨h2 rfl, rfl, h1 (h2 rfl)⟩
  wp_start as ⟨#Hrd, #Hcap, Htok⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%skn, #Hskn, #Hsknv⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨⟨%bM, #HMetaG, -⟩, -⟩
  unfold mvcc.metaReadSpecR
  simp only [hr, ↓reduceIte]
  (try wp_auto)
  wp_bind (App (App (App (App (Val #(methods rt.ty _ rt.v)) (Val #bM)) (Val #skn)) (Val #(slice.nil)))
    (Val #(W64 0)))
  ihave #Hrd' := Hrd $$ %bM %skn %mvcc.schedKeyBytes %DFrac.discard []
  · ipureintro; exact Or.inl rfl
  iapply Hrd' $$ [Htok]
  · iframe HMetaG Htok
    unfold mvcc.schedKeyBytes
    iexact Hsknv
  inext
  iintro %ks %vs ⟨Htok, -, Hr⟩
  rw [mvcc.CmpRecs.at_sched]
  icases Hr with (⟨%Hnone, #Hks, #Hvs⟩ | ⟨%ksl, %vsl, %x, %Hx, #Hks, -, #Hvs, Hvsl⟩)
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl0 : vs.len = W64 0 := by
      simp only [List.length_nil] at h1; unfold sint.nat at h1; word
    wp_if_destruct
    all_goals try (exfalso; exact Hif hl0)
    (try wp_auto)
    iapply HΦ
    iframe Htok
    ipureintro
    right; exact ⟨by trivial, Hnone, by trivial⟩
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    obtain ⟨hxr, hx0⟩ := Hx
    iunfold mvcc.rdCap at Hcap
    icases Hcap $$ %vsl %(mvcc.revBytes ⟨x, W64 0⟩ false) Hvsl Htok with ⟨%dqv, Hvb, Hback⟩
    ihave Hvsl' : vsl ↦*{dqv} (mvcc.revBytes ⟨x, W64 0⟩ false ++ []) $$ [Hvb]
    · rw [List.append_nil]; iexact Hvb
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl1 : vs.len ≠ W64 0 := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1; intro h; rw [h] at h1
      simp at h1
    wp_if_destruct
    all_goals try (exfalso; exact hl1 Hif)
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vs.len := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1
      refine ⟨by decide, ?_⟩
      rw [show sint.Z (W64 0) = 0 by decide]
      have h3 : (sint.Z vs.len).toNat = 1 := h1.symm
      omega
    simp only [Hb0, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index vs (sint.Z (W64 0)) _ DFrac.discard vsl (by decide) $$ [$Hvs] as -
    · ipureintro; rfl
    wp_apply (h0 vsl ⟨x, W64 0⟩ [] dqv (by simp) hx0 (show (0 : Int) ≤ sint.Z (W64 0) by decide)) $$ [$Hvsl'] as Hvsl'
    (try wp_auto)
    iapply HΦ
    isplitl [Hvsl' Hback]
    · iapply Hback
      rw [List.append_nil] at *
      iexact Hvsl'
    ipureintro
    try simp only [mvcc.revVal_main]
    left; exact ⟨trivial, hxr⟩

/-! ## `store.restore`, generalized (item 18) -/

/-- **`restore()`'s lock round for the finished record** (draft; `kvstore.go:330-341`): none if the
image has no finished record; else `RevP0` gives, at `Lock`, the lock's part `dql` of
`compactMainRev` with `RevK0`, and `Unlock` takes it at the record with `RevK0` and gives `RevP` (the
second round's, today's `revLockW`). `NewStore`: private memory; `store.Restore`: the lock in
restoring mode, as today's round. -/
def mvcc.revFinW (s : Loc) (dql : DFrac) (fin : Option w64) (RevP0 RevP : IProp GF) : IProp GF :=
  match fin with
  | none => iprop(RevP0 -∗ RevP)
  | some x => iprop(∃ RevK0 : IProp GF,
      (∀ Ψ : val → IProp GF, RevP0 -∗
        ▷ (∀ v : w64, (s.[store, go!"compactMainRev"] ↦{dql} v : IProp GF) -∗ RevK0 -∗ Ψ #()) -∗
        WP (App (Val (s.[store, go!"revMu"] @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Lock"))
          (Val #())) {{ Ψ }}) ∗
      (∀ Ψ : val → IProp GF, (s.[store, go!"compactMainRev"] ↦{dql} x : IProp GF) -∗ RevK0 -∗
        ▷ (RevP -∗ Ψ #()) -∗
        WP (App (Val (s.[store, go!"revMu"] @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Unlock"))
          (Val #())) {{ Ψ }}))

/-- **What `restore()` has once the index is rebuilt and `s.revMu` released** (draft: today's
post, with the records' write right, `compactMainRev` at the finished record, and one receipt per
entry the rebuild took: `ents.length`, today's `logCh L'` for the whole bucket,
`logEnts_length`). -/
def mvcc.restoreDone (s : Loc) (γ : mvcc.StoreNames) (b : GoInterface) (ti : Loc) (q1 : Qp)
    (dqb dqi dqc : DFrac) (L' : mvcc.Log) (ents : List mvcc.KvEnt) (r : mvcc.CmpRecs)
    (RT RevQ : IProp GF) : IProp GF :=
  iprop(RT ∗ mvcc.kbMW γ.kb γ.bucket ∗ ⧗ ents.length ∗ RevQ ∗
    s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((L'.length : Int) - 1) : w64) ∗
    s.[store, go!"compactMainRev"] ↦{dqc} (r.fin.getD (W64 (-1))) ∗
    s.[store, go!"b"] ↦{dqb} b ∗
    s.[store, go!"kvindex"] ↦{dqi}
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface))

/-- **The resume, as `restore()`'s caller provides it** (draft): if the records resume a compaction,
`s.compactLockfree(sched)` from `restoreDone` ends in `Fin`, whatever it returns (`restore()` only
logs the error); else `restoreDone` is `Fin`. `store.Restore`'s proof provides it from
`compactLockfree.spec` (over `storeStopR`/`compactRightR`, the store's invariant re-established at
the new names first, the lent unset hook `resumeHookM` for `SetScheduledCompact`'s lock, the new
job's budgets and supply); `NewStore`'s, over a fresh bucket, never resumes. -/
def mvcc.resumeK (s : Loc) (r : mvcc.CmpRecs) (Done Fin : IProp GF) : IProp GF :=
  if r.resumes then
    iprop(∀ Ψ : val → IProp GF, Done -∗
      ▷ (∀ (ch : GoChan) (err : GoInterface), Fin -∗ Ψ (PairV #ch #err)) -∗
      WP (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree"))
        (Val #(r.sched.getD (W64 0)))) {{ Ψ }})
  else iprop(Done -∗ Fin)

/-- **Draft of `store.restore.spec`, generalized** (item 18; internal and proved today, not an
axiom: `store__restore.lean`, linked in `mvcc/Link.lean`; repaired after review round 4's A1). Today's
text but for the image's records `r` and entries `ents`:
* the backend's contract at the records (`isKeyBackendGR … (kbRecs γ.kb γ.bucket r) r`, the
  resource `kbRecs γ.kb γ.bucket r`), with `recsOk L' r`;
* the view over the image's bucket (`restoreViewR … (bucketOfEnts ents) r`: its clean read at the
  records), the entries of the job's shape at the restored revision with each key once per revision
  up to it (`entsCutAt L' r.crev ents`, `KeyOnceAt`);
* the index published at the restored revision's level: the lower bound `crevLb γ.idx r.crev` (the
  caller raises the authority to it first), the unlock's payload the view of `m` and the index
  (`isTreeIndex`, whose lock invariant is at the switch over `IdxCRepN`: today's `IdxCRep` cannot hold,
  `idxCRep_restore_counterexample`), with the receipts' bound, which the rebuild's receipts give only
  for the whole bucket: otherwise the caller's (`restoreBoundM`), the new disjunctive premise;
* the finished record's lock round (`revFinW`, the pair `RevP0`, `dql`), before today's;
* the post: `Fin`, where the caller's `resumeK` takes `restoreDone` (today's post, `compactMainRev`
  at the finished record, a receipt per entry) through the resumed compaction, if any.
At `r = empty`, `ents` the whole bucket, `RevP0 = RevP`, `Fin = restoreDone …` it is today's.

**Not proved** (A1's evidence, `notes/m2-storage-plan.md`, "After review round 4"): the WP proof is
today's (`store__restore.lean`) with the records' reads (`UnsafeReadFinishedCompact.wp_proofR`,
`UnsafeReadScheduledCompact.wp_proofR`, proved) and the found branch's lock round; what it cannot
get today is the rebuilt index's invariant at `r.crev` (`idx_publish` takes `IdxCRep (-1)`; the
pure fact is `idxRestore_cutStmt`, drafted, unproved, and the lock invariant's `HL` must become
`IdxCRepN`). Its caller `store.Restore` further needs the backend's view widened from the image's
bucket to the log's (the store's writer holds `bucketMap L'`, `restore_finish`; the job's deletions
leave the view, only reads miss them: a backend law at the open, `kbView_widen`, not drafted) and
the writer's receipts from `restoreBoundM` (`idxWriter`'s `⧗ (logCh L')`, which `⧗ ents.length`
cannot give). -/
abbrev mvcc.store.restore.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop)
    (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (MW SR SRh : IProp GF)
    (dqb dqi : DFrac)
    (R : mvcc.Log) (RevP0 RevP RevK RevQ : IProp GF) (dqc dql : DFrac) (q1 q2 : Qp)
    (r : mvcc.CmpRecs) (ents : List mvcc.KvEnt) (Fin : IProp GF),
  mvcc.restoreLogOk R → q1 + q2 = 1 → mvcc.recsOk ([[], []] ++ R) r →
    mvcc.entsCutAt ([[], []] ++ R) r.crev ents →
    (∀ x : Nat, (x : Int) ≤ r.crev → mvcc.KeyOnceAt ([[], []] ++ R) x) →
    (ents = mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length ∨
      mvcc.logCh ([[], []] ++ R) < receiptBound GF) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      mvcc.isKeyBackendGR b (mvcc.bucketView γ) RT WT (mvcc.kbRecs γ.kb γ.bucket r) r PutOk
        (mvcc.delKey γ) W Wi Dep Cmp P HF (Rb := Rb) (Bt := Bt) (SR := SR) (SRh := SRh) (MW := MW) ∗
      RT ∗ mvcc.kbRecs γ.kb γ.bucket r ∗ mvcc.restoreViewR b γ RT q R (mvcc.bucketOfEnts ents) r ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length ∗
      mvcc.idxWriterLb γ.idx ([[], []] ++ R) ∗ mvcc.crevLb γ.idx r.crev ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗ RevP0 ∗
      mvcc.revFinW s dql r.fin RevP0 RevP ∗
      mvcc.revLockW s q2 RevP RevK ∗
      mvcc.revUnlockW s q2 ([[], []] ++ R) RevK
        iprop((if R = [] then mvcc.bucketView γ q ∅ else mvcc.bucketViewC γ q (mvcc.bucketOfEnts ents)) ∗
          mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗
          ⌜mvcc.logCh ([[], []] ++ R) < receiptBound GF⌝) RevQ ∗
      mvcc.resumeK s r (mvcc.restoreDone s γ b ti q1 dqb dqi dqc ([[], []] ++ R) ents r RT RevQ) Fin }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; Fin }}

/-- The whole bucket's entries make the log's bucket. -/
theorem mvcc.bucketOfEnts_logEnts (L : mvcc.Log) :
    mvcc.bucketOfEnts (mvcc.logEnts L 0 L.length) = mvcc.bucketMap L := by
  unfold mvcc.bucketOfEnts mvcc.bucketMap; rw [mvcc.bucketOf_logEnts]

set_option maxHeartbeats 800000 in
/-- **At no record and the whole bucket the drafted `restore` reads as today** (the off-mode law,
proved): today's spec follows from `specR` at `r = empty`, `ents` the whole bucket's entries,
`RevP0 = RevP` and `Fin` today's post. -/
theorem mvcc.store.restore.spec_of_specR (h : mvcc.store.restore.specR (GF := GF) (hG := hG)) :
    mvcc.store.restore.spec (GF := GF) (hG := hG) := by
  intro s γ b le ti lg q P HF RT WT W Wi Dep Cmp PutOk Rb Bt MW SR SRh dqb dqi R RevP RevK RevQ dqc
    q1 q2 hR hq12
  iintro %Φ ⟨#Hpkg, Hb, #Hbk, Hrt, Hnc, Hview, Hkvi, Hix, Hig, #Hiw, #Hle, #Hlg, %Hlgnn, Hcur1, Hcmp,
    HRevP, HLk, HUl⟩ HΦ
  iunfold mvcc.idxLockG at Hig
  icases Hig with ⟨Hgn, #Hcl, Hgl, Hgc⟩
  have hrec : mvcc.recsOk ([[], []] ++ R) mvcc.CmpRecs.empty := by
    unfold mvcc.recsOk mvcc.CmpRecs.empty
    refine ⟨?_, ?_⟩ <;> intro x hx <;> cases hx
  have hko : ∀ x : Nat, (x : Int) ≤ mvcc.CmpRecs.empty.crev → mvcc.KeyOnceAt ([[], []] ++ R) x := by
    intro x hx; rw [mvcc.CmpRecs.crev_empty] at hx; omega
  iapply (h s γ b le ti lg q P HF RT WT W Wi Dep Cmp PutOk Rb Bt MW SR SRh dqb dqi R RevP RevP RevK
      RevQ dqc DFrac.discard q1 q2 mvcc.CmpRecs.empty (mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length)
      iprop(RT ∗ mvcc.kbMW γ.kb γ.bucket ∗
        ⧗ (mvcc.logCh ([[], []] ++ R)) ∗ RevQ ∗
        s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((([[], []] ++ R).length : Int) - 1) : w64) ∗
        s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗
        s.[store, go!"b"] ↦{dqb} b ∗
        s.[store, go!"kvindex"] ↦{dqi}
          (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface))
      hR hq12 hrec (mvcc.entsCutAt_full _ _) hko (Or.inl rfl)) $$
    [Hb Hrt Hnc Hview Hkvi Hix Hgn Hgl Hgc Hcur1 Hcmp HRevP HLk HUl]
  · rw [mvcc.kbRecs_empty, mvcc.isKeyBackendGR_empty, mvcc.bucketOfEnts_logEnts,
      mvcc.CmpRecs.crev_empty]
    ihave Hig : mvcc.idxLockG γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length $$ [Hgn Hgl Hgc]
    · iunfold mvcc.idxLockG
      iframe Hgn Hcl Hgl Hgc
    ihave Hview : mvcc.restoreViewR b γ RT q R (mvcc.bucketMap ([[], []] ++ R)) mvcc.CmpRecs.empty
        $$ [Hview]
    · iunfold mvcc.restoreView at Hview
      iunfold mvcc.restoreViewOut at Hview
      iunfold mvcc.restoreViewR
      by_cases hR0 : R = []
      · subst hR0
        simp only [↓reduceIte]
        icases Hview with ⟨Hv, -⟩
        iframe Hv
        ipureintro; exact ⟨rfl, trivial⟩
      · simp only [hR0, ↓reduceIte]
        rw [mvcc.kbRecs_empty, mvcc.keyCleanReadR_empty]
        iexact Hview
    ihave Hfw : mvcc.revFinW s DFrac.discard mvcc.CmpRecs.empty.fin RevP RevP $$ []
    · simp only [mvcc.CmpRecs.empty]
      iunfold mvcc.revFinW
      iintro H; iexact H
    iunfold mvcc.restoreViewOut at HUl
    ihave Hk : mvcc.resumeK s mvcc.CmpRecs.empty
        (mvcc.restoreDone s γ b ti q1 dqb dqi dqc ([[], []] ++ R)
          (mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length) mvcc.CmpRecs.empty RT RevQ)
        iprop(RT ∗ mvcc.kbMW γ.kb γ.bucket ∗
          ⧗ (mvcc.logCh ([[], []] ++ R)) ∗ RevQ ∗
          s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((([[], []] ++ R).length : Int) - 1) : w64) ∗
          s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗
          s.[store, go!"b"] ↦{dqb} b ∗
          s.[store, go!"kvindex"] ↦{dqi}
            (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface)) $$ []
    · iunfold mvcc.resumeK
      simp only [mvcc.CmpRecs.resumes_empty, Bool.false_eq_true, ↓reduceIte]
      unfold mvcc.restoreDone
      simp only [mvcc.CmpRecs.empty, Option.getD_none, mvcc.logEnts_length]
      iintro H
      iexact H
    iframe Hpkg Hb Hbk Hrt Hnc Hkvi Hix Hiw Hle Hlg Hcur1 Hcmp HRevP HLk Hcl Hig Hview Hfw HUl Hk
    ipureintro; exact Hlgnn
  iintro !> H
  iapply HΦ
  iexact H

/-! ## `store.Close` (review round 3, S2.4) -/

/-- **Draft of `store.Close.spec`, in either mode**: the right to close by the mode at the store's
compaction revision `c` (`storeCloserM`: off, today's `storeCloser`; on, the restorable
compaction right, whose queue is at `c`, not `-1`: today's `storeCloser` has its queue at `-1`, which
a store that compacted cannot give, `compactQueue_mono` only going up). `Close` closes `stopc`,
then `Stop` with the stop token, the queue and the payload (`stopPayD`), as `Restore` does.
Unreachable today (the server's `run` never returns, so `Cleanup` never closes the KV): Q3 does not
dissolve until a shutdown is modelled; this is what it then takes. -/
abbrev mvcc.store.Close.specM : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeCloserM s γ c }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Close")) (Val #()))
  {{ RET #(GoInterface.nil); True }}

/-- **Off, the drafted `Close` reads as today** (for a store that does not compact). -/
theorem mvcc.store.Close.spec_of_specM (h : mvcc.store.Close.specM (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (hoff : ¬ mvcc.kbCmpM γ.kb) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isStore s γ ∗ mvcc.storeCloser s γ }}
      (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Close")) (Val #()))
    {{ RET #(GoInterface.nil); True }} := by
  iintro %Φ ⟨#Hpkg, #Hs, Hcl⟩ HΦ
  iapply (h s γ (-1)) $$ [Hcl] HΦ
  iframe Hpkg Hs
  iapply (mvcc.storeCloserM_off s γ (-1) hoff).2
  iexact Hcl

end draft

end EtcdGrove
end Perennial
