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
(`restoreRightPostM`). Also drafted: the generalized `store.restore` (`store.restore.specR`, item
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
def mvcc.bucketThinnedAt (L : mvcc.Log) (c : Int) (m : mvcc.Bucket) : Prop :=
  (∀ k v, m.lookup k = some v → (mvcc.bucketMap L).lookup k = some v) ∧
  (∀ k, (mvcc.bucketMap L).lookup k ≠ none → m.lookup k = none → mvcc.KeyDel L c k)

/-- The full bucket is thinned at any revision. -/
theorem mvcc.bucketThinnedAt_full (L : mvcc.Log) (c : Int) : mvcc.bucketThinnedAt L c (mvcc.bucketMap L) :=
  ⟨fun _ _ h => h, fun _ h1 h2 => absurd h2 h1⟩

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

/-- The bytes stored at a record (`RevToBytes(Revision{Main: x})`). -/
def mvcc.recBytes (x : Option w64) : Option GoString := x.map (fun x => mvcc.revBytes ⟨x, W64 0⟩ false)

/-- **The backend's compaction keys as opened** (persistent; draft of the backend's records fact):
the client's flag stood at `n` when the backend was opened over data whose two compaction keys
hold `v` (finished, scheduled). At the switch: `OpenBackend`/`New` over bbolt's `D` give it at
`(fkInit D, (dget D meta fin, dget D meta sched))` beside `fkCl` (the ghost `γ.fkv`, discarded at
the open, carries it: `fkV γ w` becomes `∃ n v, …` of the same name), a put of a compaction key
raises the flag strictly (`fkPut`: `f` to `f + 1`), and the batch lock's and the readers' clause
(`fkOk`) gains `f = n → the state's keys are v`: so while the client holds its half at `n`, every
read of the keys returns `v` (`metaReadSpecR`). Rests on bbolt's data as the backend's proofs
already read it (no new axiom). -/
def backend.fkOpenD (γ : backend.BNames) (n : Nat) (v : Option GoString × Option GoString) :
    IProp GF :=
  dghostVar γ.fkv DFrac.discard (n, v)

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

/-- **A read of a compaction key under the records `r`** (draft; `metaReadSpec`'s generalization:
today's `metaReadSpec rt true` is its value at `empty`): the key's record, exactly: nothing if
absent, else the key and the record's bytes. At the switch `keyReadLocked`'s meta clause reads
`□ (NC -∗ NC ∗ □ metaReadSpecR rt r Rd Tok)` for a new parameter `r` (default `empty`), and
`keyCleanRead` passes it; `UnsafeReadFinishedCompact`/`UnsafeReadScheduledCompact` return the
record. -/
def mvcc.metaReadSpecR (rt : GoInterfaceOk) (r : mvcc.CmpRecs) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (kn : GoString) (dq : DFrac),
    ⌜mvcc.metaCompactKey kn⌝ →
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ Tok ∗ key ↦*{dq} kn }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); Tok ∗ key ↦*{dq} kn ∗
        ((⌜r.at kn = none⌝ ∗ ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice)) ∨
          ∃ (ksl vsl : GoSlice) (x : w64), ⌜r.at kn = some x⌝ ∗ ks ↦*□ [ksl] ∗ Rd ksl kn ∗
            vs ↦*□ [vsl] ∗ Rd vsl (mvcc.revBytes ⟨x, W64 0⟩ false)) }})

/-- **A received image's `Key` view and compaction records, by the mode** (draft of
`keyImage`'s use in `specSnap`, D22's `hkI`): off, today's `keyImage` (the whole bucket at `L`, no
record); on, the `Key` bucket `m` thinned at the records' revision `r.crev`, the `Meta` bucket's two
compaction keys holding the records' bytes, the records of `L`, and `r.crev` safe for readers
(`NoDelPutAt`). The walk's `restoreImageM` and the clean read's records come from it with the
backend's `fkOpenD`. -/
def mvcc.keyImageM (cm : Bool) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) : Prop :=
  if cm then ∃ m : mvcc.Bucket, (∀ k, backend.dget D mvcc.keyName k = m.lookup k) ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes =
        mvcc.recBytes r.fin ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes =
        mvcc.recBytes r.sched ∧
      mvcc.recsOk L r ∧ mvcc.bucketThinnedAt L r.crev m ∧ r.crev < L.length ∧
      mvcc.NoDelPutAt L r.crev
  else mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty

theorem mvcc.keyImageM_off (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) :
    mvcc.keyImageM false L r D ↔ mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty := by
  unfold mvcc.keyImageM; simp

/-- **The received backend's image, by the mode** (draft; the pre's
`kbViewC (some d') γb' 1 (bucketMap L') ∗ kbNoCmp (some d') γb'` today; review round 3's F1): off,
the whole `Key` bucket at the log `L'` and no record (`r = empty`, so the restored revision is
`-1`); on, a view of the `Key` bucket thinned at the records' revision `r.crev` (what `restore()`
computes from them, `CmpRecs.crev`), the records with the write right (`kbRecs`: the client's half
of the compaction-key flag, which the walk holds from `OpenBackend`'s `fkCl`), the records of the
log, `r.crev` safe for readers (`NoDelPutAt`, as `store.Compact`'s caller asserts), and the
compaction keys well formed (`fkV`). -/
def mvcc.restoreImageM (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (r : mvcc.CmpRecs) :
    IProp GF :=
  if d'.cm then
    iprop(∃ m : mvcc.Bucket, mvcc.kbViewC (some d') γb' 1 m ∗ mvcc.kbRecs (some d') γb' r ∗
      backend.fkV d'.γB true ∗
      ⌜mvcc.recsOk L r ∧ mvcc.bucketThinnedAt L r.crev m ∧ r.crev < L.length ∧
        mvcc.NoDelPutAt L r.crev⌝)
  else iprop(mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
    ⌜r = mvcc.CmpRecs.empty⌝)

theorem mvcc.restoreImageM_off (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (r : mvcc.CmpRecs)
    (h : d'.cm = false) :
    mvcc.restoreImageM (GF := GF) d' γb' L r ⊣⊢
      mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
        ⌜r = mvcc.CmpRecs.empty⌝ := by
  unfold mvcc.restoreImageM; simp only [h, Bool.false_eq_true, ↓reduceIte]; exact .rfl

/-- **The hook's contract for the compaction `restore()` resumes** (draft): on, when the records
resume a compaction, the new backend's hook `f` (`kbHookIs`, persistent) and the caller's
consistent-index contract for its `SetScheduledCompact` (`csContract`, as `store.Compact`'s caller
gives: the resumed `updateCompactRev`'s `LockInsideApply` runs the hook); otherwise only `Pre`,
handed back. -/
def mvcc.resumeCsM (d' : mvcc.KBReal) (γb' : GName) (r : mvcc.CmpRecs) (P' : IProp GF) (f : val)
    (Pre Q Post : IProp GF) : IProp GF :=
  if d'.cm = true ∧ r.resumes = true then
    iprop(mvcc.kbHookIs (some d') γb' f ∗ mvcc.csContract P' f Pre Q Post)
  else Pre

/-- What the resumed compaction's contract gives back: `Post` if it ran, else `Pre`. -/
def mvcc.resumePostM (d' : mvcc.KBReal) (r : mvcc.CmpRecs) (Pre Post : IProp GF) : IProp GF :=
  if d'.cm = true ∧ r.resumes = true then Post else Pre

theorem mvcc.resumeCsM_no (d' : mvcc.KBReal) (γb' : GName) (r : mvcc.CmpRecs) (P' : IProp GF)
    (f : val) (Pre Q Post : IProp GF) (h : r.resumes = false) :
    mvcc.resumeCsM (GF := GF) d' γb' r P' f Pre Q Post = Pre := by
  unfold mvcc.resumeCsM; simp [h]

theorem mvcc.resumePostM_no (d' : mvcc.KBReal) (r : mvcc.CmpRecs) (Pre Post : IProp GF)
    (h : r.resumes = false) : mvcc.resumePostM (GF := GF) d' r Pre Post = Pre := by
  unfold mvcc.resumePostM; simp [h]

/-- A real backend's mode is its record's. -/
theorem mvcc.kbCmpM_some_iff (d : mvcc.KBReal) : mvcc.kbCmpM (some d) ↔ d.cm = true := Iff.rfl

/-! ## `store.Restore` in either mode -/

/-- **Draft of `store.Restore.spec`, in either mode** (step 2; repaired after review round 3).
Today's text but for the marked changes:
* the two `cm = false` premises become `d'.cm = d.cm` (the mode survives the install; `envAgree`'s
  mode clause, N1/S5', stays true of the new names);
* `storeCloser s γ ∗ crevFrozen γ` becomes `restoreRightM s γ c` (on: the compaction right at the
  store's revision `c`, which `Restore` takes back: the stop channel's close, the stop token and the
  queue for `Stop`, whose post returns the last job's token with the old job's budgets
  `compactJobResM γ.kb`, and the run token, with which the jobs' share of the fields comes back);
* the received image by the mode at its compaction records `r` (`restoreImageM d' γb' L' r`: on,
  the thinned bucket, the records with the compaction-key write right), the restored revision being
  what `restore()` computes from them, `r.crev`, with `c ≤ r.crev` (Q5 (a): the compaction revision
  is logical and never lowered; **false in one reachable corner**, a scheduled, unfinished
  compaction at revision `0`: `notes/m2-storage-plan.md`, Q7), and `keyCleanRead`'s `NC` the records
  (`kbRecs … r`: off, `r = empty`, today's `kbNoCmp`);
* new in the pre, all `True` or `Pre` off: the new job's slot `kbSRM (some d')`, the write-back
  supply of the new backend `kbWTSupplyM (some d')`, and, when the records resume a compaction, the
  new backend's hook `f` with the caller's contract for it (`resumeCsM`; `store.Compact`'s caller
  gives the same);
* the post: `restoreRightPostM s γ' r.crev` in place of `storeCloser s γ'`, the contract's result
  (`resumePostM`: `Post` if a compaction was resumed, else `Pre`), the old job's budgets
  `compactJobResM γ.kb` (for the old backend's `Close`: a reader's token and the safe-range slot),
  and the old pool's readers `nReaders - 1 - nJobRd γ.kb` (the job's reader came back in the
  budgets). -/
abbrev mvcc.store.Restore.specM : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs) (f : val) (Pre Q Post : IProp GF),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ r.crev →
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
          (mvcc.kbRecs (γ.withPhys p).kb (γ.withPhys p).bucket r)) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbRegRight (some d') ∗
      mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗
      mvcc.resumeCsM d' γb' r P' f Pre Q Post ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.restoreRightPostM s (γ.withPhys p') r.crev ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
      mvcc.hookP (γ.withPhys p') P' ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      mvcc.resumePostM d' r Pre Post ∗
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
from the drafted one at `c = -1`, no records (`r.crev = -1`) and the contract `True`. -/
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
  iapply (h s γ b' d' γb' P' L R (-1) mvcc.CmpRecs.empty #() iprop(True) iprop(True) iprop(True)
      hpre hR hc) $$
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
      rw [mvcc.kbRecs_empty]
      iexact Hk
    isplitl [Hv Hnc]
    · iapply (mvcc.restoreImageM_off d' γb' _ mvcc.CmpRecs.empty Hd').2
      iframe Hv Hnc; ipureintro; rfl
    rw [hsr, hws, mvcc.resumeCsM_no _ _ _ _ _ _ _ _ mvcc.CmpRecs.resumes_empty]
    isplitr <;> try isplitr
    all_goals itrivial
  have hr : mvcc.nReaders - 1 - mvcc.nJobRd γ.kb = mvcc.nReaders - 1 := by rw [hγd, hj0d]; rfl
  rw [hr]
  iintro !> ⟨%p', %hp', Hcl', Hfs, Hwd, Hwf, Hwo, #Hhook, #Hcert', Htoks, Hq, -, -, Hrd, Hrt⟩
  iapply HΦ
  iexists p'
  have hoffp : ¬ mvcc.kbCmpM (γ.withPhys p').kb := by
    rw [StoreNames.withPhys_kb, hp'.2]; exact hoff
  ihave Hcl' := (mvcc.restoreRightPostM_off s (γ.withPhys p') _ hoffp).1 $$ Hcl'
  iframe Hcl' Hfs Hwd Hwf Hwo Hhook Hcert' Htoks Hq Hrd Hrt
  ipureintro; exact hp'

/-! ## `watchableStore.Restore` in either mode -/

/-- **Draft of `watchableStore.Restore.spec`, in either mode** (step 2): today's text with
`store.Restore.specM`'s changes (the mode surviving the install, `restoreRightM`, the image by the
mode at its records `r` with `c ≤ r.crev`, the clean read's records, the new job's slot and supply,
the resumed compaction's hook contract, `restoreRightPostM` at the new names and `r.crev`, the
contract's result, the old job's budgets back and `nReaders - 1 - nJobRd` old readers). Watchers stay
excluded in compaction mode (N1), so its `syncWatchers` part is unchanged. -/
abbrev mvcc.watchableStore.Restore.specM : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs) (f : val) (Pre Q Post : IProp GF),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ r.crev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ ⌜∃ d, γ.st.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM st γ.st c ∗ mvcc.writerFrag γ.st ∗ mvcc.writerOwn γ.st ∗
      mvcc.watchWriter γ L ∗
      mvcc.certOk γ.st ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendT b' st (γ.st.withPhys p) P') ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanRead b' (mvcc.bucketViewC (γ.st.withPhys p)) (mvcc.storeRT (γ.st.withPhys p))
          (mvcc.kbRecs (γ.st.withPhys p).kb (γ.st.withPhys p).bucket r)) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbRegRight (some d') ∗
      mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗
      mvcc.resumeCsM d' γb' r P' f Pre Q Post ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.restoreRightPostM st (γ.st.withPhys p') r.crev ∗
      mvcc.writerFrag (γ.st.withPhys p') ∗ mvcc.writerOwn (γ.st.withPhys p') ∗
      mvcc.hookP (γ.st.withPhys p') P' ∗
      mvcc.watchWriter γ ([[], []] ++ R) ∗
      mvcc.resumePostM d' r Pre Post ∗
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
  iapply (h s st γ b' d' γb' P' L R (-1) mvcc.CmpRecs.empty #() iprop(True) iprop(True)
      iprop(True) hpre hR hc) $$
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
      rw [mvcc.kbRecs_empty]
      iexact Hk
    isplitl [Hv Hnc]
    · iapply (mvcc.restoreImageM_off d' γb' _ mvcc.CmpRecs.empty Hd').2
      iframe Hv Hnc; ipureintro; rfl
    rw [hsr, hws, mvcc.resumeCsM_no _ _ _ _ _ _ _ _ mvcc.CmpRecs.resumes_empty]
    isplitr <;> try isplitr
    all_goals itrivial
  have hr : mvcc.nReaders - 1 - mvcc.nJobRd γ.st.kb = mvcc.nReaders - 1 := by rw [hγd, hj0d]; rfl
  rw [hr]
  iintro !> ⟨%p', %hp', Hcl', Hwf, Hwo, #Hhook, Hww, -, -, Hrd, Hrt⟩
  iapply HΦ
  iexists p'
  have hoffp : ¬ mvcc.kbCmpM (γ.st.withPhys p').kb := by
    rw [StoreNames.withPhys_kb, hp'.2]; exact hoff
  ihave Hcl' := (mvcc.restoreRightPostM_off st (γ.st.withPhys p') _ hoffp).1 $$ Hcl'
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
    mvcc.restoreRightPostM (GF := GF) st γs c ∗
        (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter s) ⊢
      mvcc.wsCloserR s st γs c := by
  iintro ⟨Hr, ⟨%stc, #Hstc, Hsc, Hw⟩⟩
  ihave Hr := (mvcc.restoreRightPostM_on st γs c h).1 $$ Hr
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

/-- **What `restore()` has once the index is rebuilt and `s.revMu` released** (draft: today's post,
with the records' write right and `compactMainRev` at the finished record). -/
def mvcc.restoreDone (s : Loc) (γ : mvcc.StoreNames) (b : GoInterface) (ti : Loc) (q1 : Qp)
    (dqb dqi dqc : DFrac) (L' : mvcc.Log) (r : mvcc.CmpRecs) (RT RevQ : IProp GF) : IProp GF :=
  iprop(RT ∗ mvcc.kbMW γ.kb γ.bucket ∗ ⧗ (mvcc.logCh L') ∗ RevQ ∗
    s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((L'.length : Int) - 1) : w64) ∗
    s.[store, go!"compactMainRev"] ↦{dqc} (r.fin.getD (W64 (-1))) ∗
    s.[store, go!"b"] ↦{dqb} b ∗
    s.[store, go!"kvindex"] ↦{dqi}
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface))

/-- **The resume, as `restore()`'s caller provides it** (draft): if the records resume a compaction,
`s.compactLockfree(sched)` from `restoreDone` ends in `Fin`, whatever it returns (`restore()` only
logs the error); else `restoreDone` is `Fin`. `store.Restore`'s proof provides it from
`compactLockfree.spec` (over `storeStopR`/`compactRightR`, the store's invariant re-established at
the new names first, the caller's `resumeCsM`, the new job's budgets and supply); `NewStore`'s, over a
fresh bucket, never resumes. -/
def mvcc.resumeK (s : Loc) (r : mvcc.CmpRecs) (Done Fin : IProp GF) : IProp GF :=
  if r.resumes then
    iprop(∀ Ψ : val → IProp GF, Done -∗
      ▷ (∀ (ch : GoChan) (err : GoInterface), Fin -∗ Ψ (PairV #ch #err)) -∗
      WP (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree"))
        (Val #(r.sched.getD (W64 0)))) {{ Ψ }})
  else iprop(Done -∗ Fin)

/-- **Draft of `store.restore.spec`, generalized** (item 18; internal and proved today, not an axiom:
`store__restore.lean`, linked in `mvcc/Link.lean`): today's text but for the records `r` of the
image, read in place of `kbNoCmp`:
* `kbNoCmp γ.kb γ.bucket` (the resource and `isKeyBackendG`'s `NC`) becomes `kbRecs γ.kb γ.bucket r`
  (`kbRecs_empty`: today's at no record), with `recsOk L' r`;
* the finished record's lock round (`revFinW`, the new pair `RevP0`, `dql`), before today's;
* the post: `Fin`, where the caller's `resumeK` takes `restoreDone` (today's post, `compactMainRev`
  at the finished record) through the resumed compaction, if any.
At `r = empty` with `RevP0 = RevP`, `Fin = restoreDone …` it is today's. -/
abbrev mvcc.store.restore.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop)
    (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (MW SR SRh : IProp GF)
    (dqb dqi : DFrac)
    (R : mvcc.Log) (RevP0 RevP RevK RevQ : IProp GF) (dqc dql : DFrac) (q1 q2 : Qp)
    (r : mvcc.CmpRecs) (Fin : IProp GF),
  mvcc.restoreLogOk R → q1 + q2 = 1 → mvcc.recsOk ([[], []] ++ R) r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT (mvcc.kbRecs γ.kb γ.bucket r) PutOk
        (mvcc.delKey γ) W Wi Dep Cmp P HF (Rb := Rb) (Bt := Bt) (SR := SR) (SRh := SRh) (MW := MW) ∗
      RT ∗ mvcc.kbRecs γ.kb γ.bucket r ∗ mvcc.restoreView b γ RT q R ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length ∗
      mvcc.idxWriterLb γ.idx ([[], []] ++ R) ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗ RevP0 ∗
      mvcc.revFinW s dql r.fin RevP0 RevP ∗
      mvcc.revLockW s q2 RevP RevK ∗
      mvcc.revUnlockW s q2 ([[], []] ++ R) RevK
        iprop(mvcc.restoreViewOut γ q R ∗ mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗
          ⌜mvcc.logCh ([[], []] ++ R) < receiptBound GF⌝) RevQ ∗
      mvcc.resumeK s r (mvcc.restoreDone s γ b ti q1 dqb dqi dqc ([[], []] ++ R) r RT RevQ) Fin }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; Fin }}

/-! ## `store.Close` (review round 3, S2.4) -/

/-- **Draft of `store.Close.spec`, in either mode**: the right to close by the mode at the store's
compaction revision `c` (`restoreRightPostM`: off, today's `storeCloser`; on, the restorable
compaction right, whose queue is at `c`, not `-1`: today's `storeCloser` has its queue at `-1`, which
a store that compacted cannot give, `compactQueue_mono` only going up). `Close` closes `stopc`,
then `Stop` with the stop token, the queue and the payload (`stopPayD`), as `Restore` does.
Unreachable today (the server's `run` never returns, so `Cleanup` never closes the KV): Q3 does not
dissolve until a shutdown is modelled; this is what it then takes. -/
abbrev mvcc.store.Close.specM : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.restoreRightPostM s γ c }}
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
  iapply (mvcc.restoreRightPostM_off s γ (-1) hoff).2
  iexact Hcl

end draft

end EtcdGrove
end Perennial
