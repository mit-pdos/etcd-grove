/-
The FIFO scheduler (`pkg/v3/schedule`): the scheduler (`NewFIFOScheduler` and `fifo`'s methods,
translated with their bodies and proved since 2026-10-22: "The `fifo` scheduler" below) and the
jobs (`NewJob`, `job.Do`, translated with bodies). Lean-first; mvcc's
compaction (`notes/decisions.md`, "mvcc: compaction") and the server's apply loop (the request
path's unit 4c: `notes/decisions.md`, "The server's goroutines: the FIFO scheduler as a chain of
saved postconditions, the construction premise").

**The scheduler** `isFifo f γ` (persistent; `NewFIFOScheduler` returns it) runs the jobs it is
given (`Schedule`: `Spec/go_etcd_io/etcd/pkg/v3/schedule/Scheduler__Schedule.lean`) one
at a time, in the order they were scheduled, in its own goroutine (`fifo.run`): the **run token**
`schedRunning γ` (exclusive: the token proper and the worker goroutine's thread token, which it
lends each job, as Perennial's `wp_fork` leaves a forked goroutine its own) is the worker's,
every job's `Do` receives it in its precondition and returns it in its postcondition (no
overlap). `Schedule` does not ask for the token (compaction's `compactBarrier` schedules a job
from inside a running job).

**A job** `jobIs γ j Pre Prev Post` (persistent): the `Job` interface value `j` whose `Do(ctx)`,
with the run token, `Pre` (from the scheduling goroutine) and `Prev` (from the worker: the
previous tracked job's `Post`, see below), for any context (`isContext`, possibly cancelled:
`Stop` runs the pending jobs with a cancelled one), returns with the token and `Post`.
`NewJob(name, do)` makes one from the closure `do`'s triple.

**The FIFO chain** (the request path's unit 4c, agreed with the mvcc session): a job is
scheduled *tracked* or *untracked*. The scheduling goroutine of tracked jobs holds the queue
`schedQueue γ Ps` (exclusive; the authority of `γ.jobs`, the saved propositions' names of the
tracked jobs' `Post`s in scheduling order, after the initial `True`); a tracked job's `Prev` is
the `Post` saved last (`savedProp`), so the worker, which keeps the latest tracked `Post` while
it runs the jobs in order, hands it to the next tracked job: the resources flow from job to job.
An untracked job takes and gives `True` (`Prev = Post = True`) and needs no queue, only that the
scheduler is never stopped (`schedLive`: mvcc's compaction).

**Stopping** (`Stop`): `fifo.Stop` cancels the context, waits for the worker to run
the pending jobs (with the cancelled context) and exit; a `Schedule` after it panics. So `Stop`
takes the stop token `schedStopTok γ` and the queue (no tracked `Schedule` after it), and an
untracked `Schedule` needs `schedLive γ` (the stop token given up for good: never stopped). mvcc's
store holds `isScheduler f γ := isFifo f γ ∗ schedLive γ` (`NewStore` gives up the stop token).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.schedule
public import Perennial.Proof.context
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.SavedProp
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schedule

open Iris Iris.BI

/-- The ghost names of a scheduler: its run token's and its record of the scheduled jobs. -/
structure SchedNames where
  /-- the run token (`schedRunning`: a `dghostVar` of `()` at the full fraction) -/
  run : GName
  /-- the queue (a monotone list of names, `schedQueue` its authority): first the stop token's
  name (`schedStopName`), then the saved propositions' names of the tracked jobs'
  postconditions, the initial `True` first -/
  jobs : GName
  /-- (M2, the storage side, 2026-10-30: review round 3's F2, the user's Q6) the payload: the name
  of a saved proposition the creator fixes (`schedPayIs`, `NewFIFOScheduler`'s `Pay`), which
  `Stop` presents (it cancels the scheduler's context, done with it) and a job finding the
  context cancelled learns (`schedPay_elim`) -/
  pay : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The run token** (exclusive): the scheduler's goroutine has it while it runs a job, with its
own thread token (`threadTok`: the worker is a goroutine, `fifo.run`, whose token Perennial's
`wp_fork` leaves it; it lends both to each job). -/
def schedRunning (γ : SchedNames) : IProp GF := iprop(dghostVar γ.run (DFrac.own 1) () ∗ threadTok)

/-- The name `n` of the scheduler's stop token: the first name of the queue (persistent: the
queue's names are fixed once there). -/
def schedStopName (γ : SchedNames) (n : GName) : IProp GF := monoListIdxOwn γ.jobs 0 n

instance schedStopName_persistent (γ : SchedNames) (n : GName) :
    Persistent (schedStopName (GF := GF) γ n) := by
  unfold schedStopName monoListIdxOwn; infer_instance

/-- **The stop token** (exclusive; `NewFIFOScheduler` returns it): the right to `Stop`. -/
def schedStopTok (γ : SchedNames) : IProp GF :=
  iprop(∃ n : GName, schedStopName γ n ∗ dghostVar n (DFrac.own 1) ())

/-- **Never stopped** (persistent): the stop token given up for good, what an untracked
`Schedule` needs (a `Schedule` after `Stop` panics). -/
def schedLive (γ : SchedNames) : IProp GF :=
  iprop(∃ n : GName, schedStopName γ n ∗ dghostVar n DFrac.discard ())

instance schedLive_persistent (γ : SchedNames) : Persistent (schedLive (GF := GF) γ) := by
  unfold schedLive; infer_instance

/-- **The queue** (exclusive; the tracked jobs' scheduling goroutine's): the stop token's name,
then the names of the tracked jobs' saved `Post`s in scheduling order, the first the initial
`True` (`NewFIFOScheduler`). Half of the list's authority: the scheduler's lock invariant
(`fifoLockInv`) holds the other half, so that a tracked `Schedule` appends under the lock. -/
def schedQueue (γ : SchedNames) (Ps : List GName) : IProp GF :=
  monoListAuthOwn γ.jobs (1 : Qp).half Ps

/-- A saved proposition (persistent; Perennial's `savedPropOwn`, discarded). -/
def savedProp (p : GName) (P : IProp GF) : IProp GF := savedPropOwn p DFrac.discard P

instance savedProp_persistent (p : GName) (P : IProp GF) :
    Persistent (savedProp (GF := GF) p P) := by
  unfold savedProp; infer_instance

/-- Saving a proposition. -/
theorem savedProp_alloc (P : IProp GF) : ⊢ |==> ∃ p : GName, savedProp (GF := GF) p P := by
  unfold savedProp
  iapply saved_prop_alloc P DFrac.discard (by exact DFrac.valid_discard)

/-- **The scheduler's payload is `P`** (persistent; M2, the storage side, review round 3's F2):
what a job that finds the scheduler's context cancelled learns (`schedPay_elim`), fixed when the
scheduler is made (`NewFIFOScheduler.spec`'s `Pay`). -/
def schedPayIs (γ : SchedNames) (P : IProp GF) : IProp GF := savedProp γ.pay P

instance schedPayIs_persistent (γ : SchedNames) (P : IProp GF) :
    Persistent (schedPayIs (GF := GF) γ P) := by
  unfold schedPayIs; infer_instance

/-- **The payload holds** (persistent): what `Stop` takes (it cancels the scheduler's context,
whose `PDone` it is part of), and what a job finding the context cancelled learns. -/
def schedPay (γ : SchedNames) : IProp GF :=
  iprop(∃ P : IProp GF, savedProp γ.pay P ∗ □ P)

instance schedPay_persistent (γ : SchedNames) : Persistent (schedPay (GF := GF) γ) := by
  unfold schedPay; infer_instance

/-- The payload, given. -/
theorem schedPay_of (γ : SchedNames) (P : IProp GF) :
    schedPayIs (GF := GF) γ P ∗ □ P ⊢ schedPay γ := by
  iintro ⟨#Hp, #HP⟩
  iunfold schedPay
  iexists P
  iunfold schedPayIs at Hp
  iframe Hp HP

/-- A scheduler whose payload is `True` (the server's `run`): `Stop`'s premise is free. -/
theorem schedPay_true (γ : SchedNames) :
    schedPayIs (GF := GF) γ iprop(True) ⊢ schedPay γ := by
  iintro #Hp
  iapply schedPay_of γ iprop(True)
  iframe Hp
  imodintro
  itrivial

/-- **A job's use of the payload**: the payload holds, a step later. -/
theorem schedPay_elim (γ : SchedNames) (P : IProp GF) :
    schedPayIs (GF := GF) γ P ∗ schedPay γ ⊢ ▷ □ P := by
  iintro ⟨#Hp, #Hq⟩
  iunfold schedPay at Hq
  icases Hq with ⟨%Q, #HQs, #HQ⟩
  iunfold schedPayIs at Hp
  iunfold savedProp at Hp HQs
  ihave #Heq := saved_prop_agree γ.pay DFrac.discard DFrac.discard Q P $$ HQs Hp
  inext
  ihave #Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨#H1, -⟩
  imodintro
  iapply H1
  iexact HQ

/-- **The worker has exited** (exclusive; M2, the storage side, review round 3's F2): the run
token's ghost part (`schedRunning`'s `dghostVar γ.run 1 ()`, without the worker's thread token).
`Scheduler.Stop.spec`'s post gives it (`<-f.donec` returns after `run`'s deferred
`close(f.donec)`, once no job runs or will run: `schedule.go:150-184`; the worker gives it up
there, `donecCarry`). -/
def schedDone (γ : SchedNames) : IProp GF := dghostVar γ.run (DFrac.own 1) ()

/-- Two run tokens are one too many. -/
theorem schedDone_excl (γ : SchedNames) :
    schedDone (GF := GF) γ ∗ schedDone γ ⊢ False := by
  iintro ⟨H1, H2⟩
  iunfold schedDone at H1 H2
  icombine H1 H2 gives %Hv
  obtain ⟨Hv, -⟩ := Hv
  exact absurd (DFrac.valid_own.1 Hv) (Qp_one_add_not_le 1)

/-- **What a `Schedule` takes besides the job and its `Pre`**: untracked (`none`): `Prev` and
`Post` are `True` and the scheduler is never stopped; tracked (`some (Ps, prev, post)`): the
queue, whose last name `prev` saves `Prev` (the previous tracked job's `Post`, or the initial
`True`), and the name `post` saving the job's `Post`. -/
def schedPre (γ : SchedNames) (tr : Option (List GName × GName × GName)) (Prev Post : IProp GF) :
    IProp GF :=
  match tr with
  | none => iprop(⌜Prev = iprop(True) ∧ Post = iprop(True)⌝ ∗ schedLive γ)
  | some (Ps, prev, post) =>
    iprop(schedQueue γ (Ps ++ [prev]) ∗ savedProp prev Prev ∗ savedProp post Post)

/-- **What a `Schedule` gives back**: nothing (untracked); the queue with the job's `post`
appended (tracked). -/
def schedPost (γ : SchedNames) (tr : Option (List GName × GName × GName)) : IProp GF :=
  match tr with
  | none => iprop(True)
  | some (Ps, prev, post) => schedQueue γ (Ps ++ [prev, post])

end defs

section jobs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [context_sem : _root_.Perennial.context.Assumptions]

/-- `jt`'s `Do(ctx)`, with the run token, `Pre` and `Prev`, for any context (possibly cancelled:
the job reads it, `ctx.Err()`; `Stop` runs the pending jobs with a cancelled one), returns the
token and `Post`; and (M2, the storage side, review round 3's F2) the context's cancellation
gives the scheduler's payload (`□ (cd.PDone -∗ schedPay γ)`: the worker gives the scheduler's
context, done with it), so a job finding its context cancelled learns it. -/
def jobDoSpec (γ : SchedNames) (jt : GoInterfaceOk) (Pre Prev Post : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedRunning γ ∗ Pre ∗ Prev ∗ _root_.Perennial.context.isContext ctx cd ∗
        □ (cd.PDone -∗ schedPay γ) }}
      (App (Val #(methods jt.ty go!"Do" jt.v)) (Val #(GoInterface.ok ctx)))
    {{ RET #(); schedRunning γ ∗ Post }})

instance jobDoSpec_persistent (γ : SchedNames) (jt : GoInterfaceOk) (Pre Prev Post : IProp GF) :
    Persistent (jobDoSpec γ jt Pre Prev Post) := by
  unfold jobDoSpec; infer_instance

/-- **A job** (persistent): the `Job` interface value `j` runs with preconditions `Pre` (the
scheduler's caller's) and `Prev` (the worker's: the previous tracked job's `Post`) and
postcondition `Post`, under the scheduler's run token. -/
def jobIs (γ : SchedNames) (j : GoInterface) (Pre Prev Post : IProp GF) : IProp GF :=
  iprop(∃ jt : GoInterfaceOk, ⌜j = GoInterface.ok jt⌝ ∗ jobDoSpec γ jt Pre Prev Post)

instance jobIs_persistent (γ : SchedNames) (j : GoInterface) (Pre Prev Post : IProp GF) :
    Persistent (jobIs γ j Pre Prev Post) := by
  unfold jobIs; infer_instance

/-- The closure `do`'s triple: with the run token, `Pre` and `Prev`, for any context (whose
cancellation gives the payload, as `jobDoSpec`), it returns with the token and `Post` (what
`NewJob` makes a job of). -/
def jobFnSpec (γ : SchedNames) (f : GoFunc) (Pre Prev Post : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedRunning γ ∗ Pre ∗ Prev ∗ _root_.Perennial.context.isContext ctx cd ∗
        □ (cd.PDone -∗ schedPay γ) }}
      (App (Val #f) (Val #(GoInterface.ok ctx)))
    {{ RET #(); schedRunning γ ∗ Post }})

instance jobFnSpec_persistent (γ : SchedNames) (f : GoFunc) (Pre Prev Post : IProp GF) :
    Persistent (jobFnSpec γ f Pre Prev Post) := by
  unfold jobFnSpec; infer_instance

end jobs

/-! ## The `fifo` scheduler

`NewFIFOScheduler` returns a `*fifo` (`schedule.go`), translated with its body: the pending jobs
`f.pendings` and the counters under `f.mu`, the worker goroutine `f.run`, which runs the head of
`f.pendings` outside the lock and removes it afterwards (`executeJob`'s deferred function), a
buffered channel `f.resume` that wakes the worker, the context `f.ctx` whose cancellation (`Stop`)
makes the worker run the pending jobs with the cancelled context and exit, closing `f.donec`
(which `Stop` waits for) and `f.resume`.

**The lock invariant** `fifoLockInv` holds the fields written after construction (`pendings` with
the slice's elements and capacity, `scheduled`, `finished`, `cancel`), the pending jobs' resources
(`itemOk`: each job's `jobIs` and `Pre`, and its tracking: untracked `Prev = Post = True`, tracked
the names `prev`, `post` of its saved `Prev` and `Post`), the queue's other half (`schedQueue` is
half the authority), the **baton** (the saved `Post` of the last tracked job run, the `Prev` of the
next one: `baton γ L b`, at index `b` of the queue `L`), and the worker's state `rs` (a ghost
variable the worker shares): `idle`, running an untracked job, running a tracked job whose `prev`
is at index `k` (the baton then with the job; `b = k + 1`), or `drained` (`Stop`'s cancellation
seen, the pending jobs taken). `chainOk L b items`: the tracked pending jobs' names are the queue's
from index `b` on, consecutively. Until `Stop`, `cancel` is the context's cancel function and the
`stopped` flag is `false` (fully owned); after it, `cancel` is `nil`, the flag is `true`
(persistent: `stopped`, the context's `PDone`) and the invariant holds `Stop`'s stop token and
a fraction of the queue's authority (`Stop` keeps a quarter, the worker takes part of the rest when
it drains), which every later `Schedule` contradicts (tracked: the queue's half beyond the whole;
untracked: `schedLive`, the stop token's discarded name).

**The channels' invariants**: `f.resume` is buffered until the worker closes it, which it does only
once the scheduler is stopped (its close right `rc` goes into the invariant), so `Schedule`, which
sends to it only while not stopped, never sends on a closed channel; `f.donec` is empty until the
worker closes it (its close right `dc`), and then holds `donecCarry`: the worker's fraction of
the final queue with the last tracked job's `Post`, which `Stop` takes (its quarter of the queue
agreeing on the list; `Stop` persists only half of the `stopped` flag and leaves the other half in
the baton's place).
-/

section fifoFields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- Field addresses of a `*fifo`. -/
abbrev fifoMu (l : Loc) : Loc := structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"mu" l
abbrev fifoPendings (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"pendings" l
abbrev fifoScheduled (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"scheduled" l
abbrev fifoFinished (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"finished" l
abbrev fifoCancel (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"cancel" l
abbrev fifoResume (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"resume" l
abbrev fifoDonec (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"donec" l
abbrev fifoCtx (l : Loc) : Loc := structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"ctx" l
abbrev fifoCond (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"finishCond" l
abbrev fifoLg (l : Loc) : Loc := structFieldRef go_etcd_io.etcd.pkg.v3.schedule.fifo go!"lg" l

end fifoFields

section fifo
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The worker's state, shared (half each) by the worker and the lock invariant. -/
inductive RunSt where
  /-- not running a job -/
  | idle
  /-- running an untracked job (the head of `f.pendings`) -/
  | runU
  /-- running a tracked job, whose `prev` is at index `k` of the queue -/
  | runT (k : Nat)
  /-- the pending jobs taken after `Stop` (the worker runs them, then exits) -/
  | drained
  deriving DecidableEq

/-- The encoding of a `RunSt` (for `Pos.Countable`). -/
def RunSt.enc : RunSt → Nat
  | .idle => 0
  | .runU => 1
  | .drained => 2
  | .runT k => k + 3

instance RunSt.countable : Pos.Countable RunSt :=
  countableOfLeftInverse RunSt.enc
    (fun n => match n with | 0 => .idle | 1 => .runU | 2 => .drained | k + 3 => .runT k)
    (fun a => by cases a <;> rfl)

/-- The names and the fixed values of a `fifo` scheduler (persistent facts of `fifoIs`). -/
structure FifoNames where
  /-- the worker's state (`dghostVar RunSt`, half each) -/
  w : GName
  /-- the `stopped` flag (`dghostVar Bool`) -/
  st : GName
  /-- `f.resume`'s close right (`dghostVar Unit`, the worker's) -/
  rc : GName
  /-- `f.donec`'s close right (`dghostVar Unit`, the worker's) -/
  dc : GName
  /-- the drain token (`dghostVar Unit`, the worker's until it takes the pending jobs) -/
  dr : GName
  /-- `f.resume` and its channel names -/
  rch : GoChan
  γr : ChanNames
  /-- `f.donec` and its channel names -/
  dch : GoChan
  γd : ChanNames
  /-- `f.ctx` and its names -/
  ctx : GoInterfaceOk
  γc : _root_.Perennial.context.ContextNames
  /-- the context's cancel function (`f.cancel` until `Stop`) -/
  cf : GoFunc
  /-- `f.finishCond` -/
  cnd : Loc
  /-- `f.lg` -/
  lg : Loc

/-- The scheduler is stopped (persistent): `Stop` has run its context's cancel function. -/
def stopped (F : FifoNames) : IProp GF := dghostVar F.st DFrac.discard true

instance stopped_persistent (F : FifoNames) : Persistent (stopped (GF := GF) F) := by
  unfold stopped; infer_instance

/-- The context of the scheduler: no values, no deadline, done once stopped, with the payload
(M2, the storage side: `Stop` presents it, a job finding the context cancelled learns it). -/
def fifoCtxDesc (γ : SchedNames) (F : FifoNames) : _root_.Perennial.context.ContextDesc (IProp GF) :=
  { Values := ∅, Deadline := none, Done_gn := F.γc, PDone := iprop(stopped F ∗ schedPay γ) }

/-- A pending job, as the lock invariant keeps it: the job, its `Pre`, `Prev` and `Post`, and
its tracking (`some (prev, post)`: the names of its saved `Prev` and `Post`). -/
structure JobItem (PROP : Type) where
  j : GoInterface
  Pre : PROP
  Prev : PROP
  Post : PROP
  tr : Option (GName × GName)

/-- A pending job's resources: the job, its `Pre`, and its tracking. -/
def itemOk (γ : SchedNames) (it : JobItem (IProp GF)) : IProp GF :=
  iprop(jobIs γ it.j it.Pre it.Prev it.Post ∗ it.Pre ∗
    match it.tr with
    | none => ⌜it.Prev = iprop(True) ∧ it.Post = iprop(True)⌝
    | some (pv, ps) => savedProp pv it.Prev ∗ savedProp ps it.Post)

/-- The tracked jobs among `items` are the queue's from index `b` on: the `k`-th has its `prev` at
index `b + k` of `L` and its `post` at `b + k + 1`, the last's `post` the queue's last name. -/
def chainOk (L : List GName) (b : Nat) (items : List (JobItem (IProp GF))) : Prop :=
  b < L.length ∧ (items.filterMap JobItem.tr).length + b + 1 = L.length ∧
  ∀ (k : Nat) (p : GName × GName), (items.filterMap JobItem.tr)[k]? = some p →
    L[b + k]? = some p.1 ∧ L[b + k + 1]? = some p.2

/-- The pending jobs' list as the lock invariant relates it to the items (the head the worker's
while it runs a job). -/
def pendOk (rs : RunSt) (js : List GoInterface) (items : List (JobItem (IProp GF))) : Prop :=
  match rs with
  | .runU => js.drop 1 = items.map JobItem.j ∧ js ≠ []
  | .runT _ => js.drop 1 = items.map JobItem.j ∧ js ≠ []
  | _ => js = items.map JobItem.j

/-- **The baton** at index `b` of the queue `L`: the proposition saved at that name, held. -/
def baton (L : List GName) (b : Nat) : IProp GF :=
  iprop(∃ (p : GName) (Q : IProp GF), ⌜L[b]? = some p⌝ ∗ savedProp p Q ∗ Q)

/-- What the baton is, by the worker's state: with the worker while it runs a tracked job (then
`b` is past the job's `prev`), else in the invariant, or nothing once drained (the drain token in
its place). -/
def batonAt (F : FifoNames) (L : List GName) (b : Nat) (rs : RunSt) : IProp GF :=
  match rs with
  | .runT k => iprop(⌜b = k + 1⌝)
  | .drained => dghostVar F.dr (DFrac.own 1) ()
  | _ => baton L b

/-- **The lock invariant of `f.mu`** (see the section's docstring). -/
def fifoLockInv (l : Loc) (γ : SchedNames) (F : FifoNames) : IProp GF :=
  iprop(∃ (sl : GoSlice) (js : List GoInterface) (items : List (JobItem (IProp GF))) (rs : RunSt)
      (L : List GName) (b : Nat) (cf : GoFunc) (sc fn : w64),
    "Hpend" ∷ fifoPendings l ↦ sl ∗
    "Hsl" ∷ sl ↦* js ∗
    "Hcap" ∷ ownSliceCap GoInterface sl (DFrac.own 1) ∗
    "Hsch" ∷ fifoScheduled l ↦ sc ∗
    "Hfin" ∷ fifoFinished l ↦ fn ∗
    "Hcf" ∷ fifoCancel l ↦ cf ∗
    "Hrs" ∷ dghostVar F.w (DFrac.own (1 : Qp).half) rs ∗
    "Hq" ∷ monoListAuthOwn γ.jobs (1 : Qp).half L ∗
    "%Hjs" ∷ ⌜pendOk rs js items ∧ chainOk L b items⌝ ∗
    "Hitems" ∷ ([∗list] it ∈ items, itemOk γ it) ∗
    "Hbaton" ∷ batonAt F L b rs ∗
    "Hst" ∷ ((⌜cf = F.cf⌝ ∗ dghostVar F.st (DFrac.own 1) false) ∨
      (⌜cf = func.nil⌝ ∗ stopped F ∗ schedStopTok γ ∗ ∃ q : Qp, monoListAuthOwn γ.jobs q L)))

/-- `f.resume`'s invariant: buffered until the worker closes it, once stopped. -/
def resumeInv (F : FifoNames) : IProp GF :=
  iprop(∃ l : List Unit, ownChan F.γr Unit (.Buffered l) ∨
    (ownChan F.γr Unit (.Closed l) ∗ dghostVar F.rc (DFrac.own 1) () ∗ stopped F))

/-- **What the worker hands `Stop` through `f.donec`** (2026-10-30, the repair, P11): a fraction
of the queue's authority at the final queue `L` (once stopped, frozen), with the last tracked
job's `Post` (the baton at `L`'s last index) and (M2, the storage side) the run token's ghost part
(`schedDone`: the worker has run its last job), or, once `Stop` took them, half of the `stopped`
flag in their place (`Stop` keeps the other half, which with the discarded rest excludes a second
taker). -/
def donecCarry (γ : SchedNames) (F : FifoNames) : IProp GF :=
  iprop(∃ (L : List GName) (q : Qp), monoListAuthOwn γ.jobs q L ∗
    ((baton L (L.length - 1) ∗ schedDone γ) ∨ dghostVar F.st (DFrac.own (1 : Qp).half) true))

/-- `f.donec`'s invariant: empty until the worker closes it, with `donecCarry`. -/
def donecInv (γ : SchedNames) (F : FifoNames) : IProp GF :=
  iprop(ownChan F.γd Unit (.Buffered []) ∨
    (ownChan F.γd Unit (.Closed []) ∗ dghostVar F.dc (DFrac.own 1) () ∗ donecCarry γ F))

def resumeN : Namespace := nroot .@ "schedule.fifo.resume"
def donecN : Namespace := nroot .@ "schedule.fifo.donec"

/-- **A `fifo` scheduler at `l`** (persistent): its mutex with the lock invariant, its fields
fixed after construction, its condition variable over the mutex, its channels with their
invariants, its context (done once stopped) and the context's cancel function (not `nil`). -/
def fifoIs (l : Loc) (γ : SchedNames) (F : FifoNames) : IProp GF :=
  iprop("#Hmu" ∷ sync.isMutex (fifoMu l) (fifoLockInv l γ F) ∗
    "#Hres" ∷ fifoResume l ↦□ F.rch ∗
    "#Hdone" ∷ fifoDonec l ↦□ F.dch ∗
    "#Hctx" ∷ fifoCtx l ↦□ (interface.ok F.ctx : GoInterface) ∗
    "#Hcndf" ∷ fifoCond l ↦□ F.cnd ∗
    "#Hlgf" ∷ fifoLg l ↦□ F.lg ∗
    "#Hcnd" ∷ sync.isCond F.cnd
      (interface.mk (go.GoType.PointerType sync.Mutex.ty) #(fifoMu l)) ∗
    "#Hrch" ∷ isChan F.rch F.γr Unit ∗
    "#Hdch" ∷ isChan F.dch F.γd Unit ∗
    "#Hrinv" ∷ inv resumeN (resumeInv F) ∗
    "#Hdinv" ∷ inv donecN (donecInv γ F) ∗
    "#Hisctx" ∷ _root_.Perennial.context.isContext F.ctx (fifoCtxDesc γ F) ∗
    "#Hcancel" ∷ _root_.Perennial.context.cancelSpec F.cf F.γc iprop(stopped F ∗ schedPay γ) ∗
    "%Hcfnn" ∷ ⌜F.cf ≠ func.nil⌝)

instance fifoIs_persistent (l : Loc) (γ : SchedNames) (F : FifoNames) :
    Persistent (fifoIs (GF := GF) l γ F) := by
  unfold fifoIs named; infer_instance

/-- The scheduler's `*fifo`, at the later-credit instance every proof uses (the context's specs
need it); nothing at the other (mvcc's store invariant is stated for any `HasLC`). -/
def fifoOf (f : GoInterface) (γ : SchedNames) : IProp GF :=
  iprop(∃ (l : Loc) (F : FifoNames),
      ⌜f = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.schedule.fifo.ty) #l⌝ ∗
      fifoIs l γ F)

instance fifoOf_persistent (f : GoInterface) (γ : SchedNames) :
    Persistent (fifoOf (GF := GF) f γ) := by
  unfold fifoOf; infer_instance

end fifo

section isFifo
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `*fifo` part of `isFifo`, by the later-credit instance (see `fifoOf`). -/
def isFifoOf (f : GoInterface) (γ : SchedNames) : IProp GF :=
  match hlc, hG, sem with
  | .hasLC, hG', sem' => fifoOf (hG := hG') (sem := sem') f γ
  | .hasNoLC, _, _ => iprop(True)

instance isFifoOf_persistent (f : GoInterface) (γ : SchedNames) :
    Persistent (isFifoOf (GF := GF) (hG := hG) f γ) := by
  unfold isFifoOf; cases hlc <;> infer_instance

/-- **The scheduler, as `Schedule`/`Stop` see it** (persistent): a non-nil `Scheduler` interface
value with its names; it is a `*fifo` (`fifoIs`, through `isFifoOf`). -/
def isFifo (f : GoInterface) (γ : SchedNames) : IProp GF :=
  iprop(⌜f ≠ GoInterface.nil⌝ ∗ (∃ L : List GName, monoListLbOwn γ.jobs L) ∗ isFifoOf f γ)

instance isFifo_persistent (f : GoInterface) (γ : SchedNames) :
    Persistent (isFifo (GF := GF) (hG := hG) f γ) := by
  unfold isFifo; infer_instance

end isFifo

section fifo2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The worker's resources** (`f.run`'s): the run token, its half of the state, idle, the close
rights of `f.resume` and `f.donec`, and the drain token. -/
def workerRes (γ : SchedNames) (F : FifoNames) : IProp GF :=
  iprop(schedRunning γ ∗ dghostVar F.w (DFrac.own (1 : Qp).half) RunSt.idle ∗
    dghostVar F.rc (DFrac.own 1) () ∗ dghostVar F.dc (DFrac.own 1) () ∗
    dghostVar F.dr (DFrac.own 1) ())

end fifo2

end schedule
end EtcdGrove
end Perennial
