/-
The FIFO scheduler (`pkg/v3/schedule`): the trust boundary of the scheduler (`fifo`'s methods
are names-only) and the jobs (`NewJob`, `job.Do`, translated with bodies). Lean-first; mvcc's
compaction (`notes/decisions.md`, "mvcc: compaction") and the server's apply loop (the request
path's unit 4c: `notes/decisions.md`, "The server's goroutines: the FIFO scheduler as a chain of
saved postconditions, the construction premise").

**The scheduler** `isFifo f γ` (persistent; `NewFIFOScheduler` returns it) runs the jobs it is
given (`Schedule`, an axiom: `Spec/go_etcd_io/etcd/pkg/v3/schedule/Scheduler__Schedule.lean`) one
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

**Stopping** (`Stop`, an axiom): `fifo.Stop` cancels the context, waits for the worker to run
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

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The run token** (exclusive): the scheduler's goroutine has it while it runs a job, with its
own thread token (`threadTok`: the worker is a goroutine, `fifo.run`, whose token Perennial's
`wp_fork` leaves it; it lends both to each job). -/
def schedRunning (γ : SchedNames) : IProp GF := iprop(dghostVar γ.run (DFrac.own 1) () ∗ threadTok)

/-- **The scheduler, as `Schedule`/`Stop` see it** (persistent): a non-nil `Scheduler` interface
value with its names. -/
def isFifo (f : GoInterface) (γ : SchedNames) : IProp GF :=
  iprop(⌜f ≠ GoInterface.nil⌝ ∗ ∃ L : List GName, monoListLbOwn γ.jobs L)

instance isFifo_persistent (f : GoInterface) (γ : SchedNames) :
    Persistent (isFifo (GF := GF) f γ) := by
  unfold isFifo; infer_instance

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

/-- **A scheduler that is never stopped** (persistent; mvcc's store's): untracked jobs only. -/
def isScheduler (f : GoInterface) (γ : SchedNames) : IProp GF :=
  iprop(isFifo f γ ∗ schedLive γ)

instance isScheduler_persistent (f : GoInterface) (γ : SchedNames) :
    Persistent (isScheduler (GF := GF) f γ) := by
  unfold isScheduler; infer_instance

/-- Giving up the stop token: the scheduler is never stopped. -/
theorem schedLive_of_stopTok (γ : SchedNames) :
    ⊢ schedStopTok (GF := GF) γ ==∗ schedLive γ := by
  unfold schedStopTok schedLive
  iintro ⟨%n, #Hn, H⟩
  imod dghostVar_persist $$ H with #H
  imodintro
  iexists n
  iframe Hn H

/-- **The queue** (exclusive; the tracked jobs' scheduling goroutine's): the stop token's name,
then the names of the tracked jobs' saved `Post`s in scheduling order, the first the initial
`True` (`NewFIFOScheduler`). -/
def schedQueue (γ : SchedNames) (Ps : List GName) : IProp GF := monoListAuthOwn γ.jobs 1 Ps

/-- A saved proposition (persistent; Perennial's `savedPropOwn`, discarded). -/
def savedProp (p : GName) (P : IProp GF) : IProp GF := savedPropOwn p DFrac.discard P

instance savedProp_persistent (p : GName) (P : IProp GF) :
    Persistent (savedProp (GF := GF) p P) := by
  unfold savedProp; infer_instance

/-- Saving a proposition. -/
theorem savedProp_alloc (P : IProp GF) : ⊢ |==> ∃ p : GName, savedProp (GF := GF) p P := by
  unfold savedProp
  iapply saved_prop_alloc P DFrac.discard (by exact DFrac.valid_discard)

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [context_sem : _root_.Perennial.context.Assumptions]

/-- `jt`'s `Do(ctx)`, with the run token, `Pre` and `Prev`, for any context (possibly cancelled:
the job reads it, `ctx.Err()`; `Stop` runs the pending jobs with a cancelled one), returns the
token and `Post`. -/
def jobDoSpec (γ : SchedNames) (jt : GoInterfaceOk) (Pre Prev Post : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedRunning γ ∗ Pre ∗ Prev ∗ _root_.Perennial.context.isContext ctx cd }}
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

/-- The closure `do`'s triple: with the run token, `Pre` and `Prev`, for any context, it returns
with the token and `Post` (what `NewJob` makes a job of). -/
def jobFnSpec (γ : SchedNames) (f : GoFunc) (Pre Prev Post : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedRunning γ ∗ Pre ∗ Prev ∗ _root_.Perennial.context.isContext ctx cd }}
      (App (Val #f) (Val #(GoInterface.ok ctx)))
    {{ RET #(); schedRunning γ ∗ Post }})

instance jobFnSpec_persistent (γ : SchedNames) (f : GoFunc) (Pre Prev Post : IProp GF) :
    Persistent (jobFnSpec γ f Pre Prev Post) := by
  unfold jobFnSpec; infer_instance

end jobs

end schedule
end EtcdGrove
end Perennial
