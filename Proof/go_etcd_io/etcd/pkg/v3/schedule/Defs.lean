/-
The FIFO scheduler (`pkg/v3/schedule`) as mvcc's compaction uses it: the trust boundary of the
scheduler (`fifo`'s methods are names-only), and the jobs (`NewJob`, `job.Do`, translated with
bodies). Lean-first; `notes/decisions.md`, "mvcc: compaction".

**The scheduler** `isScheduler f γ` (persistent; `NewFIFOScheduler` returns it) runs the jobs it
is given (`Schedule`, an axiom: `Spec/go_etcd_io/etcd/pkg/v3/schedule/Scheduler__Schedule.lean`)
one at a time in its own goroutine: the **run token** `schedRunning γ` (exclusive) is the
scheduler's, every job's `Do` receives it in its precondition and returns it in its
postcondition (no overlap). `Schedule` does not ask for the token (compaction's `compactBarrier`
schedules a job from inside a running job).

**A job** `jobIs γ j Pre Post` (persistent): the `Job` interface value `j` whose `Do(ctx)`, with
the run token and `Pre`, for any context (`isContext`, possibly cancelled), returns with the
token and `Post`. `NewJob(name, do)` makes one from the closure `do`'s triple.

**The record of the scheduled jobs** (`γ.jobs`, a monotone list of the saved propositions'
names of the jobs' postconditions, in scheduling order): kept so that a FIFO strengthening
(the scheduler runs the jobs in the order `Schedule` was called) slots in, as an ordering of
the `Post`s; the current contract does not use it (agreed with the session verifying the
server, which will strengthen `Schedule` in place).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.schedule
public import Perennial.Proof.context
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoList

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
  /-- the scheduled jobs' postconditions (a monotone list of saved propositions' names), for a
  FIFO strengthening of `Schedule` -/
  jobs : GName

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The run token** (exclusive): the scheduler's goroutine has it while it runs a job. -/
def schedRunning (γ : SchedNames) : IProp GF := dghostVar γ.run (DFrac.own 1) ()

/-- **A scheduler** (persistent): a non-nil `Scheduler` interface value with its names. -/
def isScheduler (f : GoInterface) (γ : SchedNames) : IProp GF :=
  iprop(⌜f ≠ GoInterface.nil⌝ ∗ ∃ L : List GName, monoListLbOwn γ.jobs L)

instance isScheduler_persistent (f : GoInterface) (γ : SchedNames) :
    Persistent (isScheduler (GF := GF) f γ) := by
  unfold isScheduler; infer_instance

end defs

section jobs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [context_sem : _root_.Perennial.context.Assumptions]

/-- `jt`'s `Do(ctx)`, with the run token and `Pre`, for any context (possibly cancelled: the job
reads it, `ctx.Err()`), returns the token and `Post`. -/
def jobDoSpec (γ : SchedNames) (jt : GoInterfaceOk) (Pre Post : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedRunning γ ∗ Pre ∗ _root_.Perennial.context.isContext ctx cd }}
      (App (Val #(methods jt.ty go!"Do" jt.v)) (Val #(GoInterface.ok ctx)))
    {{ RET #(); schedRunning γ ∗ Post }})

instance jobDoSpec_persistent (γ : SchedNames) (jt : GoInterfaceOk) (Pre Post : IProp GF) :
    Persistent (jobDoSpec γ jt Pre Post) := by
  unfold jobDoSpec; infer_instance

/-- **A job** (persistent): the `Job` interface value `j` runs with precondition `Pre` and
postcondition `Post` under the scheduler's run token. -/
def jobIs (γ : SchedNames) (j : GoInterface) (Pre Post : IProp GF) : IProp GF :=
  iprop(∃ jt : GoInterfaceOk, ⌜j = GoInterface.ok jt⌝ ∗ jobDoSpec γ jt Pre Post)

instance jobIs_persistent (γ : SchedNames) (j : GoInterface) (Pre Post : IProp GF) :
    Persistent (jobIs γ j Pre Post) := by
  unfold jobIs; infer_instance

/-- The closure `do`'s triple: with the run token and `Pre`, for any context, it returns with
the token and `Post` (what `NewJob` makes a job of). -/
def jobFnSpec (γ : SchedNames) (f : GoFunc) (Pre Post : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedRunning γ ∗ Pre ∗ _root_.Perennial.context.isContext ctx cd }}
      (App (Val #f) (Val #(GoInterface.ok ctx)))
    {{ RET #(); schedRunning γ ∗ Post }})

instance jobFnSpec_persistent (γ : SchedNames) (f : GoFunc) (Pre Post : IProp GF) :
    Persistent (jobFnSpec γ f Pre Post) := by
  unfold jobFnSpec; infer_instance

end jobs

end schedule
end EtcdGrove
end Perennial
