/-
# `pkg/v3/schedule`: the FIFO scheduler (batch 2d): the vocabulary

`schedule.NewFIFOScheduler(lg)` starts one worker goroutine that runs the jobs handed to
`Schedule` in order, one at a time; `Stop` cancels the scheduler's context and returns once the
worker has run every job still pending (with the cancelled context) and exited.

## Users (the pinned etcd)

* the server's apply loop (`server.go:761, 841`): one `applyAll` job per batch of committed
  entries, each job handing the apply thread's state to the next (`run`'s FIFO chain); `run`'s
  deferred shutdown stops the scheduler and needs the last job's state back;
* mvcc's store (`kvstore.go:107, 147, 201, 236, 310`): compaction jobs and compaction barriers
  (`compactBarrier(ctx, ch)` returns early, without closing `ch`, when the context is cancelled:
  the job's postcondition must then come from what `Stop`'s caller established).

Snippets: `examples/specreq/schedule/` (`ReqFifoChain`, `ReqStopRunsPending`,
`ReqCancelledCtx`).

## Vocabulary

* `SchedNames` (opaque): a scheduler's ghost names.
* `isSched sc γ Pay` (persistent, transparent): **`sc` is a `Scheduler` interface value** with
  names `γ` (the bundle of its `Schedule` and `Stop` contracts, PRINCIPLES "an interface value gets
  a bundle"; `NewFIFOScheduler` gives it for a `*fifo`). `Pay` (persistent) is what a job learns when
  the scheduler's context is done: `Stop`'s caller must hold it.
* `schedOpen γ q` (fractional): the right to schedule (any fraction); `Stop` takes it whole, so no
  `Schedule` follows a `Stop` (`fifo.Schedule` panics on a stopped scheduler).
* `schedTail γ P` (exclusive): **the chain's end**: `P` is what the last job scheduled leaves when
  it finishes (`True` for a new scheduler). `Schedule` of a job that turns `P ∗ A` into `Q` moves it
  to `Q`; `Stop` gives back `P` (every pending job has run). A user that does not chain (mvcc's
  compactions) keeps it at `True` in its own lock invariant.
* `jobOk j Pay P Q` (persistent, transparent): `j` is a `Job` interface value whose `Do(ctx)`, for
  the scheduler's context (a context whose being done gives `Pay`), turns `P` into `Q`.
  `funcOk f Pay P Q` the same of a Go closure `func(context.Context)` (`NewJob`'s argument).

Laws: `persistent`, `schedTail_excl`, `schedOpen_fractional`.

## Intended realization

`isFifo l γ Pay` (internal): `fifo`'s lock invariant over `pendings` (each pending job with its
`jobOk` and its saved pre/post, chained: the first's pre is the worker's, each next's pre the
previous one's post), `cancel` non-nil iff `schedOpen γ 1` is not in the invariant, the context
`ctx` with `□ (ctxDone ctx -∗ □ Pay)` (Perennial's `WithCancel` over `Background()`; `cancel` is called
only by `Stop`, which holds `□ Pay`), `donec`'s close carrying the last post; `schedTail γ P` a ghost
variable of the saved name of the last post. `fifoWorker l γ` (internal) is the worker goroutine's
token: the head job's resources while it runs.

**Verify round** (A7-completeness S4, A7-provability F2): a job runs in the worker goroutine, which
`NewFIFOScheduler` forks with a fresh thread token (Perennial's `wp_fork_tok_body`; no token from
the caller); the worker lends it to each job (`funcOk`, `jobOk` take and give back `threadTok`), so
the apply jobs (`applyAll`) and mvcc's compaction jobs may call specs that take one.
-/
module

public import Spec.PkgInit.go_etcd_io.etcd.pkg.v3.schedule
public import Spec.context.Api
public import Spec.go_uber_org.zap.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schedule

open Iris Iris.BI

/-- A scheduler's ghost names. -/
opaque SchedNames : Type := Unit

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- The right to schedule (fractional; `Stop` takes it whole). -/
opaque schedOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : SchedNames) (q : Qp) : IProp GF := iprop(True)

/-- **The chain's end**: the last job scheduled leaves `P` when it finishes (exclusive). -/
opaque schedTail [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : SchedNames) (P : IProp GF) : IProp GF := iprop(True)

/-- (internal) `l` is a `*fifo` with names `γ`, its context's being done giving `Pay`. -/
opaque isFifo [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (γ : SchedNames) (Pay : IProp GF) : IProp GF := iprop(True)

/-- (internal) The worker goroutine's token (`run`'s; lent to `executeJob`). -/
opaque fifoWorker [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (γ : SchedNames) : IProp GF := iprop(True)

/-- (internal) The resources of the job at the head of the queue, handed to the worker: its
contract, its precondition and where its postcondition goes. -/
opaque fifoHead [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (γ : SchedNames) (j : GoInterface) : IProp GF := iprop(True)

/-- **A job's context**: `ctx` is a context, done only once `Pay` holds. -/
def schedCtx (ctx : GoInterface) (Pay : IProp GF) : IProp GF :=
  iprop(Context.ctxOk ctx ∗ □ (Context.ctxDone ctx -∗ □ Pay))

/-- **A `func(context.Context)` closure turning `P` into `Q`** under the scheduler's context. -/
def funcOk (f : GoFunc) (Pay P Q : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (Φ : val → IProp GF),
    schedCtx ctx Pay -∗ P -∗ threadTok -∗ ▷ (Q -∗ threadTok -∗ Φ #()) -∗ WP (App (Val #f) (Val #ctx)) {{ Φ }})

/-- **A `Job` turning `P` into `Q`** (its `Do`). -/
def jobOk (j : GoInterface) (Pay P Q : IProp GF) : IProp GF :=
  iprop(∃ ji : GoInterfaceOk, ⌜j = interface.ok ji⌝ ∗
    □ ∀ (ctx : GoInterface) (Φ : val → IProp GF),
      schedCtx ctx Pay -∗ P -∗ threadTok -∗ ▷ (Q -∗ threadTok -∗ Φ #()) -∗
        WP (App (Val #(methods ji.ty go!"Do" ji.v)) (Val #ctx)) {{ Φ }})

/-- **A `Scheduler` interface value** (the bundle of `Schedule` and `Stop`). -/
def isSched (sc : GoInterface) (γ : SchedNames) (Pay : IProp GF) : IProp GF :=
  iprop(∃ fi : GoInterfaceOk, ⌜sc = interface.ok fi⌝ ∗
    (□ ∀ (j : GoInterface) (q : Qp) (P A Q : IProp GF) (Φ : val → IProp GF),
      schedOpen γ q ∗ schedTail γ P ∗ jobOk j Pay iprop(P ∗ A) Q ∗ A -∗
      ▷ (schedOpen γ q ∗ schedTail γ Q -∗ Φ #()) -∗
      WP (App (Val #(methods fi.ty go!"Schedule" fi.v)) (Val #j)) {{ Φ }}) ∗
    (□ ∀ (P : IProp GF) (Φ : val → IProp GF),
      schedOpen γ 1 ∗ schedTail γ P ∗ □ Pay -∗ ▷ (P -∗ Φ #()) -∗
      WP (App (Val #(methods fi.ty go!"Stop" fi.v)) (Val #())) {{ Φ }}))

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

def persistent.spec : Prop :=
  (∀ l γ Pay, Persistent (isFifo (GF := GF) l γ Pay))

def schedTail_excl.spec : Prop :=
  ∀ γ (P P' : IProp GF), schedTail (GF := GF) γ P ∗ schedTail γ P' ⊢ iprop(False)

def schedOpen_fractional.spec : Prop := ∀ γ, Fractional (schedOpen (GF := GF) γ)

/-- A `*fifo` is a `Scheduler` (the bundle, from the concrete specs). -/
def isFifo_isSched.spec : Prop :=
  ∀ (l : Loc) γ (Pay : IProp GF),
    isFifo (GF := GF) l γ Pay ⊢
      isSched (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.schedule.fifo.ty) #l)
        γ Pay

end laws

end Schedule
end EtcdGrove
end Perennial
