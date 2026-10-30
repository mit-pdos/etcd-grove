/-
**M2, the storage side, step 2: the scheduler's contract for restore in compaction mode (Draft)**
(`notes/m2-storage-plan.md`, "After review round 3", F2; the user's Q6: `Stop` returns the run
token and takes the "stop channel closed" fact, `updateCompactRev`'s barrier a tracked job).
Imported by mvcc's Draft (`mvcc/M2StorageDraftRestore.lean`); no `axiom`, no `sorry`; nothing
switched.

**Why today's contract cannot carry the stop fact to a job** (review round 3, F2): a job's `Do` is
specified for *any* context (`jobDoSpec`: `□ ∀ ctx cd, {{ … ∗ isContext ctx cd }}`), so a job that
finds its context cancelled (`ctx.Err() ≠ nil`, which gives `□ cd.PDone`) learns nothing about the
scheduler. mvcc's `compactBarrier` must then handle the branch where the context is cancelled and
`s.stopc` open (`kvstore.go:138-150`), which takes `s.mu` and schedules untracked: today it needs
`schedLive` (never stopped), which a restorable store cannot have.

**The change, the least that carries the fact** (each text replaces today's of the same name
without `D` at the switch):
- **The payload** (`schedPayIs γ P`, persistent): the scheduler's names gain one, `pay`, the name of
  a saved proposition the creator fixes (`NewFIFOScheduler.specD`'s new argument `Pay`). The
  scheduler's own context (`fifoCtxDesc`, internal) is done with `stopped F ∗ schedPay γ`
  instead of `stopped F`, so `Stop`, which cancels it, takes `schedPay γ` (`Scheduler.Stop.specD`):
  the payload saved at `γ.pay`, holding (`□ P`).
- **A job learns it** (`jobDoSpecD`/`jobFnSpecD`): `Do`'s precondition gains
  `□ (cd.PDone -∗ schedPay γ)` for the context it is given (the worker gives the scheduler's
  context, whose `PDone` has it; `executeJob`, internal). A job that sees `ctx.Err() ≠ nil` has
  `□ cd.PDone`, hence `schedPay γ`, hence `▷ □ P` (`schedPay_elim`, with its own `schedPayIs γ P`).
- **`Stop` returns the run token** (`schedDoneD γ`, the worker's `dghostVar γ.run 1 ()` given up
  after its last job: `fifo.run`'s deferred `close(f.donec)`, internal).
- `NewJob.specD`, `Scheduler.Schedule.specD`: today's texts over `jobFnSpecD`/`jobIsD`.

**Every user**:
- mvcc's store (`NewStore`, `store.Restore`) creates its scheduler with `Pay` = "the store's stop
  channel is closed" (`ownBroadcastChan stopc γc True .Done`, persistent). The channel is made after
  the scheduler (`kvstore.go:309-310`), so `Pay` names it through an agreement name the store
  allocates first (internal to mvcc: `mvcc.stopPayD`, drafted in `mvcc/M2StorageDraftRestore.lean`).
  `store.Restore`/`store.Close` close `stopc` before `Stop`, so they have it (`Stop.specD`'s new
  premise). `compactBarrier`'s cancelled branch then finds `stopc` closed: Perennial's
  nonblocking receive on a `Done` broadcast needs no proof of the not-ready branch
  (`ownBroadcastChan_nonblocking_receive`), so the re-schedule branch is dead and needs no
  `schedLive` (the barrier jobs of `compact`'s cancelled path and of `updateCompactRev`'s
  `ErrCompacted` path).
- The server's `run` (`EtcdServer__run.lean`, both proofs) creates its scheduler with `Pay = True`
  (`hFifo fv.lg iprop(True)`), and its jobs ignore the payload: their `jobFnSpec` proofs carry over
  unchanged through `jobFnSpecD_of` (or one more `-` in their `iintro`).
- `etcdserver.scheduler_fifo` (exported, `Results.lean:2252`): its statement
  `schedule.Scheduler.Schedule.spec` reads over the redefined `jobIs` (text unchanged).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

/-- **The scheduler's names with the payload's** (draft: at the switch the field `pay` is
`SchedNames`' own). **Required, not optional** (review round 4's S2.1): `isFifo` must pin `pay`.
Over this extension it does not (`isFifo sc γ.toSchedNames` says nothing of `γ.pay`), so a caller of
`Scheduler.Stop.specD` could pass names with a fresh `pay` holding `True`, and `Stop`'s proof could
not produce the context's real `PDone`: as drafted here `Stop.specD` is unprovable. With `pay` a
field of `SchedNames`, `isFifo sc γ`'s internal context description (`fifoCtxDesc`, whose `PDone` is
`stopped F ∗ schedPay γ`, `fifoOf`'s) is over the same `γ`, which fixes it. -/
structure schedule.SchedNamesD extends schedule.SchedNames where
  /-- the payload's saved proposition (`schedPayIs`), fixed by the creator -/
  pay : GName

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The payload -/

/-- **The scheduler's payload is `P`** (persistent; draft): what a job that finds the scheduler's
context cancelled learns (`schedPay_elim`), fixed when the scheduler is made
(`NewFIFOScheduler.specD`). -/
def schedule.schedPayIs (γ : schedule.SchedNamesD) (P : IProp GF) : IProp GF :=
  schedule.savedProp γ.pay P

instance schedule.schedPayIs_persistent (γ : schedule.SchedNamesD) (P : IProp GF) :
    Persistent (schedule.schedPayIs (GF := GF) γ P) := by
  unfold schedule.schedPayIs; infer_instance

/-- **The payload holds** (persistent; draft): what `Stop` takes (it cancels the scheduler's
context, whose `PDone` it is part of), and what a job finding the context cancelled learns. -/
def schedule.schedPay (γ : schedule.SchedNamesD) : IProp GF :=
  iprop(∃ P : IProp GF, schedule.savedProp γ.pay P ∗ □ P)

instance schedule.schedPay_persistent (γ : schedule.SchedNamesD) :
    Persistent (schedule.schedPay (GF := GF) γ) := by
  unfold schedule.schedPay; infer_instance

/-- The payload, given. -/
theorem schedule.schedPay_of (γ : schedule.SchedNamesD) (P : IProp GF) :
    schedule.schedPayIs (GF := GF) γ P ∗ □ P ⊢ schedule.schedPay γ := by
  iintro ⟨#Hp, #HP⟩
  iunfold schedule.schedPay
  iexists P
  iunfold schedule.schedPayIs at Hp
  iframe Hp HP

/-- A scheduler whose payload is `True` (the server's `run`): `Stop`'s premise is free. -/
theorem schedule.schedPay_true (γ : schedule.SchedNamesD) :
    schedule.schedPayIs (GF := GF) γ iprop(True) ⊢ schedule.schedPay γ := by
  iintro #Hp
  iapply schedule.schedPay_of γ iprop(True)
  iframe Hp
  imodintro
  itrivial

/-- **A job's use of the payload**: the payload holds, a step later. -/
theorem schedule.schedPay_elim (γ : schedule.SchedNamesD) (P : IProp GF) :
    schedule.schedPayIs (GF := GF) γ P ∗ schedule.schedPay γ ⊢ ▷ □ P := by
  iintro ⟨#Hp, #Hq⟩
  iunfold schedule.schedPay at Hq
  icases Hq with ⟨%Q, #HQs, #HQ⟩
  iunfold schedule.schedPayIs at Hp
  iunfold schedule.savedProp at Hp HQs
  ihave #Heq := saved_prop_agree γ.pay DFrac.discard DFrac.discard Q P $$ HQs Hp
  inext
  ihave #Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨#H1, -⟩
  imodintro
  iapply H1
  iexact HQ

/-- **The worker has exited** (exclusive; draft, moved from mvcc's step-2 Draft): the scheduler's
run token's ghost part (`schedRunning`'s `dghostVar γ.run 1 ()`, without the worker's thread
token). `Scheduler.Stop.specD`'s post gives it (`<-f.donec` returns after `run`'s deferred
`close(f.donec)`, once no job runs or will run: `schedule.go:150-184`; the worker gives it up
there). -/
def schedule.schedDoneD (γ : schedule.SchedNames) : IProp GF := dghostVar γ.run (DFrac.own 1) ()

/-- Two run tokens are one too many. -/
theorem schedule.schedDoneD_excl (γ : schedule.SchedNames) :
    schedule.schedDoneD (GF := GF) γ ∗ schedule.schedDoneD γ ⊢ False := by
  iintro ⟨H1, H2⟩
  iunfold schedule.schedDoneD at H1 H2
  icombine H1 H2 gives %Hv
  obtain ⟨Hv, -⟩ := Hv
  exact absurd (DFrac.valid_own.1 Hv) (Qp_one_add_not_le 1)

end draft

section jobs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [context_sem : _root_.Perennial.context.Assumptions]

/-! ## The jobs -/

/-- **Draft of `jobDoSpec`**: today's, with `□ (cd.PDone -∗ schedPay γ)` for the context (the
worker's: the scheduler's context, done with the payload; a cancelled context's `Err` gives
`□ cd.PDone`). -/
def schedule.jobDoSpecD (γ : schedule.SchedNamesD) (jt : GoInterfaceOk) (Pre Prev Post : IProp GF) :
    IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedule.schedRunning γ.toSchedNames ∗ Pre ∗ Prev ∗
        _root_.Perennial.context.isContext ctx cd ∗ □ (cd.PDone -∗ schedule.schedPay γ) }}
      (App (Val #(methods jt.ty go!"Do" jt.v)) (Val #(GoInterface.ok ctx)))
    {{ RET #(); schedule.schedRunning γ.toSchedNames ∗ Post }})

instance schedule.jobDoSpecD_persistent (γ : schedule.SchedNamesD) (jt : GoInterfaceOk)
    (Pre Prev Post : IProp GF) : Persistent (schedule.jobDoSpecD γ jt Pre Prev Post) := by
  unfold schedule.jobDoSpecD; infer_instance

/-- **Draft of `jobIs`** over `jobDoSpecD`. -/
def schedule.jobIsD (γ : schedule.SchedNamesD) (j : GoInterface) (Pre Prev Post : IProp GF) :
    IProp GF :=
  iprop(∃ jt : GoInterfaceOk, ⌜j = GoInterface.ok jt⌝ ∗ schedule.jobDoSpecD γ jt Pre Prev Post)

instance schedule.jobIsD_persistent (γ : schedule.SchedNamesD) (j : GoInterface)
    (Pre Prev Post : IProp GF) : Persistent (schedule.jobIsD γ j Pre Prev Post) := by
  unfold schedule.jobIsD; infer_instance

/-- **Draft of `jobFnSpec`**: the same premise for the closure. -/
def schedule.jobFnSpecD (γ : schedule.SchedNamesD) (f : GoFunc) (Pre Prev Post : IProp GF) :
    IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
    {{ schedule.schedRunning γ.toSchedNames ∗ Pre ∗ Prev ∗
        _root_.Perennial.context.isContext ctx cd ∗ □ (cd.PDone -∗ schedule.schedPay γ) }}
      (App (Val #f) (Val #(GoInterface.ok ctx)))
    {{ RET #(); schedule.schedRunning γ.toSchedNames ∗ Post }})

instance schedule.jobFnSpecD_persistent (γ : schedule.SchedNamesD) (f : GoFunc)
    (Pre Prev Post : IProp GF) : Persistent (schedule.jobFnSpecD γ f Pre Prev Post) := by
  unfold schedule.jobFnSpecD; infer_instance

/-- **A job that ignores the payload is a job** (the server's `run`'s jobs, and any proved against
today's contract): today's closure triple gives the drafted one. -/
theorem schedule.jobFnSpecD_of (γ : schedule.SchedNamesD) (f : GoFunc) (Pre Prev Post : IProp GF) :
    schedule.jobFnSpec (GF := GF) γ.toSchedNames f Pre Prev Post ⊢
      schedule.jobFnSpecD γ f Pre Prev Post := by
  unfold schedule.jobFnSpec schedule.jobFnSpecD
  iintro #H !> %ctx %cd !> %Φ ⟨Hr, Hp, Hpv, #Hc, -⟩ HΦ
  iapply H $$ %ctx %cd %Φ [$Hr $Hp $Hpv $Hc] HΦ

/-- The same for a `Job` value. -/
theorem schedule.jobIsD_of (γ : schedule.SchedNamesD) (j : GoInterface) (Pre Prev Post : IProp GF) :
    schedule.jobIs (GF := GF) γ.toSchedNames j Pre Prev Post ⊢ schedule.jobIsD γ j Pre Prev Post := by
  unfold schedule.jobIs schedule.jobIsD schedule.jobDoSpec schedule.jobDoSpecD
  iintro ⟨%jt, %Hj, #H⟩
  iexists jt
  isplitr
  · ipureintro; exact Hj
  iintro !> %ctx %cd !> %Φ ⟨Hr, Hp, Hpv, #Hc, -⟩ HΦ
  iapply H $$ %ctx %cd %Φ [$Hr $Hp $Hpv $Hc] HΦ

end jobs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-! ## The specs -/

/-- **Draft of `schedule.NewFIFOScheduler.spec`**: today's, with the payload `Pay` the caller fixes
(`schedPayIs γ Pay` in the post; the scheduler's context is done with it). -/
abbrev schedule.NewFIFOScheduler.specD : Prop :=
  ∀ (lg : Loc) (Pay : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ ⌜lg ≠ null⌝ }}
    (App (Val (@! schedule.NewFIFOScheduler)) (Val #lg))
  {{ (sc : GoInterface), RET #sc; ∃ (γ : schedule.SchedNamesD) (n p₀ : GName),
      schedule.isFifo sc γ.toSchedNames ∗ schedule.schedStopTok γ.toSchedNames ∗
      schedule.schedQueue γ.toSchedNames [n, p₀] ∗ schedule.savedProp p₀ iprop(True) ∗
      schedule.schedPayIs γ Pay }}

/-- **Draft of `schedule.Scheduler.Stop.spec`**: today's, taking the payload (`schedPay γ`: `Stop`
cancels the context, done with it) and returning the run token (`schedDoneD`: the worker has
exited). Provable only once `isFifo` pins `γ.pay` (`SchedNamesD`'s docstring: `pay` a field of
`SchedNames`, a switch requirement). -/
abbrev schedule.Scheduler.Stop.specD : Prop :=
  ∀ (fi : GoInterfaceOk) (γ : schedule.SchedNamesD) (Ps : List GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.isFifo (GoInterface.ok fi) γ.toSchedNames ∗ schedule.schedStopTok γ.toSchedNames ∗
      schedule.schedQueue γ.toSchedNames Ps ∗ schedule.schedPay γ }}
    (App (Val #(methods fi.ty go!"Stop" fi.v)) (Val #()))
  {{ RET #(); (match Ps.getLast? with
      | none => iprop(True)
      | some p => iprop(∃ P : IProp GF, schedule.savedProp p P ∗ ▷ P)) ∗
      schedule.schedDoneD γ.toSchedNames }}

/-- **Draft of `schedule.Scheduler.Schedule.spec`**: today's text over `jobIsD`. -/
abbrev schedule.Scheduler.Schedule.specD : Prop :=
  ∀ (fi : GoInterfaceOk) (γ : schedule.SchedNamesD) (j : GoInterface) (Pre Prev Post : IProp GF)
    (tr : Option (List GName × GName × GName)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.isFifo (GoInterface.ok fi) γ.toSchedNames ∗ schedule.jobIsD γ j Pre Prev Post ∗ Pre ∗
      schedule.schedPre γ.toSchedNames tr Prev Post }}
    (App (Val #(methods fi.ty go!"Schedule" fi.v)) (Val #j))
  {{ RET #(); schedule.schedPost γ.toSchedNames tr }}

/-- **Draft of `schedule.NewJob.spec`**: today's text over `jobFnSpecD`/`jobIsD`. -/
abbrev schedule.NewJob.specD : Prop :=
  ∀ (γ : schedule.SchedNamesD) (name : GoString) (f : GoFunc) (Pre Prev Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.jobFnSpecD γ f Pre Prev Post }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.schedule.NewJob)) (Val #name)) (Val #f))
  {{ (j : GoInterface), RET #j; schedule.jobIsD γ j Pre Prev Post }}

end spec

end EtcdGrove
end Perennial
