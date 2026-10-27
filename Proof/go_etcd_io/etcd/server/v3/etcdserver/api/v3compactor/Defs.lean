/-
etcd's auto-compactor (`server/etcdserver/api/v3compactor`): the shared vocabulary of
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/*.lean`. Lean-first (no Rocq
counterpart); the spec-first pilot (`notes/compactor-pilot-plan.md`, "Phase 1: the design of the
skeleton").

**The environment** the compactor is built over, as persistent contracts on the interface values
`New` receives:
- `revGetterOk γi rg`: `rg.Rev()` returns the current revision of a store whose index certificates
  are `γi` (what `mvcc.store.Rev` gives; the server passes `srv.kv`), as a lower bound that only
  grows (`revLb`).
- `compactableOk c P`: `c.Compact(ctx, &CompactionRequest{Revision: r})` returns for every `r` with
  `P r`. **`P` is the guarantee C1** (the plan's "top-level statements"): the compactor's proof
  shows it calls `Compact` only with a permitted revision.
- the clock, `clockwork.clockOk clockwork.realClock` (`Proof/github_com/jonboulle/clockwork/Defs.lean`).

**C1, the permits.**
- revision mode (`revPermit γi ret r`): `0 < r` and the store has reached `r + ret`
  (`Revision.Run` compacts at `Rev() - retention`).
- periodic mode (`perPermit γi K r`, `K = periodK period`): `0 < r` and either the store had
  reached `r` by a clock time `T` with the clock now past `T + K` (the window of samples is full:
  `revs[0]` was sampled `retentions - 1` waits ago), or the store has reached `r` (the first
  compaction of a run, whose sample is the run's first: only `Now() - start ≥ period` is known, and
  the first sample may come any time after `start`; phase 1's finding, the plan's "C1 restated").

**The objects.** `isPeriodic pc E period` (persistent): the fields `New` set, read-only from then
on, with their contracts, and the `RWMutex` guard over `paused` (`Pause`/`Resume` write-lock it);
`periodicRunTok pc` (exclusive, consumed by `Run`): the `revs` field, which only `Run`'s goroutine
touches, and a reader slot of the mutex. `isRevision rc E ret` likewise, over a `sync.Mutex` (its
`Run` keeps nothing of the object). `Run` also takes the server's resource `E.R`, which its
goroutine passes to every `Compact`. `compactorOk cp RunTok R` (persistent): the interface value
`New` returns, with its four methods' contracts.
-/
module

public import Proof.github_com.jonboulle.clockwork.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor
public import Perennial.Proof.context
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Golang.Theory.Lock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.api.v3

/-! ### The periodic mode's intervals (`periodic.go`), on `time.Duration`'s nanoseconds -/

/-- `getRetryInterval`: `min(period, 1h) / 10` (Go's division truncates; `0 < period`). -/
def retryOf (period : Int) : Int := min period 3600000000000 / 10

/-- `getRetentions`: `period / retry + 1` samples in the window. -/
def retentionsOf (period : Int) : Int := period / retryOf period + 1

/-- The age of a full window's oldest sample, in clock time: `retentions - 1` waits of `retry`. -/
def periodK (period : Int) : Int := (retentionsOf period - 1) * retryOf period

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ### The environment -/

/-- The store has reached revision `r`: an index certificate of a log of `r + 1` revisions or more
(revision `0` is the empty store's). -/
def revLb (γi : mvcc.IdxNames) (r : Int) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert γi log ∗ ⌜r ≤ (log.length : Int) - 1⌝)

instance revLb_persistent (γi : mvcc.IdxNames) (r : Int) : Persistent (revLb (GF := GF) γi r) := by
  unfold revLb; infer_instance

/-- **The revision getter** (`RevGetter`, the server's `srv.kv`): `Rev()` returns `v`, which the
store has reached. -/
def revGetterOk (γi : mvcc.IdxNames) (rg : GoInterface) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rg = GoInterface.ok ri⌝ ∗
    □ ({{ True }} (App (Val #(methods ri.ty go!"Rev" ri.v)) (Val #()))
        {{ (v : w64), RET #v; revLb γi (sint.Z v) }}))

instance revGetterOk_persistent (γi : mvcc.IdxNames) (rg : GoInterface) :
    Persistent (revGetterOk (GF := GF) γi rg) := by
  unfold revGetterOk; infer_instance

/-- A compaction request the compactor builds: `&pb.CompactionRequest{Revision: r}`. -/
def compactReqIs (p : Loc) (r : Int) : IProp GF :=
  iprop(∃ v : etcdserverpb.CompactionRequest, p ↦ v ∗ ⌜sint.Z v.Revision' = r ∧ v.Physical' = false⌝)

/-- **The compactable** (`Compactable`, the server): `Compact(ctx, req)` returns, for a request
at a permitted revision (`P r`) and any context, given and giving back the caller's resource `R`
(what the server's proposal path consumes per request: `R` is the server's to define). -/
def compactableOk (c : GoInterface) (P : Int → IProp GF) (R : IProp GF) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
    □ (∀ (r : Int) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (p : Loc),
        P r -∗ R -∗ context.isContext ctx cd -∗ compactReqIs p r -∗
        WP (App (App (Val #(methods ci.ty go!"Compact" ci.v)) (Val #(GoInterface.ok ctx))) (Val #p))
          {{ fun _ => R }}))

instance compactableOk_persistent (c : GoInterface) (P : Int → IProp GF) (R : IProp GF) :
    Persistent (compactableOk (GF := GF) c P R) := by
  unfold compactableOk; infer_instance

/-! ### C1 -/

/-- **C1, revision mode**: `0 < r` and the store has reached `r + ret`. -/
def revPermit (γi : mvcc.IdxNames) (ret : Int) (r : Int) : IProp GF :=
  iprop(⌜0 < r⌝ ∗ revLb γi (r + ret))

/-- **C1, periodic mode**: `0 < r`, and the store had reached `r` by a clock time `T` the clock is
now `K` past (a full window), or (the run's first compaction) the store has reached `r`. -/
def perPermit (γi : mvcc.IdxNames) (K : Int) (r : Int) : IProp GF :=
  iprop(⌜0 < r⌝ ∗
    ((∃ T : Int, clockwork.stampAt clockwork.realClock (revLb γi r) T ∗
        clockwork.clockLb clockwork.realClock (T + K)) ∨
     revLb γi r))

/-- The permit of a mode (`New`'s `mode`; `ret` the retention's nanoseconds or revisions). -/
def modePermit (mode : GoString) (γi : mvcc.IdxNames) (ret : Int) : Int → IProp GF :=
  if mode = go!"revision" then revPermit γi ret else perPermit γi (periodK ret)

/-! ### The objects -/

/-- What `New`'s caller supplies: the store's certificates, the revision getter, the server, and
the resource the server's `Compact` takes and gives back (`compactableOk`). -/
structure CompactEnv (GF : BundledGFunctors) where
  γi : mvcc.IdxNames
  rg : GoInterface
  c : GoInterface
  R : IProp GF

/-- `paused` under the periodic compactor's `RWMutex`: a fraction of its cell. -/
def perPausedInv (pc : Loc) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, structFieldRef v3compactor.Periodic go!"paused" pc ↦{DFrac.own q} b)

/-- **A periodic compactor** (`*Periodic`, from `newPeriodic`) of `period`: its fields, read-only,
with their contracts; the mutex's writer guard. -/
def isPeriodic (pc : Loc) (E : CompactEnv GF) (period : Int) : IProp GF :=
  iprop(∃ (lg : Loc) (clk : GoInterface) (pd : time.Duration) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (γctx : context.ContextNames) (cancel : GoFunc),
    structFieldRef v3compactor.Periodic go!"lg" pc ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    structFieldRef v3compactor.Periodic go!"clock" pc ↦□ clk ∗
    clockwork.clockOk clockwork.realClock clk ∗
    structFieldRef v3compactor.Periodic go!"period" pc ↦□ pd ∗ ⌜sint.Z pd = period ∧ 10 ≤ period⌝ ∗
    structFieldRef v3compactor.Periodic go!"rg" pc ↦□ E.rg ∗ revGetterOk E.γi E.rg ∗
    structFieldRef v3compactor.Periodic go!"c" pc ↦□ E.c ∗
    compactableOk E.c (perPermit E.γi (periodK period)) E.R ∗
    structFieldRef v3compactor.Periodic go!"ctx" pc ↦□ GoInterface.ok ctx ∗
    context.isContext ctx cd ∗
    structFieldRef v3compactor.Periodic go!"cancel" pc ↦□ cancel ∗
    context.cancelSpec cancel γctx iprop(True) ∗
    sync.isRWMutexGuard (structFieldRef v3compactor.Periodic go!"mu" pc) (perPausedInv pc))

set_option synthInstance.maxSize 512 in
instance isPeriodic_persistent (pc : Loc) (E : CompactEnv GF) (period : Int) :
    Persistent (isPeriodic (GF := GF) pc E period) := by
  unfold isPeriodic; infer_instance

/-- **What `Run` takes** of a periodic compactor (besides the server's `E.R`): the sample window
`revs` (only `Run`'s goroutine touches it) and a reader slot of the mutex. -/
def periodicRunTok (pc : Loc) : IProp GF :=
  iprop((∃ s : GoSlice, structFieldRef v3compactor.Periodic go!"revs" pc ↦ s) ∗
    sync.ownRWMutex (structFieldRef v3compactor.Periodic go!"mu" pc) (perPausedInv pc))

/-- `paused` under the revision compactor's `Mutex`. -/
def revPausedInv (rc : Loc) : IProp GF :=
  iprop(∃ b : Bool, structFieldRef v3compactor.Revision go!"paused" rc ↦ b)

/-- **A revision compactor** (`*Revision`, from `newRevision`) of retention `ret`. -/
def isRevision (rc : Loc) (E : CompactEnv GF) (ret : Int) : IProp GF :=
  iprop(∃ (lg : Loc) (clk : GoInterface) (rt : w64) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (γctx : context.ContextNames) (cancel : GoFunc),
    structFieldRef v3compactor.Revision go!"lg" rc ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    structFieldRef v3compactor.Revision go!"clock" rc ↦□ clk ∗
    clockwork.clockOk clockwork.realClock clk ∗
    structFieldRef v3compactor.Revision go!"retention" rc ↦□ rt ∗ ⌜sint.Z rt = ret⌝ ∗
    structFieldRef v3compactor.Revision go!"rg" rc ↦□ E.rg ∗ revGetterOk E.γi E.rg ∗
    structFieldRef v3compactor.Revision go!"c" rc ↦□ E.c ∗
    compactableOk E.c (revPermit E.γi ret) E.R ∗
    structFieldRef v3compactor.Revision go!"ctx" rc ↦□ GoInterface.ok ctx ∗
    context.isContext ctx cd ∗
    structFieldRef v3compactor.Revision go!"cancel" rc ↦□ cancel ∗
    context.cancelSpec cancel γctx iprop(True) ∗
    isLock (structFieldRef v3compactor.Revision go!"mu" rc) (revPausedInv rc))

set_option synthInstance.maxSize 512 in
instance isRevision_persistent (rc : Loc) (E : CompactEnv GF) (ret : Int) :
    Persistent (isRevision (GF := GF) rc E ret) := by
  unfold isRevision; infer_instance

/-- **A compactor** (`Compactor`, the interface value `New` returns): `Stop`, `Pause` and `Resume`
return; `Run` returns, taking the run token `RunTok` (so it runs once) and the server's resource
`R`, which its goroutine keeps. -/
def compactorOk (cp : GoInterface) (RunTok R : IProp GF) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cp = GoInterface.ok ci⌝ ∗
    □ ({{ RunTok ∗ R }} (App (Val #(methods ci.ty go!"Run" ci.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Stop" ci.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Pause" ci.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Resume" ci.v)) (Val #())) {{ RET #(); True }}))

instance compactorOk_persistent (cp : GoInterface) (RunTok R : IProp GF) :
    Persistent (compactorOk (GF := GF) cp RunTok R) := by
  unfold compactorOk; infer_instance

end defs

end v3compactor
end EtcdGrove
end Perennial
