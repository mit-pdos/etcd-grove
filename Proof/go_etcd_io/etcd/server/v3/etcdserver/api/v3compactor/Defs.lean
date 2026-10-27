/-
etcd's auto-compactor (`server/etcdserver/api/v3compactor`): the shared vocabulary of
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/*.lean`. Lean-first (no Rocq
counterpart); the spec-first pilot (`notes/compactor-pilot-plan.md`, "Phase 1: the design of the
skeleton").

**The environment** the compactor is built over, as persistent contracts on the interface values
`New` receives:
- `revGetterOk RevLb rg R`: `rg.Rev()`, with the caller's resource `R` (the store's `Rev` needs a
  reader slot), returns a non-negative revision the store has reached (`RevLb`, the caller's
  lower-bound predicate: the server's is `revLb`, over mvcc's index certificates; the server passes
  `srv.kv`).
- `compactableOk c P R`: `c.Compact(ctx, &CompactionRequest{Revision: r})`, with `R`, returns for
  every `r` with `P r`, with an error `errors.Is` can test (`errTreeOk`). **`P` is the guarantee
  C1** (the plan's "top-level statements"): the compactor's proof shows it calls `Compact` only
  with a permitted revision.
- the clock, `clockwork.clockOk clockwork.realClock` (`Proof/github_com/jonboulle/clockwork/Defs.lean`).

**C1, the permits.**
- revision mode (`revPermit RevLb ret r`): `0 < r` and the store has reached `r + ret`
  (`Revision.Run` compacts at `Rev() - retention`).
- periodic mode (`perPermit RevLb period γf r`): `0 < r` and the store had reached `r` by a clock
  time `T` the clock is now `period` past (a full window: `revs[0]`'s sample is `retentions` waits
  of `retry` old); or `r` is the run's first sample (`firstSample γf r`, one revision per run, retried
  at the same revision if its compaction fails) and the clock is `retry` past `T` (that sample is
  taken at an unknown time after `start`; the plan's "C1 restated").

**The objects.** `isPeriodic pc E period` (persistent): the fields `New` set, read-only from then
on, the clock's contract, and the `RWMutex` guard over `paused` (`Pause`/`Resume` write-lock it);
`periodicRunTok pc` (exclusive, consumed by `Run`): the `revs` field, which only `Run`'s goroutine
touches, and a reader slot of the mutex. `isRevision rc E ret` likewise, over a `sync.Mutex` (its
`Run` keeps nothing of the object). `Run` also takes `runPre E P`: the revision getter's and the
server's contracts (only `Run` needs them: `New` calls neither), the resource they thread, and the
first sample's ghost variable. `compactorOk cp RunTok RunPre` (persistent): the interface value `New`
returns, with its four methods' contracts.
-/
module

public import Proof.github_com.jonboulle.clockwork.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor
public import Perennial.Proof.context
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Golang.Theory.Lock
public import Perennial.Ghost.DGhostVar

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

/-- **The revision getter** (`RevGetter`, the server's `srv.kv`): `Rev()`, given and giving back the
caller's resource `R` (the store's `Rev` needs a reader slot), returns a non-negative `v` the store
has reached (`RevLb v`: the caller's lower-bound predicate; the server's is `revLb`), and no smaller
than any revision `n` the caller knows the store had reached (the revision never decreases: the
periodic mode's `0 < r` rests on it, `periodic.go` having no `rev <= 0` check). -/
def revGetterOk (RevLb : Int → IProp GF) (rg : GoInterface) (R : IProp GF) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rg = GoInterface.ok ri⌝ ∗
    □ (∀ n : Int, {{ R ∗ □ RevLb n }} (App (Val #(methods ri.ty go!"Rev" ri.v)) (Val #()))
        {{ (v : w64), RET #v; R ∗ □ RevLb (sint.Z v) ∗ ⌜n ≤ sint.Z v ∧ 0 ≤ sint.Z v⌝ }}))

instance revGetterOk_persistent (RevLb : Int → IProp GF) (rg : GoInterface) (R : IProp GF) :
    Persistent (revGetterOk (GF := GF) RevLb rg R) := by
  unfold revGetterOk; infer_instance

/-- A compaction request the compactor builds: `&pb.CompactionRequest{Revision: r}`. -/
def compactReqIs (p : Loc) (r : Int) : IProp GF :=
  iprop(∃ v : etcdserverpb.CompactionRequest, p ↦ v ∗ ⌜sint.Z v.Revision' = r ∧ v.Physical' = false⌝)

/-- **An error `errors.Is` can test** against any target (the part of the server's `apply.applyErrIs`
the compactor needs: `errors.Is(err, mvcc.ErrCompacted)`). -/
def errTreeOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ target : GoInterface, ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
    _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
    ⌜S err ∧ ((∀ tii, target = GoInterface.ok tii → _root_.Perennial.errors.IsPointerError tii) →
      _root_.Perennial.errors.TreeTyped S target)⌝)

instance errTreeOk_persistent (err : GoInterface) : Persistent (errTreeOk (GF := GF) err) := by
  unfold errTreeOk; infer_instance

/-- **The compactable** (`Compactable`, the server): `Compact(ctx, req)`, for a request at a
permitted revision (`P r`) and any context, given and giving back the caller's resource `R` (what
the server's proposal path consumes per request: `R` is the server's to define), returns a response
and an error `errors.Is` can test. -/
def compactableOk (c : GoInterface) (P : Int → IProp GF) (R : IProp GF) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
    □ (∀ (r : Int) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (p : Loc),
        {{ P r ∗ R ∗ context.isContext ctx cd ∗ compactReqIs p r }}
          (App (App (Val #(methods ci.ty go!"Compact" ci.v)) (Val #(GoInterface.ok ctx))) (Val #p))
        {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗ errTreeOk err }}))

instance compactableOk_persistent (c : GoInterface) (P : Int → IProp GF) (R : IProp GF) :
    Persistent (compactableOk (GF := GF) c P R) := by
  unfold compactableOk; infer_instance

/-! ### C1 -/

/-- **C1, revision mode**: `0 < r` and the store has reached `r + ret`. -/
def revPermit (RevLb : Int → IProp GF) (ret : Int) (r : Int) : IProp GF :=
  iprop(⌜0 < r⌝ ∗ □ RevLb (r + ret))

/-- **The run's first sample** was `r` (persistent, and the same for every use: a ghost variable the
server allocates unset, `firstUnset`, and `Run`'s goroutine sets once to its first `Rev()`). -/
def firstSample (γf : GName) (r : Int) : IProp GF := dghostVar γf DFrac.discard (some r)

/-- The run's first sample, not taken yet (what the server gives `Run`). -/
def firstUnset (γf : GName) : IProp GF := dghostVar γf (DFrac.own 1) (none : Option Int)

/-- **C1, periodic mode**: `0 < r`, and the store had reached `r` by a clock time `T` that the clock
is now `period` past; or `r` is the run's first sample (`firstSample γf r`) and the clock is `retry`
past `T` (that sample is taken at an unknown time after the run's start: the plan's "C1 restated",
the user's choices 2026-10-27). So at most one revision per run, its first sample, is compacted
younger than the period (a failed compaction of it is retried at the same revision). -/
def perPermit (RevLb : Int → IProp GF) (period : Int) (γf : GName) (r : Int) : IProp GF :=
  iprop(⌜0 < r⌝ ∗ ∃ T : Int, clockwork.stampAt clockwork.realClock iprop(□ RevLb r) T ∗
    (clockwork.clockLb clockwork.realClock (T + period) ∨
     (firstSample γf r ∗ clockwork.clockLb clockwork.realClock (T + retryOf period))))

instance perPermit_persistent (RevLb : Int → IProp GF) (period : Int) (γf : GName) (r : Int) :
    Persistent (perPermit (GF := GF) RevLb period γf r) := by
  unfold perPermit firstSample; infer_instance

/-- The permit of a mode (`New`'s `mode`; `ret` the retention's nanoseconds or revisions). -/
def modePermit (mode : GoString) (RevLb : Int → IProp GF) (ret : Int) (γf : GName) :
    Int → IProp GF :=
  if mode = go!"revision" then revPermit RevLb ret else perPermit RevLb ret γf

/-! ### The objects -/

/-- What `New`'s caller supplies: the store's revision lower bounds (`RevLb r`: the store has
reached `r`; the server's is `revLb`), the revision getter, the server, and the resource the
getter's `Rev` and the server's `Compact` take and give back, and the ghost name of the periodic
mode's first sample (`firstSample`, `perPermit`). -/
structure CompactEnv (GF : BundledGFunctors) where
  RevLb : Int → IProp GF
  rg : GoInterface
  c : GoInterface
  R : IProp GF
  γf : GName

/-- **What `Run` takes from its caller** (besides the object's run token), for a compactor whose
`Compact` calls take the permit `P`: the revision getter's and the server's contracts (needed only
from `Run` on: `New` calls neither), the resource they thread, a revision the store has reached (`0`,
the getter's first lower bound), and the periodic mode's unset first sample. -/
def runPre (E : CompactEnv GF) (P : Int → IProp GF) : IProp GF :=
  iprop(revGetterOk E.RevLb E.rg E.R ∗ compactableOk E.c P E.R ∗ E.R ∗ □ E.RevLb 0 ∗
    firstUnset E.γf)

/-- `paused` under the periodic compactor's `RWMutex`: a fraction of its cell. -/
def perPausedInv (pc : Loc) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, structFieldRef v3compactor.Periodic go!"paused" pc ↦{DFrac.own q} b)

/-- **A periodic compactor** (`*Periodic`, from `newPeriodic`) of `period`: its fields, read-only,
the clock's contract, the mutex's writer guard. -/
def isPeriodic (pc : Loc) (E : CompactEnv GF) (period : Int) : IProp GF :=
  iprop(∃ (lg : Loc) (clk : GoInterface) (pd : time.Duration) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (γctx : context.ContextNames) (cancel : GoFunc),
    structFieldRef v3compactor.Periodic go!"lg" pc ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    structFieldRef v3compactor.Periodic go!"clock" pc ↦□ clk ∗
    clockwork.clockOk clockwork.realClock clk ∗
    structFieldRef v3compactor.Periodic go!"period" pc ↦□ pd ∗ ⌜sint.Z pd = period ∧ 10 ≤ period⌝ ∗
    structFieldRef v3compactor.Periodic go!"rg" pc ↦□ E.rg ∗
    structFieldRef v3compactor.Periodic go!"c" pc ↦□ E.c ∗
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
    structFieldRef v3compactor.Revision go!"rg" rc ↦□ E.rg ∗
    structFieldRef v3compactor.Revision go!"c" rc ↦□ E.c ∗
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
return; `Run` returns, taking the run token `RunTok` (so it runs once) and `RunPre` (`runPre`: the
environment's contracts and resources, which its goroutine keeps). -/
def compactorOk (cp : GoInterface) (RunTok RunPre : IProp GF) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cp = GoInterface.ok ci⌝ ∗
    □ ({{ RunTok ∗ RunPre }} (App (Val #(methods ci.ty go!"Run" ci.v)) (Val #()))
      {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Stop" ci.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Pause" ci.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Resume" ci.v)) (Val #())) {{ RET #(); True }}))

instance compactorOk_persistent (cp : GoInterface) (RunTok RunPre : IProp GF) :
    Persistent (compactorOk (GF := GF) cp RunTok RunPre) := by
  unfold compactorOk; infer_instance

end defs

end v3compactor
end EtcdGrove
end Perennial
