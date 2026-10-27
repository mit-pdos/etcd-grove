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
`periodicRunTok pc γf` (exclusive, consumed by `Run`): the `revs` field, which only `Run`'s goroutine
touches, a reader slot of the mutex, and the run's first sample, unset (`firstUnset γf`: `newPeriodic`
allocates it; `New` returns its name). `isRevision rc E ret` likewise, over a `sync.Mutex` (its `Run`
keeps nothing of the object). `Run` also takes `runPre E P`: the revision getter's and the server's
contracts (only `Run` needs them: `New` calls neither) and the resource they thread.
`compactorOk cp RunTok RunPre` (persistent): the interface value `New` returns, with its four
methods' contracts.
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

/-- `period / retry + 1` does not overflow: the quotient is at most `19` when `retry = 1` (a period
under `20ns`), and at most half the period otherwise. -/
theorem retentions_bound (p : Int) (hp : 10 ≤ p) (hp2 : p < 2 ^ 63) :
    0 ≤ p / retryOf p ∧ p / retryOf p + 1 < 2 ^ 63 := by
  unfold retryOf
  have hd : 1 ≤ min p 3600000000000 / 10 := by omega
  generalize hdd : min p 3600000000000 / 10 = d at hd ⊢
  have hq0 : 0 ≤ p / d := Int.ediv_nonneg (by omega) (by omega)
  refine ⟨hq0, ?_⟩
  by_cases h1 : d = 1
  · subst h1; omega
  · have hmul : p / d * d ≤ p := Int.ediv_mul_le p (by omega)
    have h2 : p / d * 2 ≤ p / d * d := Int.mul_le_mul_of_nonneg_left (by omega) hq0
    omega

/-- A full window's oldest sample has waited at least `period`: `retentions` waits of `retry`. -/
theorem window_full_age (p : Int) (hp : 10 ≤ p) : p ≤ retentionsOf p * retryOf p := by
  unfold retentionsOf
  have hr : 0 < retryOf p := by unfold retryOf; omega
  have := Int.lt_ediv_add_one_mul_self p hr
  omega

/-- **The window's pure invariant** (`Periodic.Run`'s loop): sorted, non-negative, bounded by the
last sample `m`, no longer than `retentions`, and `lastRevision` (`lr`) at most its head (`0` while
it is empty: before the first round). -/
def windowOk (xs : List w64) (m rn lr : Int) : Prop :=
  List.Pairwise (fun a b => sint.Z a ≤ sint.Z b) xs ∧ (∀ x ∈ xs, 0 ≤ sint.Z x ∧ sint.Z x ≤ m) ∧
    0 ≤ m ∧ (xs.length : Int) ≤ rn ∧ 0 ≤ lr ∧ (∀ x ∈ xs.head?, lr ≤ sint.Z x) ∧ (xs = [] → lr = 0)

/-- A round's sample `v`, no smaller than `m`, appended to the window and the window trimmed if it
grew past `retentions`: the invariant holds of the new window, at `v`. -/
theorem windowOk_step (xs ys : List w64) (v : w64) (m rn lr : Int) (hw : windowOk xs m rn lr)
    (hv : m ≤ sint.Z v ∧ 0 ≤ sint.Z v) (hrn : 1 ≤ rn)
    (hys : (ys = xs ++ [v] ∧ (xs.length : Int) + 1 ≤ rn) ∨
      (rn < (xs.length : Int) + 1 ∧ ys = (xs ++ [v]).tail)) :
    windowOk ys (sint.Z v) rn lr := by
  obtain ⟨hpw, hall, hm, hlen, hlr, hhd, hemp⟩ := hw
  have hpw' : List.Pairwise (fun a b => sint.Z a ≤ sint.Z b) (xs ++ [v]) := by
    refine List.pairwise_append.2 ⟨hpw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb; subst hb
    exact Int.le_trans (hall a ha).2 hv.1
  have hall' : ∀ x ∈ xs ++ [v], 0 ≤ sint.Z x ∧ sint.Z x ≤ sint.Z v := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ⟨(hall x hx).1, Int.le_trans (hall x hx).2 hv.1⟩
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨hv.2, Int.le_refl _⟩
  rcases hys with ⟨rfl, hl⟩ | ⟨hl, rfl⟩
  · refine ⟨hpw', hall', hv.2, by simp; omega, hlr, ?_, by simp⟩
    intro x hx
    cases xs with
    | nil => simp at hx; subst hx; rw [hemp rfl]; exact hv.2
    | cons x0 rest => simp at hx; subst hx; exact hhd x0 (by simp)
  · cases xs with
    | nil => simp at hl; omega
    | cons x0 rest =>
      simp only [List.cons_append, List.tail_cons] at hpw' hall' ⊢
      have hpc := List.pairwise_cons.1 hpw'
      refine ⟨hpc.2, fun x hx => hall' x (List.mem_cons_of_mem _ hx), hv.2, ?_, hlr, ?_, ?_⟩
      · simp at hl hlen ⊢; omega
      · intro x hx
        have hx' : x ∈ rest ++ [v] := List.mem_of_mem_head? hx
        exact Int.le_trans (hhd x0 (by simp)) (hpc.1 x hx')
      · simp

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

instance revPermit_persistent (RevLb : Int → IProp GF) (ret r : Int) :
    Persistent (revPermit (GF := GF) RevLb ret r) := by
  unfold revPermit; infer_instance

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

instance firstSample_persistent (γf : GName) (r : Int) : Persistent (firstSample (GF := GF) γf r) := by
  unfold firstSample; infer_instance

/-- A run has one first sample: two `firstSample`s of the same run agree (what makes "at most one
revision per run younger than the period" a fact a client can use). -/
theorem firstSample_agree (γf : GName) (r r' : Int) :
    firstSample (GF := GF) γf r ∗ firstSample γf r' ⊢ ⌜r = r'⌝ := by
  unfold firstSample
  iintro ⟨H1, H2⟩
  icases dghostVar_agree γf (some r) DFrac.discard (some r') DFrac.discard $$ H1 H2 with %Heq
  ipureintro
  exact Option.some.inj Heq

/-- The permit of a mode (`New`'s `mode`; `ret` the retention's nanoseconds or revisions). -/
def modePermit (mode : GoString) (RevLb : Int → IProp GF) (ret : Int) (γf : GName) :
    Int → IProp GF :=
  if mode = go!"revision" then revPermit RevLb ret else perPermit RevLb ret γf

instance modePermit_persistent (mode : GoString) (RevLb : Int → IProp GF) (ret : Int) (γf : GName)
    (r : Int) : Persistent (modePermit (GF := GF) mode RevLb ret γf r) := by
  unfold modePermit; split <;> infer_instance

/-! ### The objects -/

/-- What `New`'s caller supplies: the store's revision lower bounds (`RevLb r`: the store has
reached `r`; the server's is `revLb`), the revision getter, the server, and the resource the
getter's `Rev` and the server's `Compact` take and give back. -/
structure CompactEnv (GF : BundledGFunctors) where
  RevLb : Int → IProp GF
  rg : GoInterface
  c : GoInterface
  R : IProp GF

/-- **What `Run` takes from its caller** (besides the object's run token), for a compactor whose
`Compact` calls take the permit `P`: the revision getter's and the server's contracts (needed only
from `Run` on: `New` calls neither), the resource they thread, and a revision the store has reached
(`0`, the getter's first lower bound). -/
def runPre (E : CompactEnv GF) (P : Int → IProp GF) : IProp GF :=
  iprop(revGetterOk E.RevLb E.rg E.R ∗ compactableOk E.c P E.R ∗ E.R ∗ □ E.RevLb 0)

/-- `paused` under the periodic compactor's `RWMutex`: a fraction of its cell. -/
def perPausedInv (pc : Loc) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, structFieldRef v3compactor.Periodic go!"paused" pc ↦{DFrac.own q} b)

/-! ### `Periodic.Run`'s loop invariant (its proof's; package-internal) -/

/-- **The window's stamps**, at a clock bound `n`: each sample `xs[i]`, oldest first, was reached by
the store at a stamped clock time `T` that the clock is `len - i` waits of `retry` past (the
sample was waited on once in the round that took it, and once in every round since). -/
def stampsOk (RevLb : Int → IProp GF) (retry n : Int) (xs : List w64) : IProp GF :=
  iprop([∗list] i ↦ x ∈ xs, ∃ T : Int,
    clockwork.stampAt clockwork.realClock iprop(□ RevLb (sint.Z x)) T ∗
    ⌜T + ((xs.length : Int) - i) * retry ≤ n⌝)

instance stampsOk_persistent (RevLb : Int → IProp GF) (retry n : Int) (xs : List w64) :
    Persistent (stampsOk (GF := GF) RevLb retry n xs) := by
  unfold stampsOk; infer_instance

/-- A round's sample `v`, stamped at `T` (at least the clock bound `n` the stamps were at) and then
waited on (the clock now `T + r`): one more wait for every sample. -/
theorem stampsOk_snoc (RevLb : Int → IProp GF) (r n T : Int) (xs : List w64) (v : w64)
    (hT : n ≤ T) :
    stampsOk RevLb r n xs ∗ clockwork.stampAt clockwork.realClock iprop(□ RevLb (sint.Z v)) T ⊢
      stampsOk RevLb r (T + r) (xs ++ [v]) := by
  unfold stampsOk
  iintro ⟨Hs, Hv⟩
  iapply BigSepL.bigSepL_snoc.2
  isplitl [Hs]
  · iapply (BigSepL.bigSepL_mono_of_forall (fun {k x} => ?_)) $$ Hs
    iintro ⟨%T', HT', %Hb⟩
    iexists T'
    iframe HT'
    ipureintro
    rw [List.length_append, List.length_singleton]
    have h : (((xs.length + 1 : Nat) : Int) - (k : Int)) * r = ((xs.length : Int) - k) * r + r := by
      rw [show (((xs.length + 1 : Nat) : Int) - (k : Int)) = ((xs.length : Int) - k) + 1 by omega,
        Int.add_mul, Int.one_mul]
    omega
  · iexists T
    iframe Hv
    ipureintro
    rw [List.length_append, List.length_singleton]
    have h : (((xs.length + 1 : Nat) : Int) - (xs.length : Int)) * r = r := by
      rw [show (((xs.length + 1 : Nat) : Int) - (xs.length : Int)) = 1 by omega, Int.one_mul]
    omega

/-- The window trimmed (`revs = revs[1:]`): the samples keep their ages. -/
theorem stampsOk_tail (RevLb : Int → IProp GF) (r n : Int) (x : w64) (xs : List w64) :
    stampsOk RevLb r n (x :: xs) ⊢ stampsOk RevLb r n xs := by
  unfold stampsOk
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨-, H⟩
  iapply (BigSepL.bigSepL_mono_of_forall (fun {k y} => ?_)) $$ H
  iintro ⟨%T, HT, %Hb⟩
  iexists T
  iframe HT
  ipureintro
  rw [List.length_cons] at Hb
  rw [show (((xs.length + 1 : Nat) : Int) - ((k + 1 : Nat) : Int)) = (xs.length : Int) - k by omega] at Hb
  exact Hb

/-- The window's oldest sample and its stamp: as old as the window is long. -/
theorem stampsOk_head (RevLb : Int → IProp GF) (r n : Int) (x : w64) (xs : List w64) :
    stampsOk RevLb r n (x :: xs) ⊢ ∃ T : Int,
      clockwork.stampAt clockwork.realClock iprop(□ RevLb (sint.Z x)) T ∗
      ⌜T + ((x :: xs).length : Int) * r ≤ n⌝ := by
  unfold stampsOk
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%T, HT, %Hb⟩, -⟩
  iexists T
  iframe HT
  ipureintro
  simpa using Hb

/-- **The window's head**: none and the first sample unset; or the run's first sample; or a full
window (trimmed: its head is `retentions` waits old). -/
def firstOk (γf : GName) (retentions : Int) : List w64 → IProp GF
  | [] => firstUnset γf
  | x :: rest => iprop(firstSample γf (sint.Z x) ∨ ⌜((x :: rest).length : Int) = retentions⌝)

/-- The window's head after a round: the first round sets the first sample (the ghost variable,
unset until then, to the round's sample); an untrimmed window keeps its head; a trimmed one is
full. -/
theorem firstOk_step (γf : GName) (rn : Int) (xs ys : List w64) (v : w64) (hrn : 1 ≤ rn)
    (hlen : (xs.length : Int) ≤ rn)
    (hys : (ys = xs ++ [v] ∧ (xs.length : Int) + 1 ≤ rn) ∨
      (rn < (xs.length : Int) + 1 ∧ ys = (xs ++ [v]).tail)) :
    firstOk (GF := GF) γf rn xs ⊢ |==> firstOk γf rn ys := by
  cases xs with
  | nil =>
    rcases hys with ⟨rfl, -⟩ | ⟨hl, -⟩
    · simp only [firstOk, firstUnset, firstSample, List.nil_append]
      iintro H
      imod dghostVar_update (some (sint.Z v)) γf none $$ H with H
      imod dghostVar_persist γf 1 _ $$ H with #H
      imodintro
      ileft
      iexact H
    · simp at hl; omega
  | cons x0 rest =>
    rcases hys with ⟨rfl, hl⟩ | ⟨hl, rfl⟩
    · simp only [firstOk, List.cons_append]
      iintro (#H | %H)
      · imodintro; ileft; iexact H
      · simp at hl H; omega
    · simp only [List.cons_append, List.tail_cons]
      cases rest with
      | nil =>
        simp only [firstOk, List.nil_append]
        iintro -
        imodintro; iright; ipureintro; simp at hl hlen ⊢; omega
      | cons r0 rest' =>
        simp only [firstOk, List.cons_append]
        iintro -
        imodintro; iright; ipureintro; simp at hl hlen ⊢; omega

/-- **C1 from the window** (`Periodic.Run`'s compaction of the window's head `x`): its stamp is the
window's length of waits behind the clock, so the clock is `period` past it when the window is full
(`window_full_age`), and `retry` past it when `x` is the run's first sample. -/
theorem perPermit_of_window (RevLb : Int → IProp GF) (period ri rn n : Int) (γf : GName) (x : w64)
    (rest : List w64) (hp : 10 ≤ period) (hri : ri = retryOf period) (hrn : rn = retentionsOf period)
    (hx : 0 < sint.Z x) :
    stampsOk RevLb ri n (x :: rest) ∗ firstOk γf rn (x :: rest) ∗ clockwork.clockLb clockwork.realClock n ⊢
      perPermit RevLb period γf (sint.Z x) ∗ firstOk γf rn (x :: rest) := by
  iintro ⟨Hst, Hf, #Hn⟩
  icases stampsOk_head $$ Hst with ⟨%T, #HT, %Hb⟩
  have hr : 1 ≤ ri := by subst hri; unfold retryOf; omega
  simp only [firstOk]
  icases Hf with (#Hf | %Hf)
  · have hl : ri ≤ (((x :: rest).length : Int)) * ri := by
      have h1 : (1 : Int) ≤ ((x :: rest).length : Int) := by simp; omega
      have := Int.mul_le_mul_of_nonneg_right h1 (show (0 : Int) ≤ ri by omega)
      omega
    unfold perPermit
    isplitr
    · isplitr
      · ipureintro; exact hx
      iexists T; iframe HT
      iright; iframe Hf
      rw [← hri]
      iapply clockwork.clockLb_le _ _ _ (by omega) $$ Hn
    ileft; iexact Hf
  · have hw := window_full_age period hp
    rw [← hri, ← hrn, ← Hf] at hw
    unfold perPermit
    isplitr
    · isplitr
      · ipureintro; exact hx
      iexists T; iframe HT
      ileft
      iapply clockwork.clockLb_le _ _ _ (by omega) $$ Hn
    iright; ipureintro; exact Hf

/-- `paused`'s fraction family is fractional (the `RWMutex` invariant's requirement): fractions of
the cell split and, agreeing on the value, combine. -/
instance perPausedInv_fractional (pc : Loc) : Fractional (perPausedInv (GF := GF) pc) where
  fractional q1 q2 := by
    have hp : ∀ b : Bool,
        (structFieldRef v3compactor.Periodic go!"paused" pc ↦{DFrac.own (q1 + q2)} b : IProp GF) ⊣⊢
          structFieldRef v3compactor.Periodic go!"paused" pc ↦{DFrac.own q1} b ∗
          structFieldRef v3compactor.Periodic go!"paused" pc ↦{DFrac.own q2} b := fun b =>
      (typedPointsto_dfractional (GF := GF) (structFieldRef v3compactor.Periodic go!"paused" pc) b).dfractional
        (DFrac.own q1) (DFrac.own q2)
    unfold perPausedInv
    refine ⟨?_, ?_⟩
    · iintro ⟨%b, H⟩
      icases (hp b).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists b; iexact H1
      · iexists b; iexact H2
    · iintro ⟨⟨%b1, H1⟩, ⟨%b2, H2⟩⟩
      icombine H1 H2 gives %Hc
      subst Hc
      iexists b1
      iapply (hp b1).2
      iframe

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

/-- **What `Run` takes** of a periodic compactor (besides `runPre`): the sample window `revs`, empty,
with its slice's capacity (what `newPeriodic`'s `make` gives; only `Run`'s goroutine touches it: it
appends to it and reads `revs[0]`), a reader slot of the mutex, and the run's first sample, unset
(`γf`, the ghost name `perPermit`'s `firstSample` is at). -/
def periodicRunTok (pc : Loc) (γf : GName) : IProp GF :=
  iprop((∃ s : GoSlice, structFieldRef v3compactor.Periodic go!"revs" pc ↦ s ∗
      s ↦* ([] : List w64) ∗ ownSliceCap w64 s (DFrac.own 1)) ∗
    sync.ownRWMutex (structFieldRef v3compactor.Periodic go!"mu" pc) (perPausedInv pc) ∗
    firstUnset γf)

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
    sync.isMutex (structFieldRef v3compactor.Revision go!"mu" rc) (revPausedInv rc))

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
