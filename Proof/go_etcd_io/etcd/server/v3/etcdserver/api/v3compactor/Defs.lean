/-
etcd's periodic and revision compactors (`server/etcdserver/api/v3compactor/{periodic,revision}.go`,
with the `interval` field etcd#18472 adds): the shared vocabulary of
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/*.lean`. Lean-first (no Rocq
counterpart). (Started from etcd#22095's verification, branch `pr-verify/etcd-22095`, whose
auto-periodic compactor this branch does not have.)

A `Revision` `rc` holds, read-only once `newRevision` has built it, its logger, clock, retention
(a revision count), `interval` (the wait between compactions, `5 * time.Minute` when `newRevision`
was given `0`), the revision getter `rg`, the compactable `c` and a cancellable context; under the
mutex `rc.mu`, the flag `paused`. `isRevision rc P` (persistent) is all of that.

A `Periodic` `pc` holds, read-only, its logger, clock, `period` (the retention, a duration),
`interval` (`0`: the default), `rg`, `c` and a context; under the `RWMutex` `pc.mu`, the flag
`paused` (`pdLockInv`, fractional: `RLock` gives a fraction of it); and the sliding window of
sampled revisions `pc.revs`, which only `Run`'s goroutine touches after `newPeriodic` (`pdRevs`,
owned, handed to `Run`). `isPeriodic pc P` (persistent) is the read-only part and the mutex's
writer guard (`sync.isRWMutexGuard`); a reader (`Run`'s goroutine) holds one of its reader
tokens, `pdReader pc`.

The callees behind the interfaces are contracts (the trust boundary of the compactors, stated
here and premises of the `Run` specs, not axioms):

* `clockwork.isClockFor clk D` (`clockwork/Defs.lean`): `Now()` returns some time, and
  `After(d)`, for a duration `d` with `D d`, some channel of times. A real clock (`isClock`)
  is one for every `D`; `Run`'s spec takes the clock at `D := (· = interval)`, which says that
  every wait is for exactly that duration.
* `v3cRevOk rg R`: `rg.Rev()` returns some non-negative `v` with `R v`, a persistent fact the
  caller chooses (the server: "the store's current revision is at least `v`").
* `rvCompactOk c R T retention` (the revision compactor): `c.Compact(ctx, req)` with `req` a
  non-physical `CompactionRequest` at revision `r`, called with `r > 0`, `r + retention = v` for
  some `v` with `R v` (so it keeps the last `retention` revisions of a store at revision at least
  `v`), and `r` not the last revision `T` records (`p`); it returns an error `errors.Is` can
  classify (`v3cErrIs`), and then `T p ∧ |==> T r`.
* `pdCompactOk c R T` (the periodic compactor): the same at a revision `r` with `R r` (one the
  getter returned: the periodic compactor compacts at the revision it sampled `period` ago),
  `r ≠ p`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.context
public import Proof.github_com.jonboulle.clockwork.Defs
public import Perennial.Proof.sync.Results
public import Spec.errors.Is

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev rvLgAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"lg" rc
abbrev rvClockAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"clock" rc
abbrev rvRetentionAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"retention" rc
abbrev rvIntervalAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"interval" rc
abbrev rvRgAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"rg" rc
abbrev rvCAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"c" rc
abbrev rvCtxAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"ctx" rc
abbrev rvCancelAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"cancel" rc
abbrev rvMuAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"mu" rc
abbrev rvPausedAddr (rc : Loc) : Loc := structFieldRef v3compactor.Revision go!"paused" rc

abbrev pdLgAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"lg" pc
abbrev pdClockAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"clock" pc
abbrev pdPeriodAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"period" pc
abbrev pdIntervalAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"interval" pc
abbrev pdRgAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"rg" pc
abbrev pdCAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"c" pc
abbrev pdRevsAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"revs" pc
abbrev pdCtxAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"ctx" pc
abbrev pdCancelAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"cancel" pc
abbrev pdMuAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"mu" pc
abbrev pdPausedAddr (pc : Loc) : Loc := structFieldRef v3compactor.Periodic go!"paused" pc

end addrs

/-! ## The durations -/

/-- `time.Hour`, in nanoseconds. -/
abbrev hourNs : w64 := W64 3600000000000

/-- The revision compactor's wait, as `newRevision` sets it from its argument `interval`
(etcd#18472): `5 * time.Minute` for `0`, else `interval`. (Before etcd#18472: always
`5 * time.Minute`, the constant `revInterval`.) -/
def rvInterval (interval : w64) : w64 :=
  if interval = W64 0 then W64 300000000000 else interval

/-- `min(period, time.Hour)` (signed), the base of the periodic compactor's intervals. -/
def pdCapped (period : w64) : w64 :=
  if sint.Z hourNs < sint.Z period then hourNs else period

/-- The periodic compactor's sampling interval, `getRetryInterval()`:
`min(period, time.Hour) / retryDivisor` (Go's truncating signed division). -/
def pdRetry (period : w64) : w64 := BitVec.sdiv (pdCapped period) (W64 10)

/-- The length of the periodic compactor's window, `getRetentions()`:
`int(period / getRetryInterval()) + 1`. -/
def pdRetentions (period : w64) : w64 := BitVec.sdiv period (pdRetry period) + W64 1

/-- The periodic compactor's wait between compactions after the first one,
`getCompactInterval()`: `interval` if it is non-zero (etcd#18472), else
`min(period, time.Hour)`. -/
def pdCompactInterval (period interval : w64) : w64 :=
  if interval = W64 0 then pdCapped period else interval

/-- `getCompactInterval()` before etcd#18472: `min(period, time.Hour)`. -/
abbrev pdCompactIntervalOld (period : w64) : w64 := pdCapped period

theorem pdCompactInterval_zero (period : w64) :
    pdCompactInterval period (W64 0) = pdCompactIntervalOld period := by
  simp [pdCompactInterval]

/-- (Arithmetic of the window's length.) -/
theorem v3c_natdiv_le_half (a b : Nat) (hb : 2 ≤ b) : a / b ≤ a / 2 := Nat.div_le_div_left hb (by omega)

/-- The window's length, over the integers: the retry interval is non-zero and
`period / retry` is in `[0, 2^63 - 1)`. -/
theorem v3c_retentions_int (x : Int) (hx : -2^63 ≤ x ∧ x < 2^63) (h : 10 ≤ x ∨ x ≤ -10) :
    (if 3600000000000 < x then (3600000000000 : Int) else x).tdiv 10 ≠ 0 ∧
    0 ≤ x.tdiv ((if 3600000000000 < x then (3600000000000 : Int) else x).tdiv 10) ∧
    x.tdiv ((if 3600000000000 < x then (3600000000000 : Int) else x).tdiv 10) < 2^63 - 1 := by
  by_cases hA : 3600000000000 < x
  · simp only [hA, ↓reduceIte]
    have : (3600000000000 : Int).tdiv 10 = 360000000000 := by decide
    rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    omega
  simp only [hA, ↓reduceIte]
  rcases h with h | h
  · -- 10 ≤ x ≤ 1h
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have hr : 1 ≤ x / 10 := by omega
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    refine ⟨by omega, Int.ediv_nonneg (by omega) (by omega), ?_⟩
    have := Int.ediv_le_self (x / 10) (show 0 ≤ x by omega)
    have h2 : x / (x / 10) ≤ x := Int.ediv_le_self _ (by omega)
    omega
  · -- x ≤ -10
    have e1 : x.tdiv 10 = -((-x) / 10) := by
      rw [show x = -(-x) by omega, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]; simp
    rw [e1]
    have hr : 1 ≤ (-x) / 10 := by omega
    have e2 : x.tdiv (-((-x) / 10)) = (-x) / ((-x) / 10) := by
      rw [show x = -(-x) by omega, Int.neg_tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]; simp
    rw [e2]
    refine ⟨by omega, Int.ediv_nonneg (by omega) (by omega), ?_⟩
    by_cases h1 : (-x) / 10 = 1
    · rw [h1]; omega
    · have hb : 2 ≤ (-x) / 10 := by omega
      obtain ⟨n, hn⟩ : ∃ n : Nat, -x = n := ⟨(-x).toNat, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m : Nat, (-x) / 10 = m := ⟨((-x)/10).toNat, by omega⟩
      rw [hm, hn]
      have : ((n : Int) / (m : Int)) = ((n / m : Nat) : Int) := by simp
      rw [this]
      have := v3c_natdiv_le_half n m (by omega)
      omega

/-- Go's signed division by `10` truncates. -/
theorem sint_sdiv10 (x : w64) : sint.Z (BitVec.sdiv x (W64 10)) = (sint.Z x).tdiv 10 := by
  simp only [sint.Z]
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr (by decide))]
  rfl

theorem sint_pdCapped (p : w64) :
    sint.Z (pdCapped p) = if 3600000000000 < sint.Z p then 3600000000000 else sint.Z p := by
  unfold pdCapped
  have e : sint.Z hourNs = 3600000000000 := by decide
  rw [e]
  split <;> rfl

theorem sint_pdRetry (p : w64) :
    sint.Z (pdRetry p) = (if 3600000000000 < sint.Z p then (3600000000000 : Int) else sint.Z p).tdiv 10 := by
  unfold pdRetry
  rw [sint_sdiv10, sint_pdCapped]

/-- The retry interval is non-zero once the period is at least 10 ns in absolute value. -/
theorem pdRetry_ne_zero (p : w64) (h : 10 ≤ sint.Z p ∨ sint.Z p ≤ -10) :
    sint.Z (pdRetry p) ≠ 0 := by
  rw [sint_pdRetry]
  exact (v3c_retentions_int (sint.Z p) ⟨by word, by word⟩ h).1

/-- The window has room for at least one revision. -/
theorem pdRetentions_pos (p : w64) (h : 10 ≤ sint.Z p ∨ sint.Z p ≤ -10) :
    1 ≤ sint.Z (pdRetentions p) := by
  have H := v3c_retentions_int (sint.Z p) ⟨by word, by word⟩ h
  rw [← sint_pdRetry] at H
  have hq : sint.Z (BitVec.sdiv p (pdRetry p)) = (sint.Z p).tdiv (sint.Z (pdRetry p)) := by
    simp only [sint.Z]
    rw [BitVec.toInt_sdiv_of_ne_or_ne]
    by_cases hp : sint.Z p = -2^63
    · right
      intro h1
      have h2 : sint.Z (pdRetry p) = -1 := by rw [h1]; rfl
      rw [sint_pdRetry, hp] at h2
      simp at h2
    · left
      intro h1
      apply hp
      rw [h1]; rfl
  unfold pdRetentions
  have : sint.Z (BitVec.sdiv p (pdRetry p) + W64 1) = sint.Z (BitVec.sdiv p (pdRetry p)) + 1 := by
    rw [hq]
    have := H.2.2
    have := H.2.1
    word
  rw [this, hq]
  omega

/-- The read-only fields of a `Revision` (what `newRevision` stores). -/
structure RVParams [FfiSyntax] where
  lg : Loc
  clock : GoInterface
  retention : w64
  interval : w64
  rg : GoInterface
  c : GoInterface

/-- The read-only fields of a `Periodic` (what `newPeriodic` stores). -/
structure PDParams [FfiSyntax] where
  lg : Loc
  clock : GoInterface
  period : w64
  interval : w64
  rg : GoInterface
  c : GoInterface

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A context made by `context.WithCancel(context.Background())`, at the fields `ctxAddr` and
`cancelAddr` (read-only): never done but by `cancel`. -/
def cancellableCtxAt (ctxAddr cancelAddr : Loc) : IProp GF :=
  iprop(∃ (ctx : GoInterfaceOk) (γ : context.ContextNames) (cancel : GoFunc),
      ctxAddr ↦□ GoInterface.ok ctx ∗ cancelAddr ↦□ cancel ∗
      context.isContext ctx { Values := ∅, Deadline := none, Done_gn := γ, PDone := iprop(True) } ∗
      context.cancelSpec cancel γ iprop(True))

instance cancellableCtxAt_persistent (a b : Loc) :
    Persistent (cancellableCtxAt (GF := GF) a b) := by
  unfold cancellableCtxAt; infer_instance

/-! ### The revision compactor -/

/-- The lock invariant of `rc.mu`: the flag `rc.paused`, owned. -/
def rvLockInv (rc : Loc) : IProp GF :=
  iprop(∃ b : Bool, rvPausedAddr rc ↦ b)

/-- `rc` is a revision compactor with fields `P` (persistent). -/
def isRevision (rc : Loc) (P : RVParams) : IProp GF :=
  iprop(rvLgAddr rc ↦□ P.lg ∗ rvClockAddr rc ↦□ P.clock ∗ rvRetentionAddr rc ↦□ P.retention ∗
    rvIntervalAddr rc ↦□ P.interval ∗ rvRgAddr rc ↦□ P.rg ∗ rvCAddr rc ↦□ P.c ∗
    cancellableCtxAt (rvCtxAddr rc) (rvCancelAddr rc) ∗
    sync.isMutex (rvMuAddr rc) (rvLockInv rc))

instance isRevision_persistent (rc : Loc) (P : RVParams) :
    Persistent (isRevision (GF := GF) rc P) := by
  unfold isRevision; infer_instance

/-! ### The periodic compactor -/

/-- The lock invariant of `pc.mu` at fraction `q`: the flag `pc.paused`. -/
def pdLockInv (pc : Loc) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, pdPausedAddr pc ↦{DFrac.own q} b)

instance pdLockInv_fractional (pc : Loc) : Fractional (pdLockInv (GF := GF) pc) where
  fractional q1 q2 := by
    have h : ∀ b : Bool, (pdPausedAddr pc ↦{DFrac.own (q1 + q2)} b : IProp GF) ⊣⊢
        pdPausedAddr pc ↦{DFrac.own q1} b ∗ pdPausedAddr pc ↦{DFrac.own q2} b := fun b =>
      (typedPointsto_dfractional (GF := GF) (pdPausedAddr pc) b).dfractional (DFrac.own q1) (DFrac.own q2)
    unfold pdLockInv
    refine ⟨?_, ?_⟩
    · iintro ⟨%b, Hb⟩
      icases (h b).1 $$ Hb with ⟨H1, H2⟩
      isplitl [H1]
      · iexists b; iexact H1
      · iexists b; iexact H2
    · iintro ⟨⟨%b1, H1⟩, ⟨%b2, H2⟩⟩
      icombine H1 H2 gives %Heq
      subst Heq
      iexists b1
      iapply (h b1).2
      iframe

/-- `pc` is a periodic compactor with fields `P` (persistent): the read-only fields, the
context, and the writer guard of `pc.mu`. -/
def isPeriodic (pc : Loc) (P : PDParams) : IProp GF :=
  iprop(pdLgAddr pc ↦□ P.lg ∗ pdClockAddr pc ↦□ P.clock ∗ pdPeriodAddr pc ↦□ P.period ∗
    pdIntervalAddr pc ↦□ P.interval ∗ pdRgAddr pc ↦□ P.rg ∗ pdCAddr pc ↦□ P.c ∗
    cancellableCtxAt (pdCtxAddr pc) (pdCancelAddr pc) ∗
    sync.isRWMutexGuard (pdMuAddr pc) (pdLockInv pc))

instance isPeriodic_persistent (pc : Loc) (P : PDParams) :
    Persistent (isPeriodic (GF := GF) pc P) := by
  unfold isPeriodic; infer_instance

/-- One reader token of `pc.mu` (what `Run`'s goroutine needs for its `RLock`). -/
def pdReader (pc : Loc) : IProp GF := sync.ownRWMutex (pdMuAddr pc) (pdLockInv pc)

/-- The sampled-revision window `pc.revs`, owned, holding the revisions `xs`. -/
def pdRevs (pc : Loc) (xs : List w64) : IProp GF :=
  iprop(∃ s : GoSlice, pdRevsAddr pc ↦ s ∗ s ↦*□ xs ∗ ownSliceCap w64 s (DFrac.own 1))

/-! ### The callees' contracts -/

/-- The revision getter: `Rev()` returns some non-negative `v` with `R v`. -/
def v3cRevOk (rg : GoInterface) (R : w64 → IProp GF) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rg = GoInterface.ok ri⌝ ∗
    {{ True }} (App (Val #(methods ri.ty go!"Rev" ri.v)) (Val #()))
      {{ (v : w64), RET #v; ⌜0 ≤ sint.Z v⌝ ∗ □ R v }})

instance v3cRevOk_persistent (rg : GoInterface) (R : w64 → IProp GF) :
    Persistent (v3cRevOk (GF := GF) rg R) := by
  unfold v3cRevOk; infer_instance

/-- An error `errors.Is` can classify against any target (the first half of the apply
package's `applyErrIs`). -/
def v3cErrIs (err : GoInterface) : IProp GF :=
  iprop(□ ∀ target : GoInterface, ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
    _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
    ⌜S err ∧ (ptrTarget target → _root_.Perennial.errors.TreeTyped S target)⌝)

instance v3cErrIs_persistent (err : GoInterface) : Persistent (v3cErrIs (GF := GF) err) := by
  unfold v3cErrIs; infer_instance

/-- The revision compactor's compactable (see the file's header). -/
def rvCompactOk (c : GoInterface) (R : w64 → IProp GF) (T : w64 → IProp GF) (retention : w64) :
    IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
    □ ∀ (ctx : GoInterface) (req : Loc) (m : _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest) (p r v : w64),
      {{ req ↦ m ∗ ⌜m.Revision' = r ∧ m.Physical' = false⌝ ∗ T p ∗ □ R v ∗
          ⌜0 < sint.Z r ∧ r ≠ p ∧ sint.Z r + sint.Z retention = sint.Z v⌝ }}
        (App (App (Val #(methods ci.ty go!"Compact" ci.v)) (Val #ctx)) (Val #req))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          v3cErrIs err ∗ (T p ∧ |==> T r) }})

instance rvCompactOk_persistent (c : GoInterface) (R T : w64 → IProp GF) (retention : w64) :
    Persistent (rvCompactOk (GF := GF) c R T retention) := by
  unfold rvCompactOk; infer_instance

/-- The periodic compactor's compactable (see the file's header). -/
def pdCompactOk (c : GoInterface) (R : w64 → IProp GF) (T : w64 → IProp GF) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
    □ ∀ (ctx : GoInterface) (req : Loc) (m : _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest) (p r : w64),
      {{ req ↦ m ∗ ⌜m.Revision' = r ∧ m.Physical' = false⌝ ∗ T p ∗ □ R r ∗ ⌜r ≠ p⌝ }}
        (App (App (Val #(methods ci.ty go!"Compact" ci.v)) (Val #ctx)) (Val #req))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          v3cErrIs err ∗ (T p ∧ |==> T r) }})

instance pdCompactOk_persistent (c : GoInterface) (R T : w64 → IProp GF) :
    Persistent (pdCompactOk (GF := GF) c R T) := by
  unfold pdCompactOk; infer_instance

/-- `mvcc.ErrCompacted`, read-only: a pointer error (`errors.New`), a leaf. -/
def v3cErrCompacted : IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ GoInterface.ok e ∗
    ⌜errLeaf e⌝)

instance v3cErrCompacted_persistent : Persistent (v3cErrCompacted (GF := GF)) := by
  unfold v3cErrCompacted; infer_instance

end defs

section is
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem_err : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` of an error `errors.Is` can classify (`v3cErrIs`) and a pointer-leaf
target: some boolean. (A lemma over `errors.Is`'s spec, `hIs`.) -/
theorem v3compactor.wp_Is_v3cErr (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (e : GoInterfaceOk) (he : errLeaf e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ v3cErrIs err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok e)))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpkg, #Herr⟩ HΦ
  iunfold v3cErrIs at Herr
  ihave ⟨%S, %M, #Ht, %HS⟩ := Herr $$ %(GoInterface.ok e)
  iapply hIs S M err (GoInterface.ok e) (fun tii h => by cases h; exact he.1)
    (HS.2 (fun tii h => by cases h; exact he.1))
  · iframe #; ipureintro; exact HS.1
  iintro !> %b -
  iapply HΦ
  itrivial

end is

end EtcdGrove
end Perennial
