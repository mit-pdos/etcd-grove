/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/Threads/QPool.lean (241f27e).
-/
/-
A **quarter thread pool** of a resource `R` (decision D15): Perennial's thread pool
(`Perennial/Proof/ThreadPool.lean`) over quarter thread tokens (`rtok t`, `QTok.lean`). A thread
exchanges its quarter `rtok t` for one copy of `R` and a loan `qloan γ t`, and gets the same quarter
back with the copy (`giveBack`), provided the pool was given at least `4 * (threadBound GF - 1)`
copies.

Why the pool cannot run dry: it holds the `b` quarters of the copies lent out (a quarter bank,
`QBank.lean`) and `m` copies, with `4 * (threadBound GF - 1) ≤ b + m`. A borrower brings one more
quarter, and `b + 1` quarters are at most `4 * (threadBound GF - 1)` (`qbank_count`), so `m ≥ 1`.

RWMutex reader tokens through the pool (local copy of `Perennial/Proof/sync/RWMutexThreads.lean`):
a lock has `actualMaxReaders = 2^30 - 1` reader tokens, which suffice for `threadBound GF ≤ 2^28`
(`4 * (2^28 - 1) ≤ 2^30 - 1`).

* `qpool.isQPool N γ R` (persistent), `qpool.qloan γ t` (timeless);
* `qpool.init`, `qpool.borrow`, `qpool.borrow_timeless`, `qpool.borrow_lc`, `qpool.giveBack`;
* `sync.rwmutex.init_RWMutex_qpool`, `sync.init_RWMutex_qpool` (the guarded interface).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QBank
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pre
public import Perennial.Proof.sync.RWMutexThreads

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace qpool

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The pool's invariant: `b` copies lent out, backed by their borrowers' quarters (in the bank
`γ`), and `m` copies left, with `4 * (threadBound GF - 1) ≤ b + m`. -/
def poolInv (γ : GName) (R : IProp GF) : IProp GF :=
  iprop(∃ (b m : Nat), qbank γ b ∗
    ([∗list] _x ∈ List.replicate m (), R) ∗ ⌜4 * (threadBound GF - 1) ≤ b + m⌝)

/-- A pool of copies of `R`, any of which a quarter thread token borrows. -/
def isQPool (N : Namespace) (γ : GName) (R : IProp GF) : IProp GF :=
  inv N (poolInv γ R)

instance isQPool_persistent (N : Namespace) (γ : GName) (R : IProp GF) :
    Persistent (isQPool N γ R) := by
  unfold isQPool; infer_instance

/-- A copy of `R` lent out by the pool `γ` for the quarter of slot `t`, which the pool holds. -/
def qloan (γ : GName) (t : Nat) : IProp GF := qslip γ t

instance qloan_timeless (γ : GName) (t : Nat) : Timeless (qloan (GF := GF) γ t) := by
  unfold qloan; infer_instance

/-- A pool from `n` copies of `R`: `4 * (threadBound GF - 1) ≤ n`. -/
theorem init (N : Namespace) (R : IProp GF) (E : CoPset) (n : Nat)
    (Hn : 4 * (threadBound GF - 1) ≤ n) :
    ([∗list] _x ∈ List.replicate n (), R) ⊢ |={E}=> ∃ γ, isQPool N γ R := by
  iintro HR
  imod qbank_alloc (GF := GF) with ⟨%γ, Hb⟩
  imod inv_alloc N E (poolInv γ R) $$ [Hb HR] with #Hinv
  · inext
    unfold poolInv
    iexists 0, n
    iframe
    ipureintro; omega
  imodintro
  iexists γ
  unfold isQPool
  iexact Hinv

/-- Borrow a copy of `R` with the quarter `rtok t`. -/
theorem borrow (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E) (t : Nat) :
    isQPool N γ R ∗ rtok t ⊢ |={E}=> ▷ R ∗ qloan γ t := by
  iintro ⟨#Hinv, Htok⟩
  unfold isQPool
  iinv Hinv with Hi Hclose
  unfold poolInv
  icases Hi with ⟨%b, %m, >Hb, HR, >%Hle⟩
  icases qbank_count γ b t $$ [Hb Htok] with ⟨%Hlt, Hb, Htok⟩
  · iframe
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [List.replicate]
  icases HR with ⟨HR, HRs⟩
  imod qbank_deposit γ b t $$ [Hb Htok] with ⟨Hb, Hloan⟩
  · iframe
  imod Hclose $$ [Hb HRs] with _
  · inext
    iexists b + 1, m'
    iframe
    ipureintro; omega
  imodintro
  unfold qloan
  iframe

/-- `borrow`, for a timeless `R`. -/
theorem borrow_timeless (N : Namespace) (γ : GName) (R : IProp GF) [Timeless R] (E : CoPset)
    (HN : ↑N ⊆ E) (t : Nat) :
    isQPool N γ R ∗ rtok t ⊢ |={E}=> R ∗ qloan γ t := by
  iintro H
  imod borrow N γ R E HN t $$ H with ⟨>HR, Hl⟩
  imodintro
  iframe

/-- Give a borrowed copy back, for the same quarter `rtok t`. -/
theorem giveBack (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E) (t : Nat) :
    isQPool N γ R ∗ qloan γ t ∗ R ⊢ |={E}=> rtok t := by
  iintro ⟨#Hinv, Hloan, HR⟩
  unfold isQPool qloan
  iinv Hinv with Hi Hclose
  unfold poolInv
  icases Hi with ⟨%b, %m, >Hb, HRs, >%Hle⟩
  imod qbank_withdraw γ b t $$ [Hb Hloan] with ⟨%b', %Hb', Hb, Htok⟩
  · iframe
  subst Hb'
  imod Hclose $$ [Hb HR HRs] with _
  · inext
    iexists b', m + 1
    simp only [List.replicate]
    iframe
    ipureintro; omega
  imodintro
  iexact Htok

end pool

section lc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- `borrow`, the later taken off with a later credit. -/
theorem borrow_lc (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E)
    (t : Nat) :
    £ 1 ∗ isQPool N γ R ∗ rtok t ⊢ |={E}=> R ∗ qloan γ t := by
  iintro ⟨Hlc, H⟩
  imod borrow N γ R E HN t $$ H with ⟨HR, Hl⟩
  imod lc_fupd_elim_later (E := E) $$ Hlc HR with HR
  imodintro
  iframe

end lc

end qpool

namespace sync

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `threadBound GF ≤ 2^28`: the quarters, `4 * (threadBound GF - 1)`, fit in a lock's reader
tokens. -/
theorem quarters_le_actualMaxReaders (Hb : threadBound GF ≤ 2 ^ 28) :
    4 * (threadBound GF - 1) ≤ Int.toNat rwmutex.actualMaxReaders := by
  rw [rwmutex.actualMaxReaders_unseal]; omega

namespace rwmutex

/-- `init_RWMutex`, with every reader token in a quarter thread pool of namespace `Np`. -/
theorem init_RWMutex_qpool {E : CoPset} (N Np : Namespace) (rw : Loc)
    (Hb : threadBound GF ≤ 2 ^ 28) :
    typedPointsto (GF := GF) rw (zero_val RWMutex) (DFrac.own 1) ⊢
    |={E}=> ∃ (γ : RWMutexNames) (γp : GName), isRWMutex rw γ N ∗ ownRWMutex γ (.RLocked 0) ∗
      qpool.isQPool Np γp (ownRLockToken γ) := by
  iintro Hrw
  imod init_RWMutex (E := E) N rw $$ Hrw with ⟨%γ, #His, Hst, Htoks⟩
  imod qpool.init Np (ownRLockToken γ) E _ (quarters_le_actualMaxReaders Hb) $$ Htoks
    with ⟨%γp, #Hpool⟩
  imodintro
  iexists γ, γp
  iframe
  iframe #

end rwmutex

/-- The guarded `init_RWMutex`, with every reader token in a quarter thread pool of namespace
`Np`, and the guard for the writers. -/
theorem init_RWMutex_qpool (P : Qp → IProp GF) {E : CoPset} (Np : Namespace) (rw : Loc)
    [HPfrac : Fractional P] (Hb : threadBound GF ≤ 2 ^ 28) :
    ⊢ ▷ P 1 -∗ typedPointsto (GF := GF) rw (zero_val RWMutex) (DFrac.own 1) ={E}=∗
      ∃ γp : GName, isRWMutexGuard rw P ∗ qpool.isQPool Np γp (ownRWMutex rw P) := by
  iintro HP Hrw
  imod init_RWMutex P (E := E) rw $$ HP Hrw with Htoks
  obtain ⟨n, hn⟩ : ∃ n, Int.toNat rwmutex.actualMaxReaders = n + 1 :=
    ⟨Int.toNat rwmutex.actualMaxReaders - 1, by have := actualMaxReaders_ge_2; omega⟩
  rw [hn]
  simp only [List.replicate]
  icases Htoks with ⟨Htok, Htoks⟩
  icases persistent_entails_left (ownRWMutex_isRWMutexGuard rw P) $$ Htok with ⟨Htok, #Hguard⟩
  imod qpool.init Np (ownRWMutex rw P) E (n + 1)
    (by have := quarters_le_actualMaxReaders Hb; omega) $$ [Htok Htoks] with ⟨%γp, #Hpool⟩
  · simp only [List.replicate]
    iframe
  imodintro
  iexists γp
  iframe #

end wps

end sync

end Perennial
