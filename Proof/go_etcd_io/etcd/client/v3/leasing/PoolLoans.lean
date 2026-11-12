/-
Two laws of Perennial's thread pools (`Perennial/Proof/ThreadPool.lean`) that the leasing KV's
reader-slot pool needs (`notes/bounds-plan.md`, B2's leasing pilot). They belong to no Go package:
they are **Perennial changes**, kept here until they land in `ThreadPool.lean`
(`notes/perennial-changes.md`, "A thread pool's loans are fewer than the live threads").

* `threadPool.loans_lt`: `k` loan receipts of a pool are fewer than `threadBound GF`, since the
  pool holds a thread token for each. A structure that counts goroutines each holding a borrowed
  copy (a wait group whose running slots hold the loan receipts instead of thread tokens) bounds
  its count with it.
* `threadPool.init_named`: `init`, for a name allocated beforehand (`ownTokAuth γ 0`), so that the
  name can be part of the ghost names the pooled resource is defined over.
-/
module

public import Perennial.Proof.ThreadPool

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace threadPool

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **`k` loans of a pool are fewer than the live threads**: the pool holds a thread token for
each loan. -/
theorem loans_lt (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (HN : ↑N ⊆ E) (k : Nat) :
    isThreadPool N γ R ∗ ownToks γ k ⊢ |={E}=> ⌜k < threadBound GF⌝ ∗ ownToks γ k := by
  iintro ⟨#Hinv, Hk⟩
  unfold isThreadPool
  iinv Hinv with Hi Hclose
  unfold poolInv
  icases Hi with ⟨%b, %m, >Hauth, >Htoks, HRs, >%Hle⟩
  icombine Hauth Hk gives %Hkb
  icases persistent_entails_left (threadToks_lt b) $$ Htoks with ⟨Htoks, %Hlt⟩
  imod Hclose $$ [Hauth Htoks HRs] with _
  · inext
    iexists b, m
    iframe
    ipureintro; exact Hle
  imodintro
  iframe
  ipureintro; omega

/-- **A pool under a name allocated beforehand** (`init`, with `ownTokAuth γ 0` given). -/
theorem init_named (N : Namespace) (γ : GName) (R : IProp GF) (E : CoPset) (n : Nat)
    (Hn : threadBound GF ≤ n + 1) :
    ownTokAuth γ 0 ∗ ([∗list] _x ∈ List.replicate n (), R) ⊢ |={E}=> isThreadPool N γ R := by
  iintro ⟨Hauth, HR⟩
  imod inv_alloc N E (poolInv γ R) $$ [Hauth HR] with #Hinv
  · inext
    unfold poolInv
    iexists 0, n
    iframe
    isplitr
    · iapply threadToks_zero
    · ipureintro; omega
  imodintro
  unfold isThreadPool
  iexact Hinv

end pool

end threadPool

end Perennial
