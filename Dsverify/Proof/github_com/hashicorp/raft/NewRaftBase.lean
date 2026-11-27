/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/NewRaftBase.lean (241f27e).
-/
/-
Helpers of the proof of `raft.NewRaft` (API): a guarded `RWMutex` with its reader tokens in a
thread pool, made from a lock that was first used at the low level (`NewRaft` calls
`setLeader`, which write-locks `leaderLock`, before the lock invariant can be stated: the
writer must see the fields it compares).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QPool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

open rwmutex_guard in
/-- `init_RWMutex_qpool` from the low-level state `init_RWMutex` makes (after any number of
low-level `Lock`/`Unlock` pairs, which come back to it). -/
theorem init_RWMutex_threadPool_low (P : Qp → IProp GF) {E : CoPset} (Np : Namespace) (rw : Loc)
    (γ : rwmutex.RWMutexNames) [HPfrac : Fractional P] (Hb : threadBound GF ≤ 2 ^ 28) :
    ⊢ ▷ P 1 -∗ rwmutex.isRWMutex rw γ (nroot.@"rw") -∗ rwmutex.ownRWMutex γ (.RLocked 0) -∗
      ([∗list] _x ∈ List.replicate (Int.toNat rwmutex.actualMaxReaders) (), rwmutex.ownRLockToken γ)
      ={E}=∗
      ∃ γp : GName, isRWMutexGuard rw P ∗ qpool.isQPool Np γp (ownRWMutex rw P) := by
  iintro HP #His Hstate Hrtoks
  imod ownTokAuth_alloc (GF := GF) with ⟨%γmax, Hauth⟩
  imod ownTokAuth_add (Int.toNat rwmutex.actualMaxReaders) γmax 0 $$ Hauth with ⟨Hauth, Htoks⟩
  simp only [Nat.zero_add]
  imod (update_into_persistently (P := ownTokAuthDfrac (GF := GF) γmax (DFrac.own 1) _)) $$ Hauth
    with #Hauth
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrlocked, Hrauth⟩
  imod ghostVar_alloc () with ⟨%γlocked, Hl⟩
  imod ownToks_0 (GF := GF) γmax with H0
  imod inv_alloc (nroot.@"inv") E
    iprop(∃ st, rwmutex.ownRWMutex γ st ∗ invSt P γrlocked γmax γlocked st) $$ [Hstate Hrauth Hl H0 HP]
    with #Hinv
  · inext
    iexists (rwmutex.RLocked 0)
    iframe Hstate
    simp only [invSt]
    rw [invFrac_0]
    iframe
  ihave #HPf : (□ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) : IProp GF) $$ []
  · imodintro
    iintro %q1 %q2
    isplit
    · iintro H; iapply (HPfrac.fractional q1 q2).1 $$ H
    · iintro H; iapply (HPfrac.fractional q1 q2).2 $$ H
  ihave #Hmk : (□ (rwmutex.ownRLockToken γ -∗ ownToks γmax 1 -∗ ownRWMutex rw P) : IProp GF) $$ []
  · imodintro
    iintro Hrtok Htok
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    iexists γ, γmax, γrlocked, γlocked
    iframe Hrtok Htok
    iframe #
  ihave Htoks := replicate_helper _ _ _ _ $$ [$Hmk $Htoks $Hrtoks]
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
