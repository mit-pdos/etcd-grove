/-
**An `RWMutex` made a lock while its creator holds it** (B3, mvccfull F1, 2026-11-10; a Perennial
gap, `notes/perennial-changes.md`): Perennial's `sync.init_RWMutex` makes a lock only of an unlocked
`RWMutex` (`zero_val`). `NewStore` locks `s.mu` while it is still private (`plain.wp_Lock`, its memory
at `rwW`), and in compaction mode `restore()` resumes a compaction (`compactLockfree`) before the
deferred `s.mu.Unlock()`: that call needs the store (`isStore`), whose `s.mu` is a lock. So the lock
is made from the write-locked memory: the guard's write-locked state (`ownRWMutexWLocked`, which
`RWMutex.wp_Unlock_guard` takes with `P 1`) and every reader slot. The proof mirrors
`sync.rwmutex.init_RWMutex` and `sync.init_RWMutex` at the protocol's `Locked` state (`IsLocked`:
the inner `Mutex` locked, its `ownMutex` in the invariant's locked part). General: to be proposed to
Perennial (`init_RWMutex_wlocked`).
-/
module

public import Perennial.Proof.sync.RWMutexGuard
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.PlainRWMutex

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open sync

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- A lock made of locked memory, with its lock token. -/
theorem init_lock_locked (R : IProp GF) (E : CoPset) (m : Loc) :
    ⊢ typedPointsto (GF := GF) m true (DFrac.own 1) ={E}=∗ isLock m R ∗ ownLock m := by
  iintro Hl
  rw [isLock_unseal, ownLock_unseal]; unfold isLockDef ownLockDef
  icases (typedPointsto_quarter_three_quarter m true).1 $$ Hl with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot E (lockInv m R) $$ [Hl1] with #Hinv
  · inext
    unfold lockInv
    iexists true
    simp only [↓reduceIte]
    iframe
  imodintro
  iframe Hl2
  iframe Hinv

/-- The protocol's lock made of write-locked memory (`rwW`), in the `Locked` state. -/
theorem rwmutex_init_wlocked {E : CoPset} (N : Namespace) (rw : Loc) :
    typedPointsto (GF := GF) rw rwW (DFrac.own 1) ⊢
    |={E}=> ∃ γ : rwmutex.RWMutexNames, rwmutex.isRWMutex rw γ N ∗
      rwmutex.ownRWMutex γ .Locked ∗
      [∗list] _x ∈ List.replicate (Int.toNat rwmutex.actualMaxReaders) (), rwmutex.ownRLockToken γ := by
  iintro Hrw
  iStructNamed Hrw
  rw [show rwW.readerSem' = W32 0 from rfl, show rwW.writerSem' = W32 0 from rfl,
    show rwW.readerCount' =
      ({ «_#0'» := zero_val _, v' := W32 (-(1073741824 : Int)) } : sync.atomic.Int32) from rfl,
    show rwW.readerWait' =
      ({ «_#0'» := zero_val _, v' := W32 0 } : sync.atomic.Int32) from rfl,
    show rwW.w' = true from rfl]
  imod ownTokAuth_alloc (GF := GF) with ⟨%γread_wait, Hread_wait⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrlock, Hrlock⟩
  imod ownTokAuth_add (Int.toNat rwmutex.actualMaxReaders) γrlock 0 $$ Hrlock with ⟨Hrlock, Htoks⟩
  imod ghostVar_alloc WlockState.IsLocked with ⟨%γwl, Hwl⟩
  icases ghostVar_split γwl WlockState.IsLocked (1 : Qp).half (1 : Qp).half $$ [Hwl]
    with ⟨Hwl, Hwl_inv⟩
  · rw [Qp.half_add_half]; iexact Hwl
  imod ghostVar_alloc rwmutex.Locked with ⟨%γst, Hst⟩
  icases ghostVar_split γst rwmutex.Locked (1 : Qp).half (1 : Qp).half $$ [Hst]
    with ⟨Hst, Hst_inv⟩
  · rw [Qp.half_add_half]; iexact Hst
  imod ghostVar_alloc () with ⟨%γwt, Hwt⟩
  imod sync.init_sema (E := E) (N.@"sema") (rwmutex.RWReaderSem rw) (W32 0) $$ readerSem
    with ⟨%γrs, #Hrs, Hrs_own⟩
  imod sync.init_sema (E := E) (N.@"sema") (rwmutex.RWWriterSem rw) (W32 0) $$ writerSem
    with ⟨%γws, #Hws, Hws_own⟩
  let γ : rwmutex.RWMutexNames := ⟨⟨γread_wait, γrlock, γwl, γwt, γst⟩, γrs, γws⟩
  imod init_lock_locked (ghostVar γwl (1 : Qp).half (WlockState.NotLocked (W32 0))) E
    (rwmutex.RWW rw) $$ w with ⟨#Hmu, Hown⟩
  imod ownToks_0 (GF := GF) γrlock with H0
  ihave Hprot : rwmutex.ownRWMutexInvariant (GF := GF) γ.protGn (W32 0) (W32 0)
      (W32 (-(1073741824 : Int))) (W32 0) rwmutex.Locked $$ [Hread_wait Hwl_inv Hrlock H0 Hwt]
  · simp only [rwmutex.ownRWMutexInvariant_unseal, rwmutex.ownRWMutexInvariantDef]
    iexists WlockState.IsLocked, (W32 0), 0
    simp only [rwmutex.rwInvReaders, rwmutex.rwInvOutstanding, rwmutex.rwInvWriter,
      rwmutex.rwInvMain, rwmutex.RwReaderCountRel, show (sint.Z (W32 0)).toNat = 0 from rfl, Nat.zero_add]
    iframe
    simp only [named]
    ipureintro
    simp only [rwmutex.rwmutexMaxReadersZ]
    and_intros <;> word
  imod inv_alloc (N.@"inv") E (rwmutex.rwInv rw γ) $$ [Hst_inv Hrs_own Hws_own readerCount
      readerWait Hprot Hown Hwl] with #Hinv
  · inext
    iexists (W32 0), (W32 0), (W32 (-(1073741824 : Int))), (W32 0), rwmutex.Locked
    simp only [rwmutex.rwLockedPart, sync.atomic.ownInt32_unseal, sync.atomic.ownInt32Def]
    simp only [named, ownMutex_unseal, ownMutexDef]
    iframe
  imodintro
  iexists γ
  simp only [rwmutex.isRWMutex_unseal, rwmutex.isRWMutexDef, rwmutex.ownRWMutex_unseal,
    rwmutex.ownRWMutexDef, rwmutex.ownRLockToken_unseal, rwmutex.ownRLockTokenDef]
  simp only [isMutex_unseal, isMutexDef]
  iframe Hst
  iframe #
  iapply rwmutex.ownToks_replicate $$ [Htoks]
  iexact Htoks

/-- **The guarded lock made of write-locked memory** (`init_RWMutex` at `rwW`): the write-locked
state (`RWMutex.wp_Unlock_guard` takes it with `P 1`) and every reader slot. -/
theorem init_RWMutex_wlocked (P : Qp → IProp GF) {E : CoPset} (rw : Loc) [HPfrac : Fractional P] :
    ⊢ typedPointsto (GF := GF) rw rwW (DFrac.own 1) ={E}=∗
      ownRWMutexWLocked rw P ∗
      [∗list] _x ∈ List.replicate (Int.toNat rwmutex.actualMaxReaders) (), ownRWMutex rw P := by
  iintro Hrw
  imod rwmutex_init_wlocked (E := E) (nroot.@"rw") rw $$ Hrw with ⟨%γ, #His, Hstate, Hrtoks⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γmax, Hauth⟩
  imod ownTokAuth_add (Int.toNat rwmutex.actualMaxReaders) γmax 0 $$ Hauth with ⟨Hauth, Htoks⟩
  simp only [Nat.zero_add]
  imod (update_into_persistently (P := ownTokAuthDfrac (GF := GF) γmax (DFrac.own 1) _)) $$ Hauth
    with #Hauth
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrlocked, Hrauth⟩
  imod ghostVar_alloc () with ⟨%γlocked, Hl⟩
  imod inv_alloc (nroot.@"inv") E
    iprop(∃ st, rwmutex.ownRWMutex γ st ∗ rwmutex_guard.invSt P γrlocked γmax γlocked st)
    $$ [Hstate Hrauth] with #Hinv
  · inext
    iexists rwmutex.Locked
    iframe Hstate
    simp only [rwmutex_guard.invSt]
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
  imodintro
  isplitl [Hl]
  · simp only [ownRWMutexWLocked_unseal, ownRWMutexWLockedDef]
    iexists γ, γmax, γrlocked, γlocked
    iframe Hl
    iframe #
  iapply replicate_helper $$ [$Hmk $Htoks $Hrtoks]

end proof

end EtcdGrove
end Perennial
