/-
**A `sync.Mutex` no other thread can reach** (2026-11-21, Perennial pin d648cfe22). Lean-first.

Perennial translates `sync.Mutex` as `struct { _ noCopy; mu internal/sync.Mutex }`, its methods
calling the trusted spin lock on `mu` (`TrustedCode/internal/sync.lean`: a `bool`, `false` unlocked).
While the caller owns the whole mutex, `Lock` takes it at once (`wp_Mutex_Lock_owned`) and `Unlock`
gives the zero `Mutex` back (`wp_Mutex_Unlock_owned`); a locked owned mutex (`mutexLocked`) becomes a
shared lock, held, with any invariant (`init_Mutex_locked`, the locked counterpart of Perennial's
`sync.init_Mutex`). Used where a mutex is locked before it is shared (the backend's first commit,
bbolt's `loadFreelist`, the cluster constructors, the `RWMutex` restore). Stand-ins for owned-mutex
specs of Perennial's `sync` (`notes/perennial-changes.md`), proved as Perennial's own
`testMutexLiteral` proof does, from the trusted spin lock's code.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section defs
variable [GooseExts]

/-- A locked `sync.Mutex` (its lock `mu` at `true`). -/
def mutexLocked : sync.Mutex := { «_#0'» := zero_val _, mu' := true }

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `m.Lock()` on a zero `Mutex` the caller owns whole: it is locked. -/
theorem wp_Mutex_Lock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) m (zero_val sync.Mutex) (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); typedPointsto (GF := GF) m mutexLocked (DFrac.own 1) }} := by
  wp_start as Hm
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hm
  iStructNamed Hm
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Lock.impl lock.lock
  wp_pures
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc _ false false true _ _ rfl $$ mu
  iintro mu
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, mutexLocked]
  iframe

/-- `m.Unlock()` on a locked `Mutex` the caller owns whole: the zero `Mutex` back. -/
theorem wp_Mutex_Unlock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) m mutexLocked (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); typedPointsto (GF := GF) m (zero_val sync.Mutex) (DFrac.own 1) }} := by
  wp_start as Hm
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hm
  simp only [mutexLocked]
  iStructNamed Hm
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Unlock.impl lock.unlock
  wp_pures
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc _ true true false _ _ rfl $$ mu
  iintro mu
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, mutexLocked]
  iframe

/-- A locked `Mutex` the caller owns whole becomes a lock with any invariant `R`, held: `R` is
first due at the `Unlock`. -/
theorem init_Mutex_locked (R : IProp GF) (E : CoPset) (m : Loc) :
    ⊢ typedPointsto (GF := GF) m mutexLocked (DFrac.own 1) ={E}=∗
      sync.isMutex m R ∗ sync.ownMutex m := by
  iintro Hm
  simp only [mutexLocked]
  iStructNamed Hm
  simp only [sync.isMutex_unseal, sync.isMutexDef, sync.ownMutex_unseal, sync.ownMutexDef]
  rw [isLock_unseal, ownLock_unseal]; unfold isLockDef ownLockDef
  icases (typedPointsto_quarter_three_quarter _ true).1 $$ mu with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot E (lockInv (structFieldRef sync.Mutex go!"mu" m) R) $$ [Hl1] with #Hinv
  · inext; iexists true; simp only [↓reduceIte]; iframe
  imodintro
  simp only [named]
  iframe Hinv Hl2

end proof

end EtcdGrove
end Perennial
