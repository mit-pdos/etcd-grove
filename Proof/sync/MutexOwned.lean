/-
**A `sync.Mutex` no other thread can reach** (2026-11-21; ported 2026-11-24 to Perennial's
`internal/sync` Go model, pin 5ca3ae3dd). Lean-first.

Perennial translates `sync.Mutex` as `struct { _ noCopy; mu internal/sync.Mutex }`, its methods
calling `mu`'s, and `internal/sync.Mutex` (`struct { state int32; sema uint32 }`) is a Go model: a
spin lock on `state` (`0` unlocked, `1` locked) over `sync/atomic`'s compare-and-swap.
While the caller owns the whole mutex, `Lock` takes it at once (`wp_Mutex_Lock_owned`) and `Unlock`
gives the zero `Mutex` back (`wp_Mutex_Unlock_owned`); a locked owned mutex (`mutexLocked`) becomes a
shared lock, held, with any invariant (`init_Mutex_locked`, the locked counterpart of Perennial's
`sync.init_Mutex`). Used where a mutex is locked before it is shared (the backend's first commit,
bbolt's `loadFreelist`, the cluster constructors, the `RWMutex` restore). Stand-ins for owned-mutex
specs of Perennial's `sync` (`notes/perennial-changes.md`), proved as Perennial's own
`testMutexLiteral` proof does (its `wp_Lock_owned`/`wp_Unlock_owned`: the `state` cell's
compare-and-swap, `sync/atomic`'s model unfolded, so no package need be initialized).
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

/-- A locked `sync.Mutex` (its `mu.state` at `1`, the rest zero). -/
def mutexLocked : sync.Mutex :=
  { zero_val sync.Mutex with mu' := { (zero_val sync.Mutex).mu' with state' := W32 1 } }

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `Lock` on a `Mutex` whose `state` cell the caller owns and is unlocked (`0`): the model's
compare-and-swap succeeds (Perennial's `testMutexLiteral.lean`, `wp_Lock_owned`). -/
theorem wp_Mutex_Lock_state (m : Loc) (v : w32) :
    {{ ⌜v = W32 0⌝ ∗ typedPointsto (GF := GF)
        (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) v
        (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); typedPointsto
        (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) (W32 1)
        (DFrac.own 1) }} := by
  wp_start as ⟨%hv, Hs⟩
  subst hv
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Lock.impl
  simp only [internal.sync.mutexLocked]
  wp_auto
  wp_for
  wp_func_call
  unfold sync.atomic.CompareAndSwapInt32.impl
  wp_pures
  wp_bind (CmpXchgBytes _ _ _)
  wp_apply_core wp_cmpxchg_bytes_suc_typed _ (W32 0) (W32 0) (W32 1) _ _ rfl $$ Hs
  iintro Hs
  wp_auto
  cleanup_bool_decide
  wp_auto
  iapply HΦ $$ Hs

/-- `Unlock` on a `Mutex` whose `state` cell the caller owns and is locked (`1`) (Perennial's
`testMutexLiteral.lean`, `wp_Unlock_owned`). -/
theorem wp_Mutex_Unlock_state (m : Loc) :
    {{ typedPointsto (GF := GF)
        (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) (W32 1)
        (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); typedPointsto
        (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) (W32 0)
        (DFrac.own 1) }} := by
  wp_start as Hs
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Unlock.impl
  simp only [internal.sync.mutexLocked]
  wp_auto
  wp_func_call
  unfold sync.atomic.CompareAndSwapInt32.impl
  wp_pures
  wp_bind (CmpXchgBytes _ _ _)
  wp_apply_core wp_cmpxchg_bytes_suc_typed _ (W32 1) (W32 1) (W32 0) _ _ rfl $$ Hs
  iintro Hs
  wp_auto
  iapply HΦ $$ Hs

/-- `m.Lock()` on a zero `Mutex` the caller owns whole: it is locked. -/
theorem wp_Mutex_Lock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) m (zero_val sync.Mutex) (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); typedPointsto (GF := GF) m mutexLocked (DFrac.own 1) }} := by
  wp_start as Hm
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hm
  iStructNamed Hm
  ihave %Hnnmu := typedPointsto_not_null _ _ _ $$ mu
  iStructNamed mu
  wp_apply wp_Mutex_Lock_state $$ [state] as state
  · iframe; ipureintro; rfl
  ihave Hmu : typedPointsto (GF := GF) (structFieldRef sync.Mutex go!"mu" m)
      ({ (zero_val sync.Mutex).mu' with state' := W32 1 } : internal.sync.Mutex)
      (DFrac.own 1) $$ [state sema]
  · iapply typedPointsto_combine _ _ _ Hnnmu
    simp only [TypedPointsto.typedPointstoDef]
    iframe
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
  iStructNamed Hm
  ihave %Hnnmu := typedPointsto_not_null _ _ _ $$ mu
  iStructNamed mu
  simp only [mutexLocked]
  wp_apply wp_Mutex_Unlock_state $$ [state] as state
  ihave Hmu : typedPointsto (GF := GF) (structFieldRef sync.Mutex go!"mu" m)
      (zero_val sync.Mutex).mu' (DFrac.own 1) $$ [state sema]
  · iapply typedPointsto_combine _ _ _ Hnnmu
    simp only [TypedPointsto.typedPointstoDef]
    rw [show (zero_val sync.Mutex).mu'.state' = W32 0 from rfl]
    iframe
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- A locked `Mutex` the caller owns whole becomes a lock with any invariant `R`, held: `R` is
first due at the `Unlock`. -/
theorem init_Mutex_locked (R : IProp GF) (E : CoPset) (m : Loc) :
    ⊢ typedPointsto (GF := GF) m mutexLocked (DFrac.own 1) ={E}=∗
      sync.isMutex m R ∗ sync.ownMutex m := by
  iintro Hm
  iStructNamed Hm
  iStructNamed mu
  simp only [mutexLocked]
  simp only [sync.isMutex_unseal, sync.isMutexDef, sync.ownMutex_unseal, sync.ownMutexDef]
  rw [isLock_unseal, ownLock_unseal]; unfold isLockDef ownLockDef
  icases (typedPointsto_quarter_three_quarter _ (W32 1)).1 $$ state with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot E
    (lockInv (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) R)
    $$ [Hl1] with #Hinv
  · inext
    unfold lockInv
    iexists (W32 1)
    iframe
    simp only [show (W32 1 : w32) ≠ W32 0 by decide, ↓reduceIte]
    itrivial
  imodintro
  try simp only [named]
  iframe Hinv Hl2

end proof

end EtcdGrove
end Perennial
