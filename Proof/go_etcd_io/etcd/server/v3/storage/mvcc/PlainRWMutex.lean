/-
**An `RWMutex` no one else can reach** (the restore plan, R3's design point): sequential specs of
`sync.RWMutex`'s `RLock`, `RUnlock`, `Lock` and `Unlock` on memory the caller owns, proved over
Perennial's translation of `sync` (its `Mutex` the trusted spin lock `lock.lock`/`lock.unlock`).
With no other thread, each call takes the fast path and the memory goes through the values
`rwZero` (unlocked, as allocated), `rwR1` (one reader) and `rwW` (write-locked), back to
`rwZero` (so `init_RWMutex` can still turn it into a lock once the memory is shared).

`restoreIntoIndex`'s goroutine owns the index being rebuilt, whose `KeyIndex` and `Insert` lock
and unlock its `RWMutex` (`notes/restore-plan.md`). A Perennial gap: its `RWMutex` specs need the
lock allocated (`isRWMutex`); recorded in `notes/perennial-changes.md`.
-/
module

public import Perennial.Spec.sync.atomic.Int32__Add
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [FfiSyntax]

/-- An unlocked `RWMutex`, as allocated. -/
abbrev rwZero : sync.RWMutex := zero_val sync.RWMutex

/-- An `RWMutex` with one reader and no writer. -/
def rwR1 : sync.RWMutex :=
  sync.RWMutex.mk false (W32 0) (W32 0) { _0' := zero_val _, v' := W32 1 }
    { _0' := zero_val _, v' := W32 0 }

/-- A write-locked `RWMutex` with no reader. -/
def rwW : sync.RWMutex :=
  sync.RWMutex.mk true (W32 0) (W32 0) { _0' := zero_val _, v' := W32 (-(1073741824 : Int)) }
    { _0' := zero_val _, v' := W32 0 }

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem plain.wp_RLock (hAdd : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG)) (rw : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rw ↦ rwZero }}
      (App (Val (rw @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); rw ↦ rwR1 }} := by
  wp_start as Hrw
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hrw
  iStructNamed Hrw
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core hAdd $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (W32 0)
  simp only [sync.atomic.ownInt32_unseal, sync.atomic.ownInt32Def]
  rw [show rwZero.readerCount' = ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32) from rfl]
  iframe readerCount
  iintro readerCount
  imod Hmask with _
  imodintro
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, rwR1]
  iframe

theorem plain.wp_RUnlock (hAdd : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG)) (rw : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rw ↦ rwR1 }}
      (App (Val (rw @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"RUnlock")) (Val #()))
    {{ RET #(); rw ↦ rwZero }} := by
  wp_start as Hrw
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hrw
  iStructNamed Hrw
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core hAdd $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (W32 1)
  simp only [sync.atomic.ownInt32_unseal, sync.atomic.ownInt32Def]
  rw [show rwR1.readerCount' = ({ _0' := zero_val _, v' := W32 1 } : sync.atomic.Int32) from rfl]
  iframe readerCount
  iintro readerCount
  imod Hmask with _
  imodintro
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, rwR1]
  iframe

/-- `Mutex.Lock` (the trusted spin lock) on an unlocked mutex no one else can reach. -/
theorem plain.wp_Mutex_Lock (m : Loc) :
    {{ (m ↦ false : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); (m ↦ true : IProp GF) }} := by
  wp_start as Hm
  unfold lock.lock
  wp_call
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hm
  iintro Hm
  wp_pures
  iapply HΦ
  iexact Hm

/-- `Mutex.Unlock` (the trusted spin lock) on a locked mutex no one else can reach. -/
theorem plain.wp_Mutex_Unlock (m : Loc) :
    {{ (m ↦ true : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); (m ↦ false : IProp GF) }} := by
  wp_start as Hm
  unfold lock.unlock
  wp_call
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc m true true false _ _ rfl $$ Hm
  iintro Hm
  wp_auto
  iapply HΦ
  iexact Hm

theorem plain.wp_Lock (hAdd : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG)) (rw : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rw ↦ rwZero }}
      (App (Val (rw @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); rw ↦ rwW }} := by
  wp_start as Hrw
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hrw
  iStructNamed Hrw
  simp only [internal.race.Enabled]
  wp_auto
  rw [show rwZero.w' = false from rfl]
  wp_apply plain.wp_Mutex_Lock $$ [$w] as w
  (try wp_auto)
  wp_apply_core hAdd $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (W32 0)
  simp only [sync.atomic.ownInt32_unseal, sync.atomic.ownInt32Def]
  rw [show rwZero.readerCount' = ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32) from rfl]
  iframe readerCount
  iintro readerCount
  imod Hmask with _
  imodintro
  wp_auto
  iapply HΦ
  rw [show (W32 0 + W32 (-1073741824) : w32) = W32 (-1073741824) by decide]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, rwW]
  iframe

theorem plain.wp_Unlock (hAdd : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG)) (rw : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rw ↦ rwW }}
      (App (Val (rw @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); rw ↦ rwZero }} := by
  wp_start as Hrw
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hrw
  iStructNamed Hrw
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core hAdd $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (W32 (-1073741824))
  simp only [sync.atomic.ownInt32_unseal, sync.atomic.ownInt32Def]
  rw [show rwW.readerCount' =
    ({ _0' := zero_val _, v' := W32 (-1073741824) } : sync.atomic.Int32) from rfl]
  iframe readerCount
  iintro readerCount
  imod Hmask with _
  imodintro
  wp_auto
  rw [show (W32 (-1073741824) + W32 1073741824 : w32) = W32 0 by decide]
  irevert HΦ w writerSem readerSem readerWait readerCount r i rw
  iclear ∗
  iintro HΦ w writerSem readerSem readerWait readerCount r i rw
  wp_for
  rw [show rwW.w' = true from rfl]
  wp_apply plain.wp_Mutex_Unlock $$ [$w] as w
  (try wp_auto)
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, rwW]
  iframe

end proof

end EtcdGrove
end Perennial
