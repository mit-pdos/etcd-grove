/-
**A `sync.Mutex` that is owned** (claim #34, stage 2, 2026-11-25): `Lock` and `Unlock` of a mutex no
other thread can see (no lock invariant, no `isMutex`), from the trusted spin lock
(`internal.sync.Mutex.Lock.impl = lock.lock`, `Unlock.impl = lock.unlock`) with the whole points-to:
the first compare-and-swap succeeds. `Lock` takes the mutex at its zero value (unlocked) to
`sync.lockedMutex`, `Unlock` back. What a cluster under construction needs
(`NewClusterFromURLsMap`'s `genID`, then `MemberByName`, call `MemberIDs`/`MemberByName`, which lock
`c` before `Finalize` makes its lock invariant: `membership.clusterOwned`). No trust. These belong in
Perennial's `sync` proofs (`notes/perennial-changes.md`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The mutex held, its other field as the zero value's. -/
def sync.lockedMutex [GooseExts] : _root_.Perennial.sync.Mutex :=
  { (zero_val _root_.Perennial.sync.Mutex) with mu' := true }

theorem sync.zeroMutex_mu [GooseExts] :
    (zero_val _root_.Perennial.sync.Mutex).mu' = false := by
  first | rfl | decide | simp [zero_val, zeroValDef]

theorem sync.lockedMutex_mu [GooseExts] : sync.lockedMutex.mu' = true := rfl

theorem sync.lockedMutex_unlock [GooseExts] :
    ({ sync.lockedMutex with mu' := false } : _root_.Perennial.sync.Mutex) =
      zero_val _root_.Perennial.sync.Mutex := by
  unfold sync.lockedMutex
  first | rfl | (rw [← sync.zeroMutex_mu]) | simp [zero_val, zeroValDef]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `lock.lock` of an owned, unlocked lock: locked. -/
theorem wp_lock_lock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) m false (DFrac.own 1) }} (App (Val lock.lock) (Val #m))
    {{ RET #(); typedPointsto m true (DFrac.own 1) }} := by
  unfold lock.lock
  wp_start_folded as Hl
  wp_call
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hl
  iintro Hl
  wp_pures
  iapply HΦ
  iexact Hl

/-- `lock.unlock` of an owned, locked lock: unlocked. -/
theorem wp_lock_unlock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) m true (DFrac.own 1) }} (App (Val lock.unlock) (Val #m))
    {{ RET #(); typedPointsto m false (DFrac.own 1) }} := by
  unfold lock.unlock
  wp_start_folded as Hl
  wp_call
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc m true true false _ _ rfl $$ Hl
  iintro Hl
  wp_auto
  iapply HΦ
  iexact Hl

variable [package_sem : internal.sync.Assumptions] in
/-- `internal/sync`'s `Lock` of an owned, unlocked mutex. -/
theorem internal.sync.Mutex.wp_Lock_owned (m : Loc) :
    {{ (m ↦ (false : _root_.Perennial.internal.sync.Mutex) : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType _root_.Perennial.internal.sync.Mutex.ty @!! go!"Lock"))
        (Val #()))
    {{ RET #(); m ↦ (true : _root_.Perennial.internal.sync.Mutex) }} := by
  wp_start as Hl
  wp_apply wp_lock_lock_owned $$ Hl as Hl
  iapply HΦ
  iexact Hl

variable [package_sem : internal.sync.Assumptions] in
/-- `internal/sync`'s `Unlock` of an owned, locked mutex. -/
theorem internal.sync.Mutex.wp_Unlock_owned (m : Loc) :
    {{ (m ↦ (true : _root_.Perennial.internal.sync.Mutex) : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType _root_.Perennial.internal.sync.Mutex.ty @!! go!"Unlock"))
        (Val #()))
    {{ RET #(); m ↦ (false : _root_.Perennial.internal.sync.Mutex) }} := by
  wp_start as Hl
  wp_apply wp_lock_unlock_owned $$ Hl as Hl
  iapply HΦ
  iexact Hl

variable [package_sem : _root_.Perennial.sync.Assumptions] in
/-- **`sync.Mutex.Lock` of an owned, unlocked mutex**: held (`sync.lockedMutex`). -/
theorem sync.Mutex.wp_Lock_owned (m : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ m ↦ zero_val _root_.Perennial.sync.Mutex }}
      (App (Val (m @!! go.GoType.PointerType _root_.Perennial.sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); m ↦ sync.lockedMutex }} := by
  wp_start as Hm
  icases (access_strict (A := typedPointsto (GF := GF)
      (structFieldRef _root_.Perennial.sync.Mutex go!"mu" m)
      (zero_val _root_.Perennial.sync.Mutex).mu' (DFrac.own 1))
      (A' := typedPointsto (GF := GF) (structFieldRef _root_.Perennial.sync.Mutex go!"mu" m)
        (true : _root_.Perennial.internal.sync.Mutex) (DFrac.own 1))) $$ Hm with ⟨Hmu, Hback⟩
  rw [sync.zeroMutex_mu]
  wp_auto
  wp_apply internal.sync.Mutex.wp_Lock_owned $$ Hmu as Hmu
  iapply HΦ
  unfold sync.lockedMutex
  iapply Hback
  iexact Hmu

variable [package_sem : _root_.Perennial.sync.Assumptions] in
/-- **`sync.Mutex.Unlock` of an owned, held mutex**: unlocked, the zero value again. -/
theorem sync.Mutex.wp_Unlock_owned (m : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ m ↦ sync.lockedMutex }}
      (App (Val (m @!! go.GoType.PointerType _root_.Perennial.sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); m ↦ zero_val _root_.Perennial.sync.Mutex }} := by
  wp_start as Hm
  icases (access_strict (A := typedPointsto (GF := GF)
      (structFieldRef _root_.Perennial.sync.Mutex go!"mu" m)
      sync.lockedMutex.mu' (DFrac.own 1))
      (A' := typedPointsto (GF := GF) (structFieldRef _root_.Perennial.sync.Mutex go!"mu" m)
        (false : _root_.Perennial.internal.sync.Mutex) (DFrac.own 1))) $$ Hm with ⟨Hmu, Hback⟩
  rw [sync.lockedMutex_mu]
  wp_auto
  wp_apply internal.sync.Mutex.wp_Unlock_owned $$ Hmu as Hmu
  iapply HΦ
  rw [← sync.lockedMutex_unlock]
  iapply Hback
  iexact Hmu

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`c.Lock()` of a cluster not yet shared** (`RaftCluster`'s promoted `Lock`): its mutex held. -/
theorem membership.wp_RaftCluster_Lock_owned (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
        membership.rcMutexAddr c ↦ zero_val _root_.Perennial.sync.Mutex }}
      (App (Val (c @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); membership.rcMutexAddr c ↦ sync.lockedMutex }} := by
  wp_start as Hm
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock_owned $$ [$Hm] as Hm
  iapply HΦ
  iexact Hm

/-- **`c.Unlock()` of a cluster not yet shared**: its mutex unlocked, the zero value again. -/
theorem membership.wp_RaftCluster_Unlock_owned (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
        membership.rcMutexAddr c ↦ sync.lockedMutex }}
      (App (Val (c @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); membership.rcMutexAddr c ↦ zero_val _root_.Perennial.sync.Mutex }} := by
  wp_start as Hm
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Unlock_owned $$ [$Hm] as Hm
  iapply HΦ
  iexact Hm

end proof

end EtcdGrove
end Perennial
