/-
**A `sync.Mutex` that is owned** (claim #34, stage 2, 2026-11-25): `Lock` and `Unlock` of a mutex no
other thread can see (no lock invariant, no `isMutex`), from `Proof/sync/MutexOwned`'s
`wp_Mutex_Lock_owned`/`wp_Mutex_Unlock_owned` (Perennial's `internal/sync` Go model, 2026-11-25:
the `state` cell's compare-and-swap succeeds with the whole points-to). `Lock` takes the mutex at its zero value (unlocked) to
`sync.lockedMutex`, `Unlock` back. What a cluster under construction needs
(`NewClusterFromURLsMap`'s `genID`, then `MemberByName`, call `MemberIDs`/`MemberByName`, which lock
`c` before `Finalize` makes its lock invariant: `membership.clusterOwned`). No trust. These belong in
Perennial's `sync` proofs (`notes/perennial-changes.md`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build
public import Proof.sync.MutexOwned

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The mutex held: `Proof/sync/MutexOwned`'s `mutexLocked` (its `mu.state` at `1`, the rest zero). -/
abbrev sync.lockedMutex [GooseExts] : _root_.Perennial.sync.Mutex := mutexLocked

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [package_sem : _root_.Perennial.sync.Assumptions] in
/-- **`sync.Mutex.Lock` of an owned, unlocked mutex**: held (`sync.lockedMutex`). -/
theorem sync.Mutex.wp_Lock_owned (m : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ m ↦ zero_val _root_.Perennial.sync.Mutex }}
      (App (Val (m @!! go.GoType.PointerType _root_.Perennial.sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); m ↦ sync.lockedMutex }} := by
  wp_start_folded as Hm
  wp_apply wp_Mutex_Lock_owned $$ Hm as Hm
  iapply HΦ
  iexact Hm

variable [package_sem : _root_.Perennial.sync.Assumptions] in
/-- **`sync.Mutex.Unlock` of an owned, held mutex**: unlocked, the zero value again. -/
theorem sync.Mutex.wp_Unlock_owned (m : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ m ↦ sync.lockedMutex }}
      (App (Val (m @!! go.GoType.PointerType _root_.Perennial.sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); m ↦ zero_val _root_.Perennial.sync.Mutex }} := by
  wp_start_folded as Hm
  wp_apply wp_Mutex_Unlock_owned $$ Hm as Hm
  iapply HΦ
  iexact Hm

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
