/-
Lean-first (no Rocq counterpart).

# Locking a fresh mutex (2026-10-30, kvreconf-final, helper LIFE)

`sync.Mutex.Lock` on a wholly owned, never-locked mutex (its points-to at the zero `Mutex`) gives the mutex
with any lock invariant `R`, in the locked state (`isMutex m R ∗ ownMutex m`): the lock's
invariant is allocated after the `CmpXchg`, at `locked`, so `R` is first due at the `Unlock`.
`StartCluster` needs it: it locks its cluster's mutex before the cluster's lock invariant holds (the
replicas are inserted under the lock). A general lemma about Perennial's own definitions, proposed
for Perennial (`notes/perennial-changes.md`); this is the stand-in, proved from Perennial's
exported unsealing equations and the trusted spin lock's code (on the mutex's field `mu`), as
`Proof/sync/MutexOwned`'s `wp_Mutex_Lock_owned` and `init_Mutex_locked` together.
-/
module

public import Perennial.Spec.sync.Mutex__Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvreconf

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- **Locking a fresh mutex** (see the file header). -/
theorem wp_Mutex_Lock_fresh (m : Loc) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typedPointsto m (zero_val sync.Mutex) (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); sync.isMutex m R ∗ sync.ownMutex m }} := by
  wp_start as Hm
  iStructNamed Hm
  simp only [sync.isMutex_unseal, sync.isMutexDef, sync.ownMutex_unseal, sync.ownMutexDef]
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Lock.impl lock.lock
  wp_pures
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc _ false false true _ _ rfl $$ mu
  iintro Hl
  icases (typedPointsto_quarter_three_quarter _ true).1 $$ Hl with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot ⊤ (lockInv (structFieldRef sync.Mutex go!"mu" m) R) $$ [Hl1] with #Hinv
  · inext; iexists true; simp only [↓reduceIte]; iframe
  wp_auto
  iapply HΦ
  rw [isLock_unseal, ownLock_unseal]
  unfold isLockDef ownLockDef
  simp only [named]
  iframe Hinv Hl2

end proof

end raft_kvreconf
end EtcdGrove
end Perennial
