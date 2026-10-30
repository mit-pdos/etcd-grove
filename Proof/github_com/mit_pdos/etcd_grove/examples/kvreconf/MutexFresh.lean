/-
Lean-first (no Rocq counterpart).

# Locking a fresh mutex (2026-10-30, kvreconf-final, helper LIFE)

`sync.Mutex.Lock` on a wholly owned, never-locked mutex (its points-to at `false`) gives the mutex
with any lock invariant `R`, in the locked state (`isMutex m R ∗ ownMutex m`): the lock's
invariant is allocated after the `CmpXchg`, at `locked`, so `R` is first due at the `Unlock`.
`StartCluster` needs it: it locks its cluster's mutex before the cluster's lock invariant holds (the
replicas are inserted under the lock). A general lemma about Perennial's own definitions, proposed
for Perennial (`notes/perennial-changes.md`); this is the stand-in, proved from Perennial's
exported unsealing equations (`isMutex_unseal`, `isLock_unseal`, `ownMutex_unseal`,
`ownLock_unseal`) and `lock.lock`'s code, as Perennial's own `wp_lock_lock`.
-/
module

public import Perennial.Spec.sync.Mutex__Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- **Locking a fresh mutex** (see the file header). -/
theorem wp_Mutex_Lock_fresh (m : Loc) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typedPointsto m false (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); sync.isMutex m R ∗ sync.ownMutex m }} := by
  wp_start as Hm
  simp only [sync.isMutex_unseal, sync.isMutexDef, sync.ownMutex_unseal, sync.ownMutexDef]
  unfold lock.lock
  wp_call
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hm
  iintro Hl
  icases (typedPointsto_quarter_three_quarter m true).1 $$ Hl with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot ⊤ (lockInv m R) $$ [Hl1] with #Hinv
  · inext; iexists true; simp only [↓reduceIte]; iframe
  wp_pures
  iapply HΦ
  rw [isLock_unseal, ownLock_unseal]
  unfold isLockDef ownLockDef
  simp only [named]
  iframe Hinv Hl2

end proof

end kvreconf
end EtcdGrove
end Perennial
