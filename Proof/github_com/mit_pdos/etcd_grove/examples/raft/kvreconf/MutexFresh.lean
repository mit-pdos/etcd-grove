/-
Lean-first (no Rocq counterpart).

# Locking a fresh mutex (2026-10-30, kvreconf-final, helper LIFE)

`sync.Mutex.Lock` on a wholly owned, never-locked mutex (its points-to at the zero `Mutex`) gives the mutex
with any lock invariant `R`, in the locked state (`isMutex m R ∗ ownMutex m`): the lock's
invariant is allocated after the compare-and-swap, at locked, so `R` is first due at the `Unlock`.
`StartCluster` needs it: it locks its cluster's mutex before the cluster's lock invariant holds (the
replicas are inserted under the lock). A general lemma about Perennial's own definitions, proposed
for Perennial (`notes/perennial-changes.md`); this is the stand-in, `Proof/sync/MutexOwned`'s
`wp_Mutex_Lock_owned` and `init_Mutex_locked` together (2026-11-24: over Perennial's
`internal/sync` Go model, the `state` cell's compare-and-swap from `0` to `1`).
-/
module

public import Perennial.Spec.sync.Mutex__Lock
public import Proof.sync.MutexOwned

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
  iapply wp_fupd
  wp_apply wp_Mutex_Lock_owned $$ Hm as Hm
  imod init_Mutex_locked R ⊤ m $$ Hm with ⟨#Hmux, Hown⟩
  imodintro
  iapply HΦ
  iframe

end proof

end raft_kvreconf
end EtcdGrove
end Perennial
