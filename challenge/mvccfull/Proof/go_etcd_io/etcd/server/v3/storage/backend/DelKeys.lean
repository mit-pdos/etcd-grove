/-
**The backend's deletable keys** (the backend-compaction stage, `notes/backend-cmp-plan.md` 3.2,
decision O1 and its fallback; Draft, 2026-10-28; O2's `dlNone` dropped after review round 1). Lean-first (no Rocq counterpart).

mvcc's compaction deletes keys from the safe-range `Key` bucket, and readers never look them up
again (Go relies on it: a reader reads at or above the compaction revision). The backend's view
then becomes exact only up to those keys: a reader's physical state is *thin* of the logical view
the clients hold, missing only keys registered as deletable. The keys are registered by a
predicate `Φ` the backend's creator fixes (decision O1: a saved predicate, `dlReg`; mvcc's is its
late-bound `delKey`), so the backend's specs need no new parameter.

D22's clean read, restore over a new backend and snapshot sender rely on an exact view: they hold
the registration unfixed (`dlInit`, the opener's), which rules out every deletable key
(`dlInit_noDel`), or fixed at nothing deletable (`dlNoDel`, `dlNoDel_fix`; O1's fallback, a
discrete flag: no later), so that a thin view is exact for them (`thinV_exact`) (after review round 1, F6: the exclusive
token `dlNone` of decision O2, linked to nothing, was dropped).

Draft: the definitions the changed statements are written in. The registration is the backend's
(`BNames.dlg`, the predicate, and `BNames.dlb`, the flag): the constructor allocates them unfixed
and gives their whole fraction to the creator (`dlInit`, in the constructor's post), who fixes them
once: at `true` with the predicate (`dlReg_fix`, a compacting store) or at `false` (`dlNoDel_fix`,
nothing deletable; the store does it where its compaction mode is chosen, `NewStore_backend`; review
round 4, R4-1), or keeps them unfixed for an exact view (`dlInit_noDel`). The readers' invariants are
over the logical view (`rtRest`, `cacheValid`: the thin-view Draft round); the batch lock's
(`batchGhostAt`) is the next step (review round 4, R4-2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

end defs

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The safe-range deletion's slot** (3.4; one definition after review round 1, F9): a reader's
slot of the backend's `safeRangeDeleteMu`, which mvcc's compaction session holds (`kbSR`) and the
bridge's `LockForSafeRangeDelete` read-locks. -/
def srSlot (b : Loc) : IProp GF :=
  sync.ownRWMutex (bF go!"safeRangeDeleteMu" b) (fun _ => iprop(True))

/-- The slot read-locked (between `LockForSafeRangeDelete` and `UnlockForSafeRangeDelete`). -/
def srHeld (b : Loc) : IProp GF :=
  sync.ownRWMutexRLocked (bF go!"safeRangeDeleteMu" b) (fun _ => iprop(True))

end slot

end backend
end EtcdGrove
end Perennial
