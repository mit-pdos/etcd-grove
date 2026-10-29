/-
**The backend's deletable keys** (the backend-compaction stage, `notes/backend-cmp-plan.md` 3.2,
decisions O1 and O2; Draft, 2026-10-28). Lean-first (no Rocq counterpart).

mvcc's compaction deletes keys from the safe-range `Key` bucket, and readers never look them up
again (Go relies on it: a reader reads at or above the compaction revision). The backend's view
then becomes exact only up to those keys: a reader's physical state is *thin* of the logical view
the clients hold, missing only keys registered as deletable. The keys are registered by a
predicate `Φ` the backend's creator fixes (decision O1: a saved predicate, `dlReg`; mvcc's is its
late-bound `delKey`), so the backend's specs need no new parameter.

D22's clean read, restore over a new backend and snapshot sender rely on an exact view: they hold
the registration unfixed (`dlInit`, the opener's), which rules out every deletable key
(`dlInit_noDel`), so that a thin view is exact for them (after review round 1, F6: the exclusive
token `dlNone` of decision O2, linked to nothing, was dropped).

Draft: the definitions the changed statements are written in. The registration's name is the
backend's (`BNames.dlg`, Draft round 2): the constructor allocates it at `False` and gives its whole
fraction to the creator (`dlInit`, in the constructor's post), who fixes the predicate once
(`dlReg_fix`) or keeps it unfixed for an exact view (`dlInit_noDel`). The invariants' use of `thinV` (`rtRest`, `batchGhostAt`,
`cacheValid`) is the stage's next Draft step.
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

/-- **The creator's part of a new backend's deletable keys** (Draft round 2): the registration's
whole fraction, at `False` (nothing deletable); in the constructor's post (`newPost`). -/
def dlInit (γ : BNames) : IProp GF :=
  savedPredOwn γ.dlg (DFrac.own 1) (fun _ : GoString × GoString => iprop(False))

/-- **The creator fixes the deletable keys once** (decision O1): the registration at `Φ`, read-only
from then on. -/
theorem dlReg_fix (γ : BNames) (Φ : GoString × GoString → IProp GF) :
    dlInit (GF := GF) γ ⊢ |==> dlReg γ Φ := by
  unfold dlInit
  iintro Hs
  imod saved_pred_update Φ γ.dlg _ $$ Hs with Hs
  imod saved_pred_persist γ.dlg _ Φ $$ Hs with Hs
  imodintro
  iunfold dlReg
  iexact Hs

/-- **An unfixed registration rules out every deletable key** (review round 1, F6(b)): its whole
fraction and a fixed registration's discarded one are not valid together. So a holder of `dlInit`
(D22's exact readers) knows every `thinV` exact. -/
theorem dlInit_noDel (γ : BNames) (nk : GoString × GoString) :
    dlInit (GF := GF) γ ∗ dlIs γ nk ⊢ False := by
  unfold dlInit dlIs dlReg
  iintro ⟨Hs, %Φ, Hr, -⟩
  ihave ⟨%Hv, -⟩ := saved_pred_valid_2 γ.dlg _ _ _ _ nk $$ Hs Hr
  exact absurd (DFrac.valid_own_op_discard.1 Hv) (by decide)

/-- **A registration fixed at `False` rules out every deletable key** (review round 2, Target 4; the
user's F6 decision): persistent, so D22's exact readers (the restore's new backend, a boot backend
with the compactor off: whoever fixed the registration at `False` with `dlReg_fix`) share it, and
concurrent readers too; the later is stripped by any step (`▷ False` inside a WP or an update). The
holder of the still unfixed `dlInit` has `dlInit_noDel`. -/
theorem dlReg_false_noDel (γ : BNames) (nk : GoString × GoString) :
    dlReg (GF := GF) γ (fun _ => iprop(False)) ∗ dlIs γ nk ⊢ ▷ False := by
  unfold dlIs dlReg
  iintro ⟨#Hf, %Φ, #Hr, #HΦ⟩
  ihave Heq := saved_pred_agree γ.dlg _ _ Φ (fun _ => iprop(False)) nk $$ Hr Hf
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨H1, -⟩
  iapply H1
  iexact HΦ

/-- **Every entry of the data `D` satisfies the value invariant `VI`** (3.3; Draft: `BParams.VI`'s
use; mvcc's instance, `metaVI`, makes the `Meta` bucket's compaction keys hold revisions, so that
`metaReadTx` is provable). -/
def viOk (VI : GoString → GoString → GoString → Prop) (D : Data) : Prop :=
  ∀ n k v, (bktOf D n).lookup k = some v → VI n k v

/-- **With nothing deletable, a thin view is exact** (the thin-view Draft round): under the
registration fixed at `False` (a backend that never compacts: the old bridge's, D22's restore over
a new backend), a physical view thin of `L` is `L` (`◇`: a missing key would give `▷ False`). -/
theorem thinV_exact (γ : BNames) (vd L : VData) :
    dlReg (GF := GF) γ (fun _ => iprop(False)) ∗ thinV γ vd L ⊢ ◇ ⌜vd = L⌝ := by
  iintro ⟨#Hf, Hth⟩
  iunfold thinV at Hth
  icases Hth with ⟨%Hsub, #Hdel⟩
  unfold BIBase.except0
  rcases Classical.em (∃ nk, L.lookup nk ≠ none ∧ vd.lookup nk = none) with ⟨nk, hnk⟩ | hno
  · ihave Hd := Hdel $$ %nk %hnk
    ihave Hfalse := dlReg_false_noDel γ nk $$ [$Hf $Hd]
    ileft
    iexact Hfalse
  · iright
    ipureintro
    apply GMap.ext
    intro nk
    cases hv : vd.lookup nk with
    | some v => exact (Hsub nk v hv).symm
    | none =>
      cases hL : L.lookup nk with
      | none => rfl
      | some w => exact absurd ⟨nk, by simp [hL], hv⟩ hno

/-- `thinV_exact` under a fancy update (which absorbs the `◇`): for a proof whose goal is a WP. -/
theorem thinV_exact_fupd (γ : BNames) (vd L : VData) (E : CoPset) :
    dlReg (GF := GF) γ (fun _ => iprop(False)) ∗ thinV γ vd L ⊢ |={E}=> ⌜vd = L⌝ := by
  iintro H
  iapply fupd_except0
  imodintro
  iapply thinV_exact γ vd L $$ H

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
