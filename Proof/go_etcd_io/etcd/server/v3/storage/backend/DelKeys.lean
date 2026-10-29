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

/-- **The deletable keys' registration** (persistent): the saved predicate `Φ` of
(bucket, key) pairs at the backend's name `γ.dlg`, fixed by the backend's creator. -/
def dlReg (γ : BNames) (Φ : GoString × GoString → IProp GF) : IProp GF :=
  savedPredOwn γ.dlg DFrac.discard Φ

instance dlReg_persistent (γ : BNames) (Φ : GoString × GoString → IProp GF) :
    Persistent (dlReg (GF := GF) γ Φ) := by
  unfold dlReg; infer_instance

/-- **The key `nk` (bucket, key) is deletable** (persistent): the registered predicate holds of it. -/
def dlIs (γ : BNames) (nk : GoString × GoString) : IProp GF :=
  iprop(∃ Φ : GoString × GoString → IProp GF, dlReg γ Φ ∗ □ Φ nk)

instance dlIs_persistent (γ : BNames) (nk : GoString × GoString) :
    Persistent (dlIs (GF := GF) γ nk) := by
  unfold dlIs; infer_instance

/-- **A physical view thin of the logical view `L`** (persistent): every entry of the physical
view `vd` is `L`'s, and an entry of `L` missing from `vd` is a deletable key. -/
def thinV (γ : BNames) (vd L : VData) : IProp GF :=
  iprop(⌜∀ nk v, vd.lookup nk = some v → L.lookup nk = some v⌝ ∗
    □ ∀ nk, ⌜L.lookup nk ≠ none ∧ vd.lookup nk = none⌝ -∗ dlIs γ nk)

instance thinV_persistent (γ : BNames) (vd L : VData) : Persistent (thinV (GF := GF) γ vd L) := by
  unfold thinV; infer_instance

/-- An exact view is thin. -/
theorem thinV_refl (γ : BNames) (vd : VData) : ⊢ thinV (GF := GF) γ vd vd := by
  iunfold thinV
  isplitr
  · ipureintro; intro nk v h; exact h
  · iintro !> %nk %h
    exact absurd h.2 h.1

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

/-- **A cached read buffer reads thin of the logical view** (3.2; Draft): `cacheValid` with
"exactly" weakened to "thin of `L`" (a tombstone put and compacted within one commit interval: a
reader of the cached buffer may still see the deleted key, which it never looks up). -/
def cacheValidC (γ : BNames) (P : BParams) (rv : RView) (idx : Nat) (L : VData) :
    IProp GF :=
  iprop(□ ∀ (i : Nat) (rv' : RView), ⌜i ≤ idx⌝ -∗ histAt γ rv.2.ver i rv' -∗
    cachedAt γ rv.2.ver i -∗ thinV γ (vData P (rv.1, rv'.2)) L)

/-- **Every entry of the data `D` satisfies the value invariant `VI`** (3.3; Draft: `BParams.VI`'s
use; mvcc's instance, `metaVI`, makes the `Meta` bucket's compaction keys hold revisions, so that
`metaReadTx` is provable). -/
def viOk (VI : GoString → GoString → GoString → Prop) (D : Data) : Prop :=
  ∀ n k v, (bktOf D n).lookup k = some v → VI n k v

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
