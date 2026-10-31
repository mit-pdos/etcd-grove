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

/-- **The creator's part of a new backend's deletable keys** (Draft round 2; with O1's fallback, the
flag `γ.dlb`): the registration's whole fraction, at `False`, and the flag's, at `false` (nothing
deletable); in the constructor's post (`newPost`). -/
def dlInit (γ : BNames) : IProp GF :=
  iprop(savedPredOwn γ.dlg (DFrac.own 1) (fun _ : GoString × GoString => iprop(False)) ∗
    dghostVar γ.dlb (DFrac.own 1) false)

/-- **The creator fixes the deletable keys once** (decision O1): the registration at `Φ`, the flag at
`true`, read-only from then on. -/
theorem dlReg_fix (γ : BNames) (Φ : GoString × GoString → IProp GF) :
    dlInit (GF := GF) γ ⊢ |==> dlReg γ Φ := by
  unfold dlInit
  iintro ⟨Hs, Hb⟩
  imod saved_pred_update Φ γ.dlg _ $$ Hs with Hs
  imod saved_pred_persist γ.dlg _ Φ $$ Hs with Hs
  imod dghostVar_update true γ.dlb false $$ Hb with Hb
  imod dghostVar_persist γ.dlb 1 true $$ Hb with Hb
  imodintro
  iunfold dlReg
  iframe Hs Hb

/-- **The creator fixes nothing deletable** (O1's fallback, decided by the agent while the user was
away, 2026-10-29): the flag at `false`, persistent (`dlNoDel`), for a backend whose creator registered nothing as deletable (not `mvcc.bkNoCmp`, a fact about
the backend's data at opening: no compaction keys in `meta`). -/
theorem dlNoDel_fix (γ : BNames) : dlInit (GF := GF) γ ⊢ |==> dlNoDel γ := by
  unfold dlInit
  iintro ⟨-, Hb⟩
  imod dghostVar_persist γ.dlb 1 false $$ Hb with Hb
  imodintro
  iunfold dlNoDel
  iexact Hb

/-- **An unfixed registration rules out every deletable key** (review round 1, F6(b)): its flag's
whole fraction at `false` disagrees with a registration's `true`. -/
theorem dlInit_noDel (γ : BNames) (nk : GoString × GoString) :
    dlInit (GF := GF) γ ∗ dlIs γ nk ⊢ False := by
  unfold dlInit dlIs dlReg
  iintro ⟨⟨-, Hb⟩, %Φ, ⟨-, Hr⟩, -⟩
  ihave %Heq := dghostVar_agree γ.dlb false _ true _ $$ Hb Hr
  exact absurd Heq (by decide)

/-- **Nothing deletable rules out every deletable key, with no later** (O1's fallback): the flag at
`false` disagrees with a registration's `true`. Persistent, so D22's exact readers and concurrent
readers share it. -/
theorem dlNoDel_noDel (γ : BNames) (nk : GoString × GoString) :
    dlNoDel (GF := GF) γ ∗ dlIs γ nk ⊢ False := by
  unfold dlNoDel dlIs dlReg
  iintro ⟨Hb, %Φ, ⟨-, Hr⟩, -⟩
  ihave %Heq := dghostVar_agree γ.dlb false _ true _ $$ Hb Hr
  exact absurd Heq (by decide)

/-- **With nothing deletable, a thin view is exact** (the thin-view Draft round; O1's fallback: no
later): under `dlNoDel` (a backend whose creator registered nothing as deletable: the old bridge's, D22's restore over a new
backend), a physical view thin of `L` is `L`. -/
theorem thinV_exact (γ : BNames) (vd L : VData) :
    dlNoDel (GF := GF) γ ∗ thinV γ vd L ⊢ ⌜vd = L⌝ := by
  iintro ⟨#Hf, Hth⟩
  iunfold thinV at Hth
  icases Hth with ⟨%Hsub, #Hdel⟩
  rcases Classical.em (∃ nk, L.lookup nk ≠ none ∧ vd.lookup nk = none) with ⟨nk, hnk⟩ | hno
  · ihave Hd := Hdel $$ %nk %hnk
    iexfalso
    iapply dlNoDel_noDel γ nk $$ [$Hf $Hd]
  · ipureintro
    apply GMap.ext
    intro nk
    cases hv : vd.lookup nk with
    | some v => exact (Hsub nk v hv).symm
    | none =>
      cases hL : L.lookup nk with
      | none => rfl
      | some w => exact absurd ⟨nk, by simp [hL], hv⟩ hno

/-- **With the registration not yet fixed, a thin view is exact** (M2's restore chain, item 30's
D1, 2026-10-30): as `thinV_exact`, from the creator's unfixed registration (`dlInit`, kept), for a
backend nothing has been made deletable on yet (the new backend `kv.Restore` reads before the store
fixes its registration). -/
theorem thinV_exact_init (γ : BNames) (vd L : VData) :
    dlInit (GF := GF) γ ∗ thinV γ vd L ⊢ dlInit γ ∗ ⌜vd = L⌝ := by
  iintro ⟨Hi, Hth⟩
  iunfold thinV at Hth
  icases Hth with ⟨%Hsub, #Hdel⟩
  rcases Classical.em (∃ nk, L.lookup nk ≠ none ∧ vd.lookup nk = none) with ⟨nk, hnk⟩ | hno
  · ihave Hd := Hdel $$ %nk %hnk
    iexfalso
    iapply dlInit_noDel γ nk $$ [$Hi $Hd]
  · iframe Hi
    ipureintro
    apply GMap.ext
    intro nk
    cases hv : vd.lookup nk with
    | some v => exact (Hsub nk v hv).symm
    | none =>
      cases hL : L.lookup nk with
      | none => rfl
      | some w => exact absurd ⟨nk, by simp [hL], hv⟩ hno

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
