/-
**The laws of `merge`'s internal vocabulary** (`merge/Defs.lean`: the stages `addBackOwned`,
`addBackOwnedMF`, `addBackDangling`, `conflictsMF`, `mfPairs`; the owned managed fields `ownMF`)
that make `Updater.Apply` and `Updater.Update` glue over their stages' specs, and `prune`'s and
`update`'s proofs glue over theirs. Stated, not proved (`def <name>.law : Prop`, as `v7/Laws.lean`):
the next phase's invariant work.

How the stages compose (`notes/smd-plan.md`, "The call DAG", `merge`):
- `Apply`: `reconcileManagedFieldsWithSchemaChanges` gives `ownMF m (reconcileMF S t mf)` (`mf0`);
  `TypedValue.Merge` gives `merged`; `managers[manager]` read gives `isVSetOpt ls (mf0.get mgr)`;
  the write of the applier's new entry gives `ownMF m (mf0.set mgr ⟨fieldSet S t config, ver,
  true⟩)` (`mf1`; a map write, unfolding `ownMF`); `prune` gives `prune S t merged mf1 (mf0.get mgr)` (its premises
  from `Apply`'s one-version premise, `reconcileMF_get`, `MF.get_set`); `update` gives the
  conflicts or `afterUpdate mf1 mgr (conflictsOf mf1 mgr c) c.removed`: `applyResult` line by line.
- `Update`: `mf0`, then `update` forced, then the manager's own entry (`MF.get_set`, a map write
  and a delete): `updateResult` line by line.
- `prune`: `prune_stages`; `update`'s conflicts: `mfPairs_conflictsMF`, `conflictsMF_nil_iff`.

Draft (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Owned managed fields -/

/-- A finished map of managed fields is handed out persistently (`Apply`'s and `Update`'s
result). -/
def ownMF_persist.law : Prop := ∀ m mf, ownMF (GF := GF) m mf ⊢ |==> isMF m mf

/-- `fieldpath.ManagedFields{}`: an owned empty map. -/
def ownMF_empty.law : Prop :=
  ∀ m, m ↦$ (∅ : GMap GoString GoInterface) ⊢ ownMF (GF := GF) m MF.none

-- The map operations on an owned map (`managers[m]`, `managers[m] = i`, `delete(managers, m)`)
-- are proved inside `merge`'s own proofs by unfolding `ownMF` (`import all`), over
-- `MF.get_set`, `MF.set_sorted` and Perennial's map rules: no law.

end laws

/-! ## Pure laws -/

/-- **`prune` is its three passes** (`Updater.prune` over `addBackOwnedItems` and
`addBackDanglingItems`): with a non-empty last set and at least one manager. -/
def prune_stages.law : Prop :=
  ∀ S t merged (mf : MF) (L : VSet), ¬ L.set.IsEmpty → mf ≠ [] →
    prune S t merged mf (some L) =
      addBackDangling S t merged
        (addBackOwnedMF S t merged (removeItems S t merged (ensureNamed S t L.set)) mf) L.set

/-- The pairs of the conflicts map `update` builds are its conflicts. -/
def mfPairs_conflictsMF.law : Prop :=
  ∀ mf mgr c, mfPairs (conflictsMF mf mgr c) = conflictsOf mf mgr c

/-- `len(conflicts) != 0` decides whether there is a conflict. -/
def conflictsMF_nil_iff.law : Prop :=
  ∀ mf mgr c, conflictsMF mf mgr c = [] ↔ (conflictsOf mf mgr c).isEmpty = true

/-- The conflicts map is sorted when the managers are (its `isMF`). -/
def conflictsMF_sorted.law : Prop :=
  ∀ mf mgr c, keysSorted mf = true → keysSorted (conflictsMF mf mgr c) = true

/-- Reconciling keeps every manager's version and applied flag. -/
def reconcileMF_get.law : Prop :=
  ∀ S t mf m, (reconcileMF S t mf).get m =
    (mf.get m).map (fun e => { e with set := reconcile S t e.set })

/-- Reconciling keeps the managers sorted. -/
def reconcileMF_sorted.law : Prop :=
  ∀ S t mf, keysSorted mf = true → keysSorted (reconcileMF S t mf) = true

/-- `MF.set` writes one manager's entry. -/
def MF.get_set.law : Prop :=
  ∀ (mf : MF) k e m, (mf.set k e).get m = if m = k then some e else mf.get m

/-- `MF.set` keeps the managers sorted. -/
def MF.set_sorted.law : Prop :=
  ∀ (mf : MF) k e, keysSorted mf = true → keysSorted (mf.set k e) = true

/-- `afterUpdate` keeps the managers sorted. -/
def afterUpdate_sorted.law : Prop :=
  ∀ mf mgr confl removed, keysSorted mf = true →
    keysSorted (afterUpdate mf mgr confl removed) = true

end smd
end EtcdGrove
end Perennial
