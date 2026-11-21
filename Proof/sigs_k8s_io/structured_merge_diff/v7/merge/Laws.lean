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
  true⟩)` (`mf1`; a map write, `ownMF_access`); `prune` gives `prune S t merged mf1 (mf0.get mgr)` (its premises
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

/-! ## Owned managed fields: `ownMF` is `fieldpath`'s (`fieldpath/Defs.lean`, beside `isMF`); its
laws (`ownMF_persist`, `ownMF_empty`, `ownMF_access`: the map operations `managers[m]`,
`managers[m] = i`, `delete(managers, m)` over Perennial's map rules) are `fieldpath/Vocab.lean`'s. -/

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


/-! ## The workload premise (D9) and `RemoveItems`' conformance (D10 (b)), the Draft's integration
(2026-11-19): what the stages' premises follow from -/

/-- Merging adds no node beyond the two sides' (conforming sides of a schema in scope: without
conformance an associative list repeating a key merges that key's item more than once; premises
added in Prove, 2026-11-21, no user yet). -/
def merge_size.law : Prop :=
  ∀ S t l r, S.WF → conforms S t l → conforms S t r → (merge S t l r).size ≤ l.size + r.size
/-- Removing paths adds no node. -/
def removeItems_size.law : Prop :=
  ∀ S t x R, (removeItems S t x R).size ≤ x.size
/-- Pruning adds no node (its three passes remove from `merged`). -/
def prune_size.law : Prop :=
  ∀ S t merged (mf : MF) last, (prune S t merged mf last).size ≤ merged.size
/-- `ensureNamed` adds only prefixes of the set's paths: its count is bounded by the trie's nodes. -/
def ensureNamed_nodes.law : Prop :=
  ∀ S t (s : PathSet) q, q ∈ ensureNamed S t s → q ∈ s.nodes
/-- A field set's trie nodes are nodes of the value. -/
def fieldSet_nodes.law : Prop :=
  ∀ S t x, (fieldSet S t x).nodes.card ≤ x.size
/-- A manager's set is part of the union (each set's nodes count no more than the union's). -/
def mfUnion_nodes.law : Prop :=
  ∀ (mf : MF) m e, mf.get m = some e → e.set.nodes.card ≤ (mfUnion mf).nodes.card
/-- `Apply`'s workload premise gives `prune`'s and `update`'s size premises (with
`merge_size`, `prune_size`, `reconcileMF` and `MF.set` keeping the union's nodes below the bound
together with the applier's new field set: `fieldSet_nodes`). Restated 2026-11-21 with
`inputsSmall`'s combined bound (the union below `smdSizeMax`, as `prune` needs) and `merge_size`'s
premises (no user). -/
def inputsSmall_prune.law : Prop :=
  ∀ S t (live config : UVal) (mf : MF) mgr (e : VSet), S.WF → conforms S t live →
    conforms S t config → inputsSmall [live, config] mf →
    e.set = fieldSet S t config →
    (merge S t live config).size < smdSizeMax ∧
    (mfUnion ((reconcileMF S t mf).set mgr e)).nodes.card < smdSizeMax

/-- **`prune`'s passes keep the object conforming** (D10 (b): `RemoveItems`' premise), from
`keysWithItems` of the managers' and the last sets (`Apply`'s premise; round 1's finding 1 is the
counterexample without it). -/
def prune_conforms.law : Prop :=
  ∀ S t merged (mf : MF) (L : VSet), S.WF → conforms S t merged →
    (∀ m e, mf.get m = some e → keysWithItems S t e.set) → keysWithItems S t L.set →
    let p0 := removeItems S t merged (ensureNamed S t L.set)
    let p1 := addBackOwnedMF S t merged p0 mf
    conforms S t p0 ∧ conforms S t p1 ∧ conforms S t (addBackDangling S t merged p1 L.set)

end smd
end EtcdGrove
end Perennial
