/-
**Server-side apply and update, abstractly** (`merge` package, v7.0.0): the vocabulary of the
specs of `Updater.Apply` and `Updater.Update` (`notes/smd-plan.md`, "The vocabulary").

`applyResult` and `updateResult` are what SSA computes, written in the `typed` vocabulary
(`typed/Defs.lean`), for an updater in the scope (one API version, an identity converter, no
ignored fields): the managed fields reconciled with the schema (`reconcileMF`), the configuration
merged into the live object, the applying manager's fields replaced by the configuration's, the
merged object pruned (`prune`) of what the manager applied last time and no longer applies unless
another manager owns it, and the other managers' ownership updated by the comparison of the live
object with the new one: a manager loses what changed (a conflict unless forced) and what was
removed.

`prune` states SMD's three passes (`Updater.prune`, `addBackOwnedItems`, `addBackDanglingItems`)
over the typed operations. **It has no simpler reading**: the documented one ("a field the
manager applied last time and does not apply now is removed, unless a manager's set has it, and
nothing else is removed") is false of SMD, even on managed fields SMD computed itself (review
round 1, finding 3; Go-reproduced, `issues/smd-apply-deletes-own-struct.md`):
- A applied `{spec: {}}`, so A owns `{.spec}`; the live object is `{name: o, spec: {a: "a",
  l: []}}` (`spec.a` unowned, as a field the API server defaulted; `l: []` has no field path).
  A applies `{spec: {}}` again: SMD returns `{name: o}`. The field A applies now is deleted: the
  second pass drops the unowned `a`, and the third sees no field path left under `spec` (`l: []`
  contributes none) and removes `spec` as dangling. Without `l: []` the apply is a no-op.
- A list item is removed as a whole when its own path goes, even if another manager owns a field
  inside it (SSA-03, kubernetes/kubernetes#134902).
- A container emptied on the way becomes `null` (SSA-01/02).
All faithful, not repaired. (A path below an item's key field, the third known exception, is
excluded by `Apply`'s premise `keysWithItems`.)

The pure definitions are computable (review round 1, P1): `decide` evaluates `applyResult` and
`updateResult` on literals.

The internal specs of `merge` (`Updater.update`, `prune`, `addBackOwnedItems`,
`addBackOwnedItemsForVersion`, `addBackDanglingItems`, `reconcileManagedFieldsWithSchemaChanges`,
`ConflictsFromManagers`, `Conflict.Equals`) are stated over the stages of `applyResult`:
`addBackOwned`/`addBackOwnedMF`/`addBackDangling` (`prune`'s second and third passes:
`prune_stages`), `conflictsMF` and `mfPairs` (the conflicts `update` collects: `mfPairs_conflictsMF`),
and the owned managed fields `ownMF` that `Apply`/`Update` thread between them (laws in
`merge/Laws.lean`).

Lean-first (2026-11-19, notes/smd-plan.md); the stages added with `merge`'s per-function specs
(Draft, 2026-11-19).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

open PathSet

/-! ## The algorithm, abstractly -/

/-- Every manager's set reconciled with the schema (`reconcileManagedFieldsWithSchemaChanges`,
with an identity converter). -/
def reconcileMF (S : Schema) (t : TypeRef) (mf : MF) : MF :=
  mf.map fun (m, e) => (m, { e with set := reconcile S t e.set })

/-- The union of every manager's set. -/
def mfUnion (mf : MF) : PathSet := mf.foldr (fun me acc => PathSet.union me.2.set acc) PathSet.empty

/-- **`prune S t merged mf last`**: the merged object pruned for the applying manager, whose
previous entry is `last` and whose new one is in `mf` (`Updater.prune`; see the file header). -/
def prune (S : Schema) (t : TypeRef) (merged : UVal) (mf : MF) (last : Option VSet) : UVal :=
  match last with
  | none => merged
  | some L =>
    if L.set.IsEmpty then merged else
    let ens := ensureNamed S t
    let fieldsOf := fun v => ens (fieldSet S t v)
    -- remove what the manager applied last time
    let p0 := removeItems S t merged (ens L.set)
    -- put back what a manager owns (`addBackOwnedItems`)
    let p1 := removeItems S t merged
      ((fieldsOf merged).diff ((fieldsOf p0).union (ens (mfUnion mf))))
    -- put back what the manager did not apply last time (`addBackDanglingItems`)
    removeItems S t merged (((fieldsOf merged).diff (fieldsOf p1)).inter (ens L.set))

/-- Manager `m`'s paths in a set of (manager, path) pairs. -/
def conflictsOfMgr (cs : FSet (GoString × Path)) (m : GoString) : PathSet :=
  cs.bind (fun mp => if mp.1 = m then [mp.2] else [])

/-- The managers after `Updater.update` (forced, or without conflicts): every manager but `mgr`
loses its conflicting paths (`confl`'s pairs for it) and the removed paths; a manager with no path
left goes (`mgr` too). -/
def afterUpdate (mf : MF) (mgr : GoString) (confl : FSet (GoString × Path)) (removed : PathSet) :
    MF :=
  mf.filterMap fun (m, e) =>
    let s := if m = mgr then e.set else (e.set.diff (conflictsOfMgr confl m)).diff removed
    if s.IsEmpty then none else some (m, { e with set := s })

/-- Each other manager's paths that a change from `live` to `new` (`c`) modifies or adds, as
(manager, path) pairs. -/
def conflictsOf (mf : MF) (mgr : GoString) (c : Cmp) : FSet (GoString × Path) :=
  mf.foldr (fun me acc =>
    if me.1 = mgr then acc
    else FSet.union ((me.2.set.inter (c.modified.union c.added)).map (fun p => (me.1, p))) acc)
    FSet.empty

/-! ## The stages, for the internal specs (`Updater.prune`'s passes, `Updater.update`'s maps) -/

/-- **`addBackOwned S t merged pruned managed`**: `addBackOwnedItemsForVersion`'s result: the merged
object less what it has and neither the pruned object nor the managed set has (each closed by
`ensureNamed`): the second pass of `prune`. -/
def addBackOwned (S : Schema) (t : TypeRef) (merged pruned : UVal) (managed : PathSet) : UVal :=
  removeItems S t merged
    ((ensureNamed S t (fieldSet S t merged)).diff
      ((ensureNamed S t (fieldSet S t pruned)).union (ensureNamed S t managed)))

/-- `addBackOwnedItems` with every manager at the pruned version: one pass over the union of the
managers' sets; no manager, no pass (the pruned object itself). -/
def addBackOwnedMF (S : Schema) (t : TypeRef) (merged pruned : UVal) (mf : MF) : UVal :=
  match mf with
  | [] => pruned
  | _ :: _ => addBackOwned S t merged pruned (mfUnion mf)

/-- **`addBackDangling S t merged pruned last`**: `addBackDanglingItems`'s result: the merged
object less what the pruned object lost of the manager's last applied set `last` (each closed by
`ensureNamed`): the third pass of `prune`. -/
def addBackDangling (S : Schema) (t : TypeRef) (merged pruned : UVal) (last : PathSet) : UVal :=
  removeItems S t merged
    (((ensureNamed S t (fieldSet S t merged)).diff (ensureNamed S t (fieldSet S t pruned))).inter
      (ensureNamed S t last))

/-- The `conflicts` map `Updater.update` builds: each manager but `mgr` with a non-empty
intersection of its set with what the change modifies or adds, at its version, not applied. -/
def conflictsMF (mf : MF) (mgr : GoString) (c : Cmp) : MF :=
  mf.filterMap fun (m, e) =>
    if m = mgr then none else
    let s := e.set.inter (c.modified.union c.added)
    if s.IsEmpty then none else some (m, ⟨s, e.version, false⟩)

/-- Every (manager, path) pair of managed fields (`ConflictsFromManagers`' conflicts). -/
def mfPairs (mf : MF) : FSet (GoString × Path) :=
  mf.foldr (fun me acc => FSet.union (me.2.set.map (fun p => (me.1, p))) acc) FSet.empty

/-- The outcome of `Updater.Apply`. -/
inductive ApplyOutcome where
  /-- The new object (`none`: unchanged, and the updater does not return the input on a no-op)
  and managers. -/
  | ok (obj : Option UVal) (mf : MF)
  /-- A conflict, not forced: the other managers' conflicting (manager, path) pairs. -/
  | conflicts (cs : FSet (GoString × Path))

/-- Equality of outcomes, decided (by hand: see `VSet`'s instance). -/
instance : DecidableEq ApplyOutcome
  | .ok o m, .ok o' m' => decidable_of_iff (o = o' ∧ m = m') (by simp only [ApplyOutcome.ok.injEq])
  | .conflicts c, .conflicts c' => decidable_of_iff (c = c') (by simp only [ApplyOutcome.conflicts.injEq])
  | .ok _ _, .conflicts _ => isFalse (fun h => by cases h)
  | .conflicts _, .ok _ _ => isFalse (fun h => by cases h)

/-- **`applyResult S t rion live config ver mf mgr force`**: what `Updater.Apply` computes (see
the file header); `rion`: the updater returns the input on a no-op (`ReturnInputOnNoop`). -/
def applyResult (S : Schema) (t : TypeRef) (rion : Bool) (live config : UVal) (ver : GoString)
    (mf : MF) (mgr : GoString) (force : Bool) : ApplyOutcome :=
  let mf0 := reconcileMF S t mf
  let merged := merge S t live config
  let mf1 : MF := mf0.set mgr ⟨fieldSet S t config, ver, true⟩
  let new := prune S t merged mf1 (mf0.get mgr)
  let c := compare S t live new
  let confl := conflictsOf mf1 mgr c
  if !force && !confl.isEmpty then .conflicts confl
  else .ok (if !rion && decide (new = live) then none else some new)
    (afterUpdate mf1 mgr confl c.removed)

/-- **`updateResult S t live new ver mf mgr`**: the managers after `Updater.Update` (the object
is `new` itself): every other manager loses what changed or was removed; `mgr` owns (not applied)
what it owned, less what was removed, plus what changed or was added. -/
def updateResult (S : Schema) (t : TypeRef) (live new : UVal) (ver : GoString) (mf : MF)
    (mgr : GoString) : MF :=
  let mf0 := reconcileMF S t mf
  let c := compare S t live new
  let mf2 := afterUpdate mf0 mgr (conflictsOf mf0 mgr c) c.removed
  let base := match mf2.get mgr with
    | some e => e.set
    | none => PathSet.empty
  let s := ((base.diff c.removed).union c.modified).union c.added
  if s.IsEmpty then mf2.filter (fun me => me.1 != mgr) else mf2.set mgr ⟨s, ver, false⟩

/-- **A field set's list items and their key fields go together, and nothing is below a key
field** (`Updater.Apply`'s premise on the managed fields, `notes/smd-plan.md`, "Scope"), for every
associative-list item path `p ++ [.key fl]`:
1. a set with a key field of the item (`p ++ [.key fl, .field n]`, `n` a key field) has the item;
2. a set with the item, of a granular map type, has its key fields;
3. no path of the set extends a key field's path (`p ++ [.key fl, .field n] ++ r`, `r ≠ []`).
Every set SMD computes has it (`fieldSet` and `compare` never produce a path below a scalar, and
`afterUpdate` only removes paths), and `Apply` and `Update` keep it (`applyResult_premise`,
`updateResult_premise`). Without (1) or (3) SMD's pruning (`ensureNamed` makes the key field a
member when a path below it is; the third pass then removes the key field from an item it keeps)
can leave an item without its key: `Apply` then fails with an error that is not a conflict, or
leaves two items with one key and reports (or, forced, applies) a spurious conflict (review round
1, finding 1; `nonissues/smd-apply-keyless-item-compare-error.md`). The weaker form "(1) for paths
at or below a key field" is not kept by `Update` and is not used. Decided by `keysWithItemsB`
(`keysWithItemsB_iff`). -/
def keysWithItems (S : Schema) (t : TypeRef) (s : PathSet) : Prop :=
  ∀ p fl, ((∃ n v, (n, v) ∈ fl ∧ (p ++ [.key fl, .field n]) ∈ s) → (p ++ [.key fl]) ∈ s) ∧
    ((p ++ [.key fl]) ∈ s →
      (∃ fs e rel, (typeAlong S (some t) (p ++ [.key fl])).bind (fun t => S.find t.name) =
        some (.map fs e rel) ∧ rel ≠ .atomic) →
      ∀ n v, (n, v) ∈ fl → (p ++ [.key fl, .field n]) ∈ s) ∧
    (∀ n v r, (n, v) ∈ fl → r ≠ [] → (p ++ [.key fl, .field n] ++ r) ∉ s)

/-- `keysWithItems` at the paths of `s` below `acc` (`acc ++ q ∈ s`), computed. -/
def kwiAt (S : Schema) (t : TypeRef) (s : PathSet) : Path → Path → Bool
  | _, [] => true
  | acc, pe :: rest =>
    (match pe with
      | .key fl =>
        let it := acc ++ [pe]
        match rest with
        | [] =>
          match (typeAlong S (some t) it).bind (fun t => S.find t.name) with
          | some (.map _ _ rel) =>
            decide (rel = .atomic) || fl.all (fun nv => decide ((it ++ [.field nv.1]) ∈ s))
          | _ => true
        | .field n :: r =>
          if fl.any (fun nv => decide (nv.1 = n)) then decide (it ∈ s) && r.isEmpty else true
        | _ => true
      | _ => true) && kwiAt S t s (acc ++ [pe]) rest

/-- **`keysWithItems`, decided**: every path of `s` passes `kwiAt` (`keysWithItemsB_iff`). -/
def keysWithItemsB (S : Schema) (t : TypeRef) (s : PathSet) : Bool := s.all (kwiAt S t s [])

/-- **D9's workload premise** of `Updater.Apply` and `Updater.Update` (`notes/smd-plan.md`, D9),
stated once: the objects' sizes together, and the trie nodes of the managers' sets together, below
`smdSizeMax` (`value/Defs.lean`). Every internal count (`Set.Insert`'s and `slices.Insert`'s
lengths, `make`'s capacities, the typed API's size premises) follows from it by laws
(`merge/Laws.lean`, `inputsSmall_*`). Decided (`decide` on the driver's literals). -/
def inputsSmall (xs : List UVal) (mf : MF) : Prop :=
  (xs.map UVal.size).sum < smdSizeMax ∧ (mfUnion mf).nodes.card < smdSizeMax

instance (xs : List UVal) (mf : MF) : Decidable (inputsSmall xs mf) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`isIdentityConverter cv`**: the `merge.Converter` `cv` is the identity on every version:
`Convert(obj, v)` returns `(obj, nil)` and `IsMissingVersionError(err)` returns `false` (Hoare
triples on its dynamic type's methods; persistent). -/
@[no_expose] def isIdentityConverter (cv : merge.Converter) : IProp GF :=
  iprop(∃ (T : go.GoType) (v : val), ⌜cv = interface.mkOk T v⌝ ∗
    □ (∀ (p : Loc) (ver : fieldpath.APIVersion) (Φ : val → IProp GF),
        ▷ Φ (PairV #p #(interface.nil : GoInterface)) -∗
        WP (App (App (Val #(methods T go!"Convert" v)) (Val #p)) (Val #ver)) {{ Φ }}) ∗
    □ (∀ (e : GoInterface) (Φ : val → IProp GF), ▷ Φ #false -∗
        WP (App (Val #(methods T go!"IsMissingVersionError" v)) (Val #e)) {{ Φ }}))

/-- **`isUpdater u cv igf igfl rion`**: the `*merge.Updater` at `u` with converter `cv`, ignored
fields `igf`, ignore filter `igfl` and `ReturnInputOnNoop` `rion` (persistent: SMD never writes
it). Built by `BuildUpdater`, or a client's literal (`isUpdater_intro`: Kubernetes builds
`merge.Updater{...}` directly). -/
@[no_expose] def isUpdater (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) : IProp GF :=
  iprop(u ↦□ (merge.Updater.mk cv igf igfl rion))

/-- A `merge.Conflicts` slice's conflicts (internal). -/
@[no_expose] def isConflictL : List merge.Conflict → List (GoString × Path) → IProp GF
  | [], [] => iprop(True)
  | x :: xs, (m, p) :: cs => iprop(⌜x.Manager' = m⌝ ∗ isPath x.Path' p ∗ isConflictL xs cs)
  | _, _ => iprop(False)

/-- **`isConflicts s cs`**: the `merge.Conflicts` slice `s` holds the conflicts `cs`, each a
manager and a path, in order (persistent). -/
@[no_expose] def isConflicts (s : merge.Conflicts) (cs : List (GoString × Path)) : IProp GF :=
  iprop(∃ xs : List merge.Conflict, s ↦*{DFrac.discard} xs ∗ isConflictL xs cs)

/-- **`isVSetOpt i o`**: a manager's entry read from a `ManagedFields` map: the nil interface
(no entry) for `none`, else an `isVSet` (persistent). -/
@[no_expose] def isVSetOpt (i : fieldpath.VersionedSet) : Option VSet → IProp GF
  | none => iprop(⌜i = interface.nil⌝)
  | some e => isVSet i e

/-- **`isConflict x c`**: the `merge.Conflict` `x` is the conflict `c`, a manager and a path
(persistent). -/
@[no_expose] def isConflict (x : merge.Conflict) (c : GoString × Path) : IProp GF :=
  iprop(⌜x.Manager' = c.1⌝ ∗ isPath x.Path' c.2)

end own

end smd
end EtcdGrove
end Perennial
