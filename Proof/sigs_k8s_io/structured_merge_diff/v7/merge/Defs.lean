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
over the typed operations; read as a whole: a field the manager applied last time and does not
apply now is removed, unless a manager's set (any manager's, this configuration's included) has it
(`addBackOwnedItems`), and nothing the manager did not apply last time is removed
(`addBackDanglingItems`). A list item is removed as a whole when its own path goes, even if another
manager owns a field inside it (SSA-03, kubernetes/kubernetes#134902), and a container emptied
on the way becomes `null` (SSA-01/02): faithful, not repaired.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

attribute [local instance] Classical.propDecidable

open PathSet

/-! ## The algorithm, abstractly -/

/-- Every manager's set reconciled with the schema (`reconcileManagedFieldsWithSchemaChanges`,
with an identity converter). -/
def reconcileMF (S : Schema) (t : TypeRef) (mf : MF) : MF :=
  fun m => (mf m).map fun e => { e with set := reconcile S t e.set }

/-- The union of every manager's set. -/
def mfUnion (mf : MF) : PathSet := fun q => ∃ m e, mf m = some e ∧ e.set q

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
    let p1 := removeItems S t merged ((fieldsOf merged).diff ((fieldsOf p0).union (ens (mfUnion mf))))
    -- put back what the manager did not apply last time (`addBackDanglingItems`)
    removeItems S t merged (((fieldsOf merged).diff (fieldsOf p1)).inter (ens L.set))

/-- The managers after `Updater.update` (forced, or without conflicts): every manager but `mgr`
loses its conflicting paths `confl` and the removed paths; a manager with no path left goes
(`mgr` too). -/
def afterUpdate (mf : MF) (mgr : GoString) (confl : GoString → PathSet) (removed : PathSet) : MF :=
  fun m => match mf m with
    | none => none
    | some e =>
      let s := if m = mgr then e.set else (e.set.diff (confl m)).diff removed
      if s.IsEmpty then none else some { e with set := s }

/-- Each other manager's paths that a change from `live` to `new` (`c`) modifies or adds. -/
def conflictsOf (mf : MF) (mgr : GoString) (c : Cmp) : GoString → PathSet := fun m =>
  if m = mgr then empty else
  match mf m with
  | some e => e.set.inter (c.modified.union c.added)
  | none => empty

/-- The outcome of `Updater.Apply`. -/
inductive ApplyOutcome where
  /-- The new object (`none`: unchanged, and the updater does not return the input on a no-op)
  and managers. -/
  | ok (obj : Option UVal) (mf : MF)
  /-- A conflict, not forced: each other manager's conflicting paths (empty for a manager with
  none). -/
  | conflicts (cs : GoString → PathSet)

/-- **`applyResult S t rion live config ver mf mgr force`**: what `Updater.Apply` computes (see
the file header); `rion`: the updater returns the input on a no-op (`ReturnInputOnNoop`). -/
def applyResult (S : Schema) (t : TypeRef) (rion : Bool) (live config : UVal) (ver : GoString)
    (mf : MF) (mgr : GoString) (force : Bool) : ApplyOutcome :=
  let mf0 := reconcileMF S t mf
  let merged := merge S t live config
  let mf1 : MF := fun m => if m = mgr then some ⟨fieldSet S t config, ver, true⟩ else mf0 m
  let new := prune S t merged mf1 (mf0 mgr)
  let c := compare S t live new
  let confl := conflictsOf mf1 mgr c
  if ¬ force ∧ ∃ m, ¬ (confl m).IsEmpty then .conflicts confl
  else .ok (if ¬ rion ∧ new = live then none else some new) (afterUpdate mf1 mgr confl c.removed)

/-- **`updateResult S t live new ver mf mgr`**: the managers after `Updater.Update` (the object
is `new` itself): every other manager loses what changed or was removed; `mgr` owns (not applied)
what it owned, less what was removed, plus what changed or was added. -/
def updateResult (S : Schema) (t : TypeRef) (live new : UVal) (ver : GoString) (mf : MF)
    (mgr : GoString) : MF :=
  let mf0 := reconcileMF S t mf
  let c := compare S t live new
  let mf2 := afterUpdate mf0 mgr (conflictsOf mf0 mgr c) c.removed
  let base := match mf2 mgr with
    | some e => e.set
    | none => empty
  let s := ((base.diff c.removed).union c.modified).union c.added
  fun m => if m = mgr then (if s.IsEmpty then none else some ⟨s, ver, false⟩) else mf2 m

/-- **A field set's list items and their key fields go together** (`Updater.Apply`'s premise on
the managed fields, `notes/smd-plan.md`, "Scope"): a set with a key field of an item has the item,
and a set with an item of a granular map type has its key fields. Every set SMD computes has it;
it rules out a pruned item that keeps its path but loses a key field (whose key SMD then cannot
compute: `Compare` fails). -/
def keysWithItems (S : Schema) (t : TypeRef) (s : PathSet) : Prop :=
  ∀ p fl, ((∃ n v, (n, v) ∈ fl ∧ s (p ++ [.key fl, .field n])) → s (p ++ [.key fl])) ∧
    (s (p ++ [.key fl]) →
      (∃ fs e rel, (typeAlong S (some t) (p ++ [.key fl])).bind (fun t => S.find t.name) =
        some (.map fs e rel) ∧ rel ≠ .atomic) →
      ∀ n v, (n, v) ∈ fl → s (p ++ [.key fl, .field n]))

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`isIdentityConverter cv`**: the `merge.Converter` `cv` is the identity on every version:
`Convert(obj, v)` returns `(obj, nil)` and `IsMissingVersionError(err)` returns `false` (Hoare
triples on its dynamic type's methods; persistent). -/
def isIdentityConverter (cv : merge.Converter) : IProp GF :=
  iprop(∃ (T : go.GoType) (v : val), ⌜cv = interface.mkOk T v⌝ ∗
    □ (∀ (p : Loc) (ver : fieldpath.APIVersion) (Φ : val → IProp GF),
        ▷ Φ (PairV #p #(interface.nil : GoInterface)) -∗
        WP (App (App (Val #(methods T go!"Convert" v)) (Val #p)) (Val #ver)) {{ Φ }}) ∗
    □ (∀ (e : GoInterface) (Φ : val → IProp GF), ▷ Φ #false -∗
        WP (App (Val #(methods T go!"IsMissingVersionError" v)) (Val #e)) {{ Φ }}))

/-- **`isUpdater u cv igf igfl rion`**: the `*merge.Updater` at `u` with converter `cv`, ignored
fields `igf`, ignore filter `igfl` and `ReturnInputOnNoop` `rion` (persistent: SMD never writes
it). -/
def isUpdater (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) : IProp GF :=
  iprop(u ↦□ (merge.Updater.mk cv igf igfl rion))

/-- A `merge.Conflicts` slice's conflicts. -/
def isConflictL : List merge.Conflict → List (GoString × Path) → IProp GF
  | [], [] => iprop(True)
  | x :: xs, (m, p) :: cs => iprop(⌜x.Manager' = m⌝ ∗ isPath x.Path' p ∗ isConflictL xs cs)
  | _, _ => iprop(False)

/-- **`isConflicts s cs`**: the `merge.Conflicts` slice `s` holds the conflicts `cs`, each a
manager and a path, in order (persistent). -/
def isConflicts (s : merge.Conflicts) (cs : List (GoString × Path)) : IProp GF :=
  iprop(∃ xs : List merge.Conflict, s ↦*{DFrac.discard} xs ∗ isConflictL xs cs)

end own

end smd
end EtcdGrove
end Perennial
