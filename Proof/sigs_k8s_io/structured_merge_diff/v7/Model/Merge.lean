/-
The pure model of SMD's **updater** (`merge` package): `Updater.update`, `Update`,
`Apply`, `prune`, `addBackOwnedItems(ForVersion)`, `addBackDanglingItems`,
`reconcileManagedFieldsWithSchemaChanges`, `ConflictsFromManagers`, `Conflicts.Equals`.

**The model as a whole** (`Model/{Value,Schema,Fieldpath,Typed,Merge}.lean`): pure values and a
pure function per Go function of the `Apply`/`Update` call graph (notes/smd-goose.md's table),
transcribing the Go algorithm so that each Go function's proof is a refinement step; every
function is structurally recursive (with fuel where Go loops over two lists or down a value), so
that the model runs in the kernel (`decide +kernel` on the driver's scenario:
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/smd/Scenario.lean`). Where it is unfaithful
or restricted (each restriction is a premise of the specs, notes/smd-robustness.md):

* the updater: `IgnoreFilter` and `IgnoredFields` nil, a converter that is the identity
  (`Convert` returns its argument, `IsMissingVersionError` is false), every managed field set at
  the request's API version: `update` then compares once, `addBackOwnedItems` adds back one union;
* values are unstructured without floats (`UVal`); schemas have no element-relationship
  overrides, unions or defaults (`Schema`);
* Go map iteration is in key order. It is observable only in the order of the managers in
  `ConflictsFromManagers`: `conflictsOf` takes them in the order given, and `Apply`'s spec allows
  any order;
* errors: which error (its message) is not modelled, only that there is one (and `Conflicts`);
* panics: `Res.panic`/`ApplyRes.panic` where Go panics (on a nil `value.Value`: `merge` returns
  one when its walker's output is nil; `RemoveItems` and `value.Equals` then panic, and
  `ToFieldSet` of a list type). The specs take "the model does not panic" as a premise.

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Model.Typed

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace smd

/-! ## merge -/

/-- The result of a model function that may fail with an error or panic. -/
inductive Res (α : Type) where
  | ok (a : α)
  | error
  | panic
  deriving Inhabited

namespace Res
def bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok a, f => f a
  | .error, _ => .error
  | .panic, _ => .panic
instance : Monad Res where
  pure := .ok
  bind := bind
end Res

def ofOpt {α : Type} : Option α → Res α | some a => .ok a | none => .error
def ofPanicOpt {α : Type} : Option α → Res α | some a => .ok a | none => .panic

/-- `Updater.reconcileManagedFieldsWithSchemaChanges` (the identity converter). -/
def reconcileMF (sc : Schema) (live : TV) (mf : MF) : Res MF :=
  mf.foldlM (fun acc (m, vs) => do
    let r ← ofOpt (reconcileFieldSet sc vs.set live.typeRef)
    pure (insertKV m (match r with | some s => ⟨s, vs.version, vs.applied⟩ | none => vs) acc)) []

/-- The outcome of `Updater.update`: the managers and the comparison, or the conflicts (the
conflicting managers, each with its conflicting set). -/
inductive UpdRes where
  | ok (mf : MF) (c : Comparison)
  | conflicts (cs : MF)
  | error
  | panic

/-- `Updater.update` (the identity converter: every manager's comparison is `compare`). -/
def update (sc : Schema) (live new : TV) (mf : MF) (workflow : GoString) (force : Bool) : UpdRes :=
  match tvCompare sc live new with
  | none => .error
  | some c =>
    let (conflicts, removed) := mf.foldl (fun (cs, rs) (m, vs) =>
      if m = workflow then (cs, rs) else
      let cset := vs.set.inter (c.modified.union c.added)
      let cs := if !cset.isEmpty then insertKV m ⟨cset, vs.version, false⟩ cs else cs
      let rs := if !c.removed.isEmpty then insertKV m ⟨c.removed, vs.version, false⟩ rs else rs
      (cs, rs)) (([] : MF), ([] : MF))
    if !force && !conflicts.isEmpty then .conflicts conflicts else
    let sub (mf : MF) (xs : MF) : MF := xs.foldl (fun mf (m, x) =>
      let cur := (lookupKV m mf).getD default
      insertKV m ⟨cur.set.diff x.set, cur.version, cur.applied⟩ mf) mf
    let mf := sub (sub mf conflicts) removed
    .ok (mf.filter (fun (_, vs) => !vs.set.isEmpty)) c

/-- `Updater.prune` (the identity converter). -/
def prune (sc : Schema) (merged : TV) (mf : MF) (manager : GoString) (lastSet : Option VSet) : Res TV := do
  match lastSet with
  | none => pure merged
  | some last =>
    if last.set.isEmpty then pure merged else
    let tr := merged.typeRef
    let pruned ← ofPanicOpt (tvRemoveItems sc merged (last.set.ensureNamed sc tr))
    -- `addBackOwnedItems`: the union of every manager's set (one version)
    let managed := mf.foldl (fun s (_, vs) => s.union vs.set) PSet.empty
    let pruned ← (if mf.isEmpty then pure pruned else do
      -- `addBackOwnedItemsForVersion`
      let mergedSet ← (match tvToFieldSet sc merged with | none => .error | some none => .panic | some (some s) => pure s)
      let prunedSet ← (match tvToFieldSet sc pruned with | none => .error | some none => .panic | some (some s) => pure s)
      ofPanicOpt (tvRemoveItems sc merged ((mergedSet.ensureNamed sc tr).diff
        ((prunedSet.ensureNamed sc tr).union (managed.ensureNamed sc tr)))))
    -- `addBackDanglingItems`
    let prunedSet ← (match tvToFieldSet sc pruned with | none => .error | some none => .panic | some (some s) => pure s)
    let mergedSet ← (match tvToFieldSet sc merged with | none => .error | some none => .panic | some (some s) => pure s)
    let _ := manager
    ofPanicOpt (tvRemoveItems sc merged (((mergedSet.ensureNamed sc tr).diff (prunedSet.ensureNamed sc tr)).inter
      (last.set.ensureNamed sc tr)))

/-- The outcome of `Updater.Apply`. -/
inductive ApplyRes where
  /-- The new object (`none`: nil, a no-op without `ReturnInputOnNoop`) and managers. -/
  | ok (obj : Option TV) (mf : MF)
  /-- A `Conflicts` error: the conflicting managers' conflict sets. -/
  | conflicts (cs : MF)
  /-- Another error (the managers returned are an empty map). -/
  | error
  | panic

/-- `Updater.Apply` (the identity converter, no ignored fields). -/
def apply (returnInputOnNoop : Bool) (sc : Schema) (live config : TV) (version : GoString)
    (mf : MF) (manager : GoString) (force : Bool) : ApplyRes :=
  match reconcileMF sc live mf with
  | .error => .error
  | .panic => .panic
  | .ok mf =>
  match tvMerge sc live config with
  | none => .error
  | some newObject =>
  let lastSet := lookupKV manager mf
  match tvToFieldSet sc config with
  | none => .error
  | some none => .panic
  | some (some set) =>
  let mf := insertKV manager ⟨set, version, true⟩ mf
  match prune sc newObject mf manager lastSet with
  | .error => .error
  | .panic => .panic
  | .ok newObject =>
  match update sc live newObject mf manager force with
  | .error => .error
  | .panic => .panic
  | .conflicts cs => .conflicts cs
  | .ok mf _ =>
    if returnInputOnNoop then .ok (some newObject) mf else
    match live.value, newObject.value with
    | some l, some r => if UVal.equals l r then .ok none mf else .ok (some newObject) mf
    | _, _ => .panic

/-- The outcome of `Updater.Update`: the managers (the object returned is `newObject`). -/
inductive UpdateRes where
  | ok (mf : MF)
  | error
  | panic

/-- `Updater.Update` (the identity converter, no ignored fields). -/
def updateObj (sc : Schema) (live new : TV) (version : GoString) (mf : MF) (manager : GoString) :
    UpdateRes :=
  match reconcileMF sc live mf with
  | .error => .error
  | .panic => .panic
  | .ok mf =>
  match update sc live new mf manager true with
  | .error | .conflicts _ => .error
  | .panic => .panic
  | .ok mf c =>
    let cur : VSet := (lookupKV manager mf).getD ⟨.empty, version, false⟩
    let set := ((cur.set.diff c.removed).union c.modified).union c.added
    let mf := insertKV manager ⟨set, version, false⟩ mf
    .ok (if set.isEmpty then eraseKV manager mf else mf)

/-- `merge.Conflict`. -/
structure Conflict where
  manager : GoString
  path : Path

/-- `ConflictsFromManagers`, the managers in the order given. -/
def conflictsOf (cs : MF) : List Conflict :=
  cs.flatMap (fun (m, vs) => (vs.set.paths []).map (fun p => ⟨m, p⟩))

/-- `Conflicts.Equals`. -/
def conflictsEquals (a b : List Conflict) : Bool :=
  a.length == b.length &&
    (a.zip b).all (fun (x, y) => decide (x.manager = y.manager) && pathEquals x.path y.path)

end smd
end EtcdGrove
end Perennial
