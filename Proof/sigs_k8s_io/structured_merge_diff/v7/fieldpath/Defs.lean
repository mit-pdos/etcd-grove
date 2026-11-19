/-
**structured-merge-diff's field paths and field sets, abstractly** (`fieldpath` package, v7.0.0):
the vocabulary of the SMD API specs (`notes/smd-plan.md`, "The vocabulary").

- `PE`: a path element (`fieldpath.PathElement`): a field name, a key (an associative list item's
  key fields, `(name, value)` in the order given: SMD sorts them by name), a set item's value, a
  list index. `Path`: a list of them.
- `PathSet`: a **set of paths**, mathematically (`Path → Prop`), every path non-empty
  (`Set.Insert` of the empty path does nothing: "no one owns the entire object"). The trie SMD
  keeps (`Set`: sorted members, sorted children) is the representation's business (`isSet`): it is
  canonical (sorted by `PathElement.Compare`, no element twice, no child without a member below
  it), every operation SMD reaches keeps it so, and then `Set.Equals` is the equality of the sets.
- `VSet` (`VersionedSet`: a set, an API version, whether it was applied) and `MF`
  (`ManagedFields`: a manager's entry, if any).

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Path elements and paths -/

/-- A `value.FieldList`: `(name, value)` pairs. -/
abbrev FieldList := List (GoString × UVal)

/-- `fieldpath.PathElement` (its one non-nil field). -/
inductive PE where
  | field (n : GoString)
  | key (fl : FieldList)
  | value (v : UVal)
  | index (i : w64)
  deriving Inhabited

abbrev Path := List PE

/-- `FieldList.Compare`. -/
def flCompare : FieldList → FieldList → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | (n, v) :: xs, (n', v') :: ys =>
    let c := gsCompare n n'
    if c != 0 then c else
    let c := UVal.compare v v'
    if c != 0 then c else flCompare xs ys

/-- `PathElement.Compare`: the order of a set's sorted slices. -/
def PE.compare : PE → PE → Int
  | .field a, .field b => gsCompare a b
  | .field _, _ => -1
  | _, .field _ => 1
  | .key a, .key b => flCompare a b
  | .key _, _ => -1
  | _, .key _ => 1
  | .value a, .value b => UVal.compare a b
  | .value _, _ => -1
  | _, .value _ => 1
  | .index a, .index b => intCompare a b

/-! ## Sets of paths -/

/-- A set of paths (see the file header). -/
abbrev PathSet := Path → Prop

namespace PathSet
def empty : PathSet := fun _ => False
def union (a b : PathSet) : PathSet := fun p => a p ∨ b p
def inter (a b : PathSet) : PathSet := fun p => a p ∧ b p
def diff (a b : PathSet) : PathSet := fun p => a p ∧ ¬ b p
/-- No path (`Set.Empty`). -/
def IsEmpty (a : PathSet) : Prop := ∀ p, ¬ a p
/-- The paths below `e`, without it (`Set.WithPrefix`). -/
def under (a : PathSet) (e : PE) : PathSet := fun q => q ≠ [] ∧ a (e :: q)
/-- The non-empty paths of a list (`NewSet(paths...)`). -/
def ofList (ps : List Path) : PathSet := fun p => p ≠ [] ∧ p ∈ ps
/-- `{p}` (`NewSet(p)`: empty for the empty path). -/
def single (p : Path) : PathSet := ofList [p]
end PathSet

/-- A `fieldpath.VersionedSet`. -/
structure VSet where
  set : PathSet
  version : GoString
  applied : Bool

/-- A `fieldpath.ManagedFields`: each manager's entry, if any. -/
abbrev MF := GoString → Option VSet

/-- No manager (`fieldpath.ManagedFields{}`). -/
def MF.none : MF := fun _ => Option.none

/-! ## The trie of a set (the representation's) -/

/-- `fieldpath.Set`: members (`PathElementSet`) and children (`SetNodeMap`). -/
inductive Trie where
  | mk (members : List PE) (children : List (PE × Trie))

mutual
/-- The paths of a trie. -/
def Trie.paths : Trie → PathSet
  | .mk ms cs => fun q => (∃ e, q = [e] ∧ e ∈ ms) ∨ Trie.pathsC cs q
/-- The paths below a list of children. -/
def Trie.pathsC : List (PE × Trie) → PathSet
  | [] => fun _ => False
  | (e, t) :: cs => fun q => (∃ r, q = e :: r ∧ Trie.paths t r) ∨ Trie.pathsC cs q
end

mutual
/-- A canonical trie: members and children strictly sorted (`PE.compare`), every child canonical
and with a path (`Set.Union`, `Intersection`, `Difference`, `Insert` keep this). -/
def Trie.Canonical : Trie → Prop
  | .mk ms cs => ms.Pairwise (fun a b => PE.compare a b < 0) ∧
      (cs.map (·.1)).Pairwise (fun a b => PE.compare a b < 0) ∧ Trie.CanonicalC cs
def Trie.CanonicalC : List (PE × Trie) → Prop
  | [] => True
  | (_, t) :: cs => Trie.Canonical t ∧ (∃ q, Trie.paths t q) ∧ Trie.CanonicalC cs
end

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A `value.FieldList`'s fields. -/
def isFieldsL : List value.Field → FieldList → IProp GF
  | [], [] => iprop(True)
  | f :: fs, (n, x) :: rest => iprop(⌜f.Name' = n⌝ ∗ isVal f.Value' x ∗ isFieldsL fs rest)
  | _, _ => iprop(False)

/-- **`isFieldList s fl`**: the `value.FieldList` slice `s` holds `fl` (persistent). -/
def isFieldList (s : GoSlice) (fl : FieldList) : IProp GF :=
  iprop(∃ fs : List value.Field, s ↦*{DFrac.discard} fs ∗ isFieldsL fs fl)

/-- **`isPE e pe`**: the `fieldpath.PathElement` `e` is `pe` (its first non-nil field;
persistent). -/
def isPE (e : fieldpath.PathElement) : PE → IProp GF
  | .field n => iprop(e.FieldName' ↦□ n)
  | .key fl => iprop(⌜e.FieldName' = null⌝ ∗ ∃ s : GoSlice, e.Key' ↦□ s ∗ isFieldList s fl)
  | .value x => iprop(⌜e.FieldName' = null ∧ e.Key' = null⌝ ∗
      ∃ v : value.Value, e.Value' ↦□ v ∗ isVal v x)
  | .index i => iprop(⌜e.FieldName' = null ∧ e.Key' = null ∧ e.Value' = null⌝ ∗ e.Index' ↦□ i)

/-- A list of path elements. -/
def isPEL : List fieldpath.PathElement → List PE → IProp GF
  | [], [] => iprop(True)
  | e :: es, pe :: pes => iprop(isPE e pe ∗ isPEL es pes)
  | _, _ => iprop(False)

/-- **`isPath s p`**: the `fieldpath.Path` slice `s` holds `p` (persistent). -/
def isPath (s : GoSlice) (p : Path) : IProp GF :=
  iprop(∃ es : List fieldpath.PathElement, s ↦*{DFrac.discard} es ∗ isPEL es p)

/-- A list of paths (the elements of a `[]fieldpath.Path`). -/
def isPaths : List GoSlice → List Path → IProp GF
  | [], [] => iprop(True)
  | s :: ss, p :: ps => iprop(isPath s p ∗ isPaths ss ps)
  | _, _ => iprop(False)

mutual
/-- The trie at `p`: its members' and children's slices. -/
def trieRep (p : Loc) : Trie → IProp GF
  | .mk ms cs => iprop(∃ (v : fieldpath.Set') (es : List fieldpath.PathElement)
      (ns : List fieldpath.setNode),
      p ↦□ v ∗ v.Members'.members' ↦*{DFrac.discard} es ∗ isPEL es ms ∗
      v.Children'.members' ↦*{DFrac.discard} ns ∗ trieRepC ns cs)
  termination_by structural t => t
/-- A `SetNodeMap`'s nodes. -/
def trieRepC : List fieldpath.setNode → List (PE × Trie) → IProp GF
  | [], [] => iprop(True)
  | n :: ns, (pe, t) :: cs => iprop(isPE n.pathElement' pe ∗ trieRep n.set' t ∗ trieRepC ns cs)
  | _, _ => iprop(False)
  termination_by structural _ cs => cs
end

/-- **`isSet p S`**: the `*fieldpath.Set` at `p` holds the set of paths `S`, as a canonical trie
(persistent). -/
def isSet (p : Loc) (S : PathSet) : IProp GF :=
  iprop(∃ t : Trie, ⌜t.Canonical ∧ ∀ q, t.paths q ↔ S q⌝ ∗ trieRep p t)

/-- **`isVSet i e`**: the `fieldpath.VersionedSet` `i` (a `versionedSet`) holds `e`
(persistent). -/
def isVSet (i : fieldpath.VersionedSet) (e : VSet) : IProp GF :=
  iprop(∃ p : Loc,
    ⌜i = interface.mkOk fieldpath.versionedSet.ty #(fieldpath.versionedSet.mk p e.version e.applied)⌝ ∗
    isSet p e.set)

/-- The entries of a `ManagedFields` map, for the managers `ks`. -/
def isMFL (M : GMap GoString GoInterface) (mf : MF) : List GoString → IProp GF
  | [] => iprop(True)
  | k :: ks => iprop(∃ (i : GoInterface) (e : VSet), ⌜M !! k = some i ∧ mf k = some e⌝ ∗
      isVSet i e ∗ isMFL M mf ks)

/-- **`isMF m mf`**: the `fieldpath.ManagedFields` `m` (a non-nil Go map) holds `mf`: the same
managers, each entry's set, version and applied flag (persistent). -/
def isMF (m : fieldpath.ManagedFields) (mf : MF) : IProp GF :=
  iprop(∃ (M : GMap GoString GoInterface) (ks : List GoString), m ↦$□ M ∗
    ⌜ks.Nodup ∧ ∀ k, (k ∈ ks ↔ (M !! k).isSome) ∧ (k ∈ ks ↔ (mf k).isSome)⌝ ∗ isMFL M mf ks)

end own

end smd
end EtcdGrove
end Perennial
