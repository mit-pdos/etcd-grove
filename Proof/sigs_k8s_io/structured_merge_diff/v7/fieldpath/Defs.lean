/-
**structured-merge-diff's field paths and field sets, abstractly** (`fieldpath` package, v7.0.0):
the vocabulary of the SMD API specs (`notes/smd-plan.md`, "The vocabulary").

- `PE`: a path element (`fieldpath.PathElement`): a field name, a key (an associative list item's
  key fields, `(name, value)` in the order given: SMD sorts them by name), a set item's value, a
  list index. `Path`: a list of them.
- `PathSet`: a **finite set of paths** (`FSet Path`: lists up to having the same members, a
  quotient), every path non-empty (`Set.Insert` of the empty path does nothing: "no one owns the
  entire object"). Its equality is the sets' (extensional) and decidable, so a client decides an
  equality of literal sets by `decide`. The trie SMD keeps (`Set`: sorted members, sorted
  children) is the representation's business (`isSet`): it is canonical (sorted by
  `PathElement.Compare`, no element twice, no child without a member below it), every operation
  SMD reaches keeps it so, and then `Set.Equals` is the equality of the sets.
- `VSet` (`VersionedSet`: a set, an API version, whether it was applied) and `MF`
  (`ManagedFields`: the managers' entries, an association list sorted by manager, so that equal
  managed fields are equal lists; `MF.ofList` sorts a literal's entries).

Representation predicates: `isSet` (persistent: a set the API hands out or takes) and `ownSet`
(exclusive: a set under construction, `NewSet`'s and the walkers'; `ownSet_persist` turns it into
`isSet`). The internals (`trieRep`, `isPEL`, ...) are sealed (`@[no_expose]`).

Lean-first (2026-11-19, notes/smd-plan.md); round 1's repairs 2026-11-19.
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
  deriving DecidableEq, Inhabited

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

/-! ## Finite sets -/

/-- Two lists with the same members. -/
def FSet.Same {α : Type} (a b : List α) : Prop := ∀ x, x ∈ a ↔ x ∈ b

instance FSet.setoid (α : Type) : Setoid (List α) where
  r := FSet.Same
  iseqv := ⟨fun _ _ => Iff.rfl, fun h x => (h x).symm, fun h1 h2 x => (h1 x).trans (h2 x)⟩

/-- **A finite set**: a list up to having the same members (order and repetitions forgotten). -/
def FSet (α : Type) : Type := Quotient (FSet.setoid α)

namespace FSet
variable {α β : Type}

/-- The set of a list's members. -/
def ofList (l : List α) : FSet α := Quotient.mk _ l
def empty : FSet α := ofList []

/-- Membership, decided. -/
def mem [DecidableEq α] (s : FSet α) (x : α) : Bool :=
  Quotient.lift (fun l : List α => decide (x ∈ l))
    (fun a b (h : FSet.Same a b) => by simp only [h x]) s

/-- Some member satisfies `p`. -/
def any (p : α → Bool) (s : FSet α) : Bool :=
  Quotient.lift (fun l : List α => l.any p)
    (fun a b (h : FSet.Same a b) => by
      apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
      exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, (h x).1 hx, hp⟩, fun ⟨x, hx, hp⟩ => ⟨x, (h x).2 hx, hp⟩⟩) s

/-- Every member satisfies `p`. -/
def all (p : α → Bool) (s : FSet α) : Bool := !s.any (fun x => !p x)

/-- No member. -/
def isEmpty (s : FSet α) : Bool := !s.any (fun _ => true)

/-- A function of the list representation that keeps lists with the same members together. -/
def lift1 (f : List α → List β) (hf : ∀ a b : List α, FSet.Same a b → FSet.Same (f a) (f b))
    (s : FSet α) : FSet β :=
  Quotient.lift (fun l => (Quotient.mk _ (f l) : FSet β)) (fun a b h => Quotient.sound (hf a b h)) s

/-- The members satisfying `p`. -/
def filter (p : α → Bool) (s : FSet α) : FSet α :=
  lift1 (List.filter p)
    (fun a b (h : FSet.Same a b) x => by simp only [List.mem_filter, h x]) s

/-- The union of `f x` over the members `x`. -/
def bind (f : α → List β) (s : FSet α) : FSet β :=
  lift1 (fun l => l.flatMap f)
    (fun a b (h : FSet.Same a b) x => by
      simp only [List.mem_flatMap]
      exact ⟨fun ⟨y, hy, hx⟩ => ⟨y, (h y).1 hy, hx⟩, fun ⟨y, hy, hx⟩ => ⟨y, (h y).2 hy, hx⟩⟩) s

/-- The image. -/
def map (f : α → β) (s : FSet α) : FSet β := s.bind (fun x => [f x])

def union (a b : FSet α) : FSet α :=
  Quotient.lift₂ (fun x y => (Quotient.mk _ (x ++ y) : FSet α))
    (fun _ _ _ _ (ha : FSet.Same _ _) (hb : FSet.Same _ _) => Quotient.sound (fun x => by
      simp only [List.mem_append, ha x, hb x])) a b

def inter [DecidableEq α] (a b : FSet α) : FSet α := a.filter b.mem
def diff [DecidableEq α] (a b : FSet α) : FSet α := a.filter (fun x => !b.mem x)

instance [DecidableEq α] : Membership α (FSet α) := ⟨fun s x => s.mem x = true⟩

instance [DecidableEq α] (x : α) (s : FSet α) : Decidable (x ∈ s) :=
  inferInstanceAs (Decidable (s.mem x = true))

/-- Equality of finite sets (same members), decided. -/
instance [DecidableEq α] : DecidableEq (FSet α) := fun a b =>
  decidable_of_iff ((a.all b.mem && b.all a.mem) = true) (by
    induction a using Quotient.inductionOn with | h la =>
    induction b using Quotient.inductionOn with | h lb =>
    show ((!(la.any fun x => !decide (x ∈ lb))) && !(lb.any fun x => !decide (x ∈ la))) = true ↔ _
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
      decide_eq_false_iff_not, Classical.not_not]
    constructor
    · rintro ⟨h1, h2⟩; exact Quotient.sound (fun x => ⟨h1 x, h2 x⟩)
    · intro h
      have h' : FSet.Same la lb := Quotient.exact h
      exact ⟨fun x hx => (h' x).1 hx, fun x hx => (h' x).2 hx⟩)

instance : Inhabited (FSet α) := ⟨empty⟩

end FSet

/-! ## Sets of paths -/

/-- A set of paths (see the file header). -/
abbrev PathSet := FSet Path

namespace PathSet
def empty : PathSet := FSet.empty
def union (a b : PathSet) : PathSet := FSet.union a b
def inter (a b : PathSet) : PathSet := FSet.inter a b
def diff (a b : PathSet) : PathSet := FSet.diff a b
/-- No path (`Set.Empty`). -/
def IsEmpty (a : PathSet) : Prop := a.isEmpty = true
/-- The paths below `e`, without it (`Set.WithPrefix`). -/
def under (a : PathSet) (e : PE) : PathSet :=
  a.bind (fun q => match q with
    | e' :: r@(_ :: _) => if e' = e then [r] else []
    | _ => [])
/-- The non-empty paths of a list (`NewSet(paths...)`). -/
def ofList (ps : List Path) : PathSet := FSet.ofList (ps.filter (fun p => !p.isEmpty))
/-- `{p}` (`NewSet(p)`: empty for the empty path). -/
def single (p : Path) : PathSet := ofList [p]
end PathSet

instance (a : PathSet) : Decidable a.IsEmpty := inferInstanceAs (Decidable (_ = true))

/-- A `fieldpath.VersionedSet`. -/
structure VSet where
  set : PathSet
  version : GoString
  applied : Bool

/-- Equality of versioned sets, decided componentwise (not by the deriving handler, whose
transport along the sets' equality is stuck for the kernel: equal sets are not definitionally
equal). -/
instance : DecidableEq VSet := fun a b =>
  decidable_of_iff (a.set = b.set ∧ a.version = b.version ∧ a.applied = b.applied) (by
    cases a; cases b; simp only [VSet.mk.injEq])

/-- A `fieldpath.ManagedFields`: each manager's entry, as an association list sorted by manager
(`keysSorted`; every operation below keeps it so), so that two managed fields with the same
entries are the same list. -/
abbrev MF := List (GoString × VSet)

/-- A manager's entry. -/
def MF.get (mf : MF) (m : GoString) : Option VSet := lookupKV m mf

/-- No manager (`fieldpath.ManagedFields{}`). -/
def MF.none : MF := []

/-- A `ManagedFields` literal (`fieldpath.ManagedFields{m: e, ...}`, any order; sorted here). -/
def MF.ofList (ms : List (GoString × VSet)) : MF := kvsOf ms

/-- `mf[m] = e`. -/
def MF.set (mf : MF) (m : GoString) (e : VSet) : MF := insertKV m e mf

/-! ## The trie of a set (the representation's) -/

/-- `fieldpath.Set`: members (`PathElementSet`) and children (`SetNodeMap`). -/
inductive Trie where
  | mk (members : List PE) (children : List (PE × Trie))

mutual
/-- The paths of a trie. -/
def Trie.paths : Trie → Path → Prop
  | .mk ms cs => fun q => (∃ e, q = [e] ∧ e ∈ ms) ∨ Trie.pathsC cs q
/-- The paths below a list of children. -/
def Trie.pathsC : List (PE × Trie) → Path → Prop
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

/-- A `value.FieldList`'s fields (internal). -/
@[no_expose] def isFieldsL : List value.Field → FieldList → IProp GF
  | [], [] => iprop(True)
  | f :: fs, (n, x) :: rest => iprop(⌜f.Name' = n⌝ ∗ isVal f.Value' x ∗ isFieldsL fs rest)
  | _, _ => iprop(False)

/-- **`isFieldList s fl`**: the `value.FieldList` slice `s` holds `fl` (persistent). -/
@[no_expose] def isFieldList (s : GoSlice) (fl : FieldList) : IProp GF :=
  iprop(∃ fs : List value.Field, s ↦*{DFrac.discard} fs ∗ isFieldsL fs fl)

/-- **`isPE e pe`**: the `fieldpath.PathElement` `e` is `pe` (its first non-nil field;
persistent). -/
@[no_expose] def isPE (e : fieldpath.PathElement) : PE → IProp GF
  | .field n => iprop(e.FieldName' ↦□ n)
  | .key fl => iprop(⌜e.FieldName' = null⌝ ∗ ∃ s : GoSlice, e.Key' ↦□ s ∗ isFieldList s fl)
  | .value x => iprop(⌜e.FieldName' = null ∧ e.Key' = null⌝ ∗
      ∃ v : value.Value, e.Value' ↦□ v ∗ isVal v x)
  | .index i => iprop(⌜e.FieldName' = null ∧ e.Key' = null ∧ e.Value' = null⌝ ∗ e.Index' ↦□ i)

/-- A list of path elements (internal). -/
@[no_expose] def isPEL : List fieldpath.PathElement → List PE → IProp GF
  | [], [] => iprop(True)
  | e :: es, pe :: pes => iprop(isPE e pe ∗ isPEL es pes)
  | _, _ => iprop(False)

/-- **`isPath s p`**: the `fieldpath.Path` slice `s` holds `p` (persistent). -/
@[no_expose] def isPath (s : GoSlice) (p : Path) : IProp GF :=
  iprop(∃ es : List fieldpath.PathElement, s ↦*{DFrac.discard} es ∗ isPEL es p)

/-- **`isPaths ss ps`**: the `fieldpath.Path` slices `ss` (a `[]fieldpath.Path`'s elements) hold
the paths `ps` (persistent). -/
@[no_expose] def isPaths : List GoSlice → List Path → IProp GF
  | [], [] => iprop(True)
  | s :: ss, p :: ps => iprop(isPath s p ∗ isPaths ss ps)
  | _, _ => iprop(False)

mutual
/-- The trie at `p`: its members' and children's slices (internal). -/
@[no_expose] def trieRep (p : Loc) : Trie → IProp GF
  | .mk ms cs => iprop(∃ (v : fieldpath.Set') (es : List fieldpath.PathElement)
      (ns : List fieldpath.setNode),
      p ↦□ v ∗ v.Members'.members' ↦*{DFrac.discard} es ∗ isPEL es ms ∗
      v.Children'.members' ↦*{DFrac.discard} ns ∗ trieRepC ns cs)
  termination_by structural t => t
/-- A `SetNodeMap`'s nodes (internal). -/
@[no_expose] def trieRepC : List fieldpath.setNode → List (PE × Trie) → IProp GF
  | [], [] => iprop(True)
  | n :: ns, (pe, t) :: cs => iprop(isPE n.pathElement' pe ∗ trieRep n.set' t ∗ trieRepC ns cs)
  | _, _ => iprop(False)
  termination_by structural _ cs => cs
end

/-- **`isSet p S`**: the `*fieldpath.Set` at `p` holds the set of paths `S`, as a canonical trie
(persistent). -/
@[no_expose] def isSet (p : Loc) (S : PathSet) : IProp GF :=
  iprop(∃ t : Trie, ⌜t.Canonical ∧ ∀ q, t.paths q ↔ q ∈ S⌝ ∗ trieRep p t)

mutual
/-- The trie at `p`, owned (internal): the set's struct, its members' and children's slices with
their capacity, each child set owned. -/
@[no_expose] def trieOwn (p : Loc) : Trie → IProp GF
  | .mk ms cs => iprop(∃ (v : fieldpath.Set') (es : List fieldpath.PathElement)
      (ns : List fieldpath.setNode),
      p ↦ v ∗ v.Members'.members' ↦* es ∗
      ownSliceCap fieldpath.PathElement v.Members'.members' (DFrac.own 1) ∗ isPEL es ms ∗
      v.Children'.members' ↦* ns ∗
      ownSliceCap fieldpath.setNode v.Children'.members' (DFrac.own 1) ∗ trieOwnC ns cs)
  termination_by structural t => t
/-- A `SetNodeMap`'s nodes, owned (internal). -/
@[no_expose] def trieOwnC : List fieldpath.setNode → List (PE × Trie) → IProp GF
  | [], [] => iprop(True)
  | n :: ns, (pe, t) :: cs => iprop(isPE n.pathElement' pe ∗ trieOwn n.set' t ∗ trieOwnC ns cs)
  | _, _ => iprop(False)
  termination_by structural _ cs => cs
end

/-- **`ownSet p S`**: the `*fieldpath.Set` at `p` holds the set of paths `S`, as a canonical trie,
**owned** (exclusive): a set under construction (`NewSet`'s, the walkers' `Comparison` and field
sets), which `Set.Insert` updates in place. `ownSet_persist` (`Laws.lean`) hands it out as an
`isSet`. -/
@[no_expose] def ownSet (p : Loc) (S : PathSet) : IProp GF :=
  iprop(∃ t : Trie, ⌜t.Canonical ∧ ∀ q, t.paths q ↔ q ∈ S⌝ ∗ trieOwn p t)

/-- **`isVSet i e`**: the `fieldpath.VersionedSet` `i` (a `versionedSet`) holds `e`
(persistent). -/
@[no_expose] def isVSet (i : fieldpath.VersionedSet) (e : VSet) : IProp GF :=
  iprop(∃ p : Loc,
    ⌜i = interface.mkOk fieldpath.versionedSet.ty #(fieldpath.versionedSet.mk p e.version e.applied)⌝ ∗
    isSet p e.set)

/-- The entries of a `ManagedFields` map (internal). -/
@[no_expose] def isMFL (M : GMap GoString GoInterface) : MF → IProp GF
  | [] => iprop(True)
  | (k, e) :: rest => iprop(∃ i : GoInterface, ⌜M !! k = some i⌝ ∗ isVSet i e ∗ isMFL M rest)

/-- **`isMF m mf`**: the `fieldpath.ManagedFields` `m` (a non-nil Go map: scope restriction, a nil
`ManagedFields` is not admitted) holds `mf`: the same managers, each entry's set, version and
applied flag (persistent). -/
@[no_expose] def isMF (m : fieldpath.ManagedFields) (mf : MF) : IProp GF :=
  iprop(∃ M : GMap GoString GoInterface, m ↦$□ M ∗
    ⌜keysSorted mf = true ∧ ∀ k, (M !! k).isSome = (mf.get k).isSome⌝ ∗ isMFL M mf)

end own

end smd
end EtcdGrove
end Perennial
