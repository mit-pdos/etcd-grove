/-
The pure model of SMD's **field paths and sets** (`fieldpath` package): `PathElement`
(`PE`), `PathElementSet` (sorted lists), `Set` (`PSet`: members and children, the children a
sorted `SetNodeMap`), its operations, `VersionedSet` and `ManagedFields`.

Each operation transcribes the Go function: `PathElementSet.Insert`/`Has` and
`SetNodeMap.Descend`/`Get` as their binary searches compute them (the least element not below
the key: `slices.BinarySearchFunc`'s trust-boundary spec), the two-list merges (`Union`,
`Intersection`, `Difference`, `RecursiveDifference`) with fuel (`*F`; the wrappers give
`weight a + weight b + 1`, more than the merges' steps), so that everything is structurally
recursive and reduces in the kernel. A set's structure is kept exactly as Go's (`Set.Equals`
compares it: `Union` keeps empty children, `Difference` and `Intersection` drop them).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Model.Schema

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace smd

/-! ## fieldpath -/

/-- `fieldpath.PathElement`: its first non-nil field (`invalid`: all nil). -/
inductive PE where
  | field (n : GoString)
  | key (fl : FieldList)
  | value (v : UVal)
  | index (i : w64)
  | invalid
  deriving Inhabited

/-- `PathElement.Compare`. -/
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
  | .index _, _ => -1
  | _, .index _ => 1
  | .invalid, .invalid => 0

def PE.less (a b : PE) : Bool := a.compare b < 0

/-- `PathElement.Equals`. -/
def PE.equals : PE → PE → Bool
  | .field a, .field b => decide (a = b)
  | .key a, .key b => flEquals a b
  | .value a, .value b => UVal.equals a b
  | .index a, .index b => a == b
  | .invalid, .invalid => true
  | _, _ => false

abbrev Path := List PE

/-- `Path.Equals`. -/
def pathEquals (a b : Path) : Bool :=
  a.length == b.length && (a.zip b).all (fun (x, y) => x.equals y)

/-! ### `PathElementSet`: sorted -/

/-- `PathElementSet.Insert` (binary search: the least element `≥ pe`). -/
def pesInsert (pe : PE) : List PE → List PE
  | [] => [pe]
  | a :: as =>
    let c := a.compare pe
    if c < 0 then a :: pesInsert pe as else if c == 0 then a :: as else pe :: a :: as

/-- `PathElementSet.Has`. -/
def pesHas (pe : PE) : List PE → Bool
  | [] => false
  | a :: as => let c := a.compare pe; if c < 0 then pesHas pe as else c == 0

/-- `PathElementSet.Union`'s loop. -/
def pesUnion : Nat → List PE → List PE → List PE
  | 0, _, _ => []
  | _ + 1, as, [] => as
  | _ + 1, [], bs => bs
  | n + 1, a :: as, b :: bs =>
    if a.less b then a :: pesUnion n as (b :: bs)
    else if !(b.less a) then b :: pesUnion n as bs
    else b :: pesUnion n (a :: as) bs

/-- `PathElementSet.Intersection`'s loop. -/
def pesInter : Nat → List PE → List PE → List PE
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | _ + 1, [], _ => []
  | n + 1, a :: as, b :: bs =>
    if a.less b then pesInter n as (b :: bs)
    else if !(b.less a) then a :: pesInter n as bs
    else pesInter n (a :: as) bs

/-- `PathElementSet.Difference`'s loop. -/
def pesDiff : Nat → List PE → List PE → List PE
  | 0, _, _ => []
  | _ + 1, as, [] => as
  | _ + 1, [], _ => []
  | n + 1, a :: as, b :: bs =>
    if a.less b then a :: pesDiff n as (b :: bs)
    else if !(b.less a) then pesDiff n as bs
    else pesDiff n (a :: as) bs

/-- `PathElementSet.Equals`. -/
def pesEquals (as bs : List PE) : Bool :=
  as.length == bs.length && (as.zip bs).all (fun (a, b) => a.equals b)

/-! ### `Set`: the trie of members and children (`SetNodeMap`, sorted) -/

inductive PSet where
  | mk (members : List PE) (children : List (PE × PSet))
  deriving Inhabited

namespace PSet
def members : PSet → List PE | .mk m _ => m
def children : PSet → List (PE × PSet) | .mk _ c => c

/-- `&Set{}`, `NewSet()`. -/
def empty : PSet := .mk [] []

mutual
def weight : PSet → Nat
  | .mk ms cs => ms.length + weightL cs + 1
def weightL : List (PE × PSet) → Nat
  | [] => 0
  | (_, s) :: cs => weight s + weightL cs + 1
end

/-- `SetNodeMap.Descend(pe)`: the child set at `pe` (a new empty one if none), replaced by
`f` of it. -/
def descend (pe : PE) (f : PSet → PSet) : List (PE × PSet) → List (PE × PSet)
  | [] => [(pe, f empty)]
  | (a, s) :: rest =>
    let c := a.compare pe
    if c < 0 then (a, s) :: descend pe f rest
    else if c == 0 then (a, f s) :: rest
    else (pe, f empty) :: (a, s) :: rest

/-- `Set.Insert`. -/
def insert : PSet → Path → PSet
  | s, [] => s
  | .mk ms cs, pe :: p =>
    if p.isEmpty then .mk (pesInsert pe ms) cs else .mk ms (descend pe (fun c => insert c p) cs)

/-- `NewSet(paths...)`. -/
def ofPaths (ps : List Path) : PSet := ps.foldl (fun s p => s.insert p) empty

/-- `SetNodeMap.Get`. -/
def nodeGet (pe : PE) : List (PE × PSet) → Option PSet
  | [] => none
  | (a, s) :: rest => let c := a.compare pe; if c < 0 then nodeGet pe rest else if c == 0 then some s else none

mutual
/-- `Set.Empty`. -/
def isEmpty : PSet → Bool
  | .mk ms cs => ms.isEmpty && isEmptyL cs
/-- `SetNodeMap.Empty`. -/
def isEmptyL : List (PE × PSet) → Bool
  | [] => true
  | (_, s) :: cs => isEmpty s && isEmptyL cs
end

mutual
/-- `Set.Size`. -/
def size : PSet → Nat
  | .mk ms cs => ms.length + sizeL cs
def sizeL : List (PE × PSet) → Nat
  | [] => 0
  | (_, s) :: cs => size s + sizeL cs
end

/-- `Set.Has`. -/
def has : PSet → Path → Bool
  | _, [] => false
  | s, [pe] => pesHas pe s.members
  | s, pe :: p => match nodeGet pe s.children with | some c => has c p | none => false

/-- `Set.WithPrefix`. -/
def withPrefix (s : PSet) (pe : PE) : PSet := (nodeGet pe s.children).getD empty

mutual
/-- `Set.Equals`. -/
def equals : PSet → PSet → Bool
  | .mk ms cs, .mk ms' cs' => pesEquals ms ms' && cs.length == cs'.length && equalsL cs cs'
/-- `SetNodeMap.Equals`'s loop (the lengths are equal). -/
def equalsL : List (PE × PSet) → List (PE × PSet) → Bool
  | (a, s) :: cs, (b, s') :: cs' => a.equals b && equals s s' && equalsL cs cs'
  | _, _ => true
end

mutual
/-- `Set.Union`, with fuel. -/
def unionF : Nat → PSet → PSet → PSet
  | 0, _, _ => empty
  | n + 1, .mk m1 c1, .mk m2 c2 => .mk (pesUnion (m1.length + m2.length + 1) m1 m2) (nodeUnionF n c1 c2)
/-- `SetNodeMap.Union`'s loop. -/
def nodeUnionF : Nat → List (PE × PSet) → List (PE × PSet) → List (PE × PSet)
  | 0, _, _ => []
  | _ + 1, as, [] => as
  | _ + 1, [], bs => bs
  | n + 1, (a, sa) :: as, (b, sb) :: bs =>
    if a.less b then (a, sa) :: nodeUnionF n as ((b, sb) :: bs)
    else if !(b.less a) then (a, unionF n sa sb) :: nodeUnionF n as bs
    else (b, sb) :: nodeUnionF n ((a, sa) :: as) bs
end
def union (a b : PSet) : PSet := unionF (a.weight + b.weight + 1) a b

mutual
/-- `Set.Intersection`, with fuel. -/
def interF : Nat → PSet → PSet → PSet
  | 0, _, _ => empty
  | n + 1, .mk m1 c1, .mk m2 c2 => .mk (pesInter (m1.length + m2.length + 1) m1 m2) (nodeInterF n c1 c2)
def nodeInterF : Nat → List (PE × PSet) → List (PE × PSet) → List (PE × PSet)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | _ + 1, [], _ => []
  | n + 1, (a, sa) :: as, (b, sb) :: bs =>
    if a.less b then nodeInterF n as ((b, sb) :: bs)
    else if !(b.less a) then
      let res := interF n sa sb
      if !res.isEmpty then (a, res) :: nodeInterF n as bs else nodeInterF n as bs
    else nodeInterF n ((a, sa) :: as) bs
end
def inter (a b : PSet) : PSet := interF (a.weight + b.weight + 1) a b

mutual
/-- `Set.Difference`, with fuel. -/
def diffF : Nat → PSet → PSet → PSet
  | 0, _, _ => empty
  | n + 1, .mk m1 c1, .mk m2 c2 => .mk (pesDiff (m1.length + m2.length + 1) m1 m2) (nodeDiffF n c1 c2)
/-- `SetNodeMap.Difference(s2)`'s loop over `s2.Children`. -/
def nodeDiffF : Nat → List (PE × PSet) → List (PE × PSet) → List (PE × PSet)
  | 0, _, _ => []
  | _ + 1, as, [] => as
  | _ + 1, [], _ => []
  | n + 1, (a, sa) :: as, (b, sb) :: bs =>
    if a.less b then (a, sa) :: nodeDiffF n as ((b, sb) :: bs)
    else if !(b.less a) then
      let d := diffF n sa sb
      if !d.isEmpty then (a, d) :: nodeDiffF n as bs else nodeDiffF n as bs
    else nodeDiffF n ((a, sa) :: as) bs
end
def diff (a b : PSet) : PSet := diffF (a.weight + b.weight + 1) a b

mutual
/-- `Set.RecursiveDifference`, with fuel. -/
def rdiffF : Nat → PSet → PSet → PSet
  | 0, _, _ => empty
  | n + 1, .mk m1 c1, .mk m2 c2 =>
    .mk (pesDiff (m1.length + m2.length + 1) m1 m2) (nodeRdiffF n m2 c1 c2)
/-- `SetNodeMap.RecursiveDifference(s2)`'s loop (`m2`: `s2.Members`). -/
def nodeRdiffF : Nat → List PE → List (PE × PSet) → List (PE × PSet) → List (PE × PSet)
  | 0, _, _, _ => []
  | _ + 1, m2, as, [] => as.filter (fun (a, _) => !pesHas a m2)
  | _ + 1, _, [], _ => []
  | n + 1, m2, (a, sa) :: as, (b, sb) :: bs =>
    if a.less b then
      if !pesHas a m2 then (a, sa) :: nodeRdiffF n m2 as ((b, sb) :: bs)
      else nodeRdiffF n m2 as ((b, sb) :: bs)
    else if !(b.less a) then
      if !pesHas a m2 then
        let d := rdiffF n sa sb
        if !d.isEmpty then (a, d) :: nodeRdiffF n m2 as bs else nodeRdiffF n m2 as bs
      else nodeRdiffF n m2 as bs
    else nodeRdiffF n m2 ((a, sa) :: as) bs
end
def rdiff (a b : PSet) : PSet := rdiffF (a.weight + b.weight + 1) a b

mutual
/-- `Set.EnsureNamedFieldsAreMembers`. -/
def ensureNamed (sc : Schema) (tr : TypeRef) : PSet → PSet
  | .mk ms cs =>
    let atom := (sc.resolve tr).getD (.mk none .none .none)
    let ms' := cs.foldl (fun acc (pe, _) =>
      match pe, atom.map with
      | .field n, some m => if (m.findField n).isSome then pesInsert pe acc else acc
      | _, _ => acc) ms
    .mk ms' (ensureNamedL sc atom cs)
/-- `SetNodeMap.EnsureNamedFieldsAreMembers`. -/
def ensureNamedL (sc : Schema) (atom : Atom) : List (PE × PSet) → List (PE × PSet)
  | [] => []
  | (pe, s) :: cs =>
    let tr : TypeRef :=
      match pe, atom.map, atom.list with
      | .field n, some m, _ => match m.findField n with | some f => f.type | none => m.elementType
      | .key _, none, some l => l.elementType
      | .key _, some _, some l => l.elementType
      | _, _, _ => default
    (pe, ensureNamed sc tr s) :: ensureNamedL sc atom cs
end

mutual
/-- `Set.Iterate`: the members' paths, then the children's. -/
def paths (pre : Path) : PSet → List Path
  | .mk ms cs => ms.map (fun pe => pre ++ [pe]) ++ pathsL pre cs
def pathsL (pre : Path) : List (PE × PSet) → List Path
  | [] => []
  | (pe, s) :: cs => paths (pre ++ [pe]) s ++ pathsL pre cs
end
end PSet

/-! ### `ManagedFields` -/

/-- A `fieldpath.VersionedSet` (a `versionedSet`). -/
structure VSet where
  set : PSet
  version : GoString
  applied : Bool
  deriving Inhabited

/-- `fieldpath.ManagedFields`: a Go map, kept sorted by manager. -/
abbrev MF := List (GoString × VSet)

/-- `ManagedFields.Equals`. -/
def mfEquals (l r : MF) : Bool :=
  l.length == r.length &&
    l.all (fun (m, lv) => match lookupKV m r with
      | some rv => decide (lv.version = rv.version) && lv.applied == rv.applied && lv.set.equals rv.set
      | none => false)

end smd
end EtcdGrove
end Perennial
