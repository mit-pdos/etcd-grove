/-
**`fieldpath`'s vocabulary beyond `Defs.lean`**: what the per-function specs of the package's
internal operations and of its smaller cross-package types (the sorted `PathElementSet`, the
`PathElementMap`s, a set's two halves, paths lent for a call) are written in, and the laws stating
what they mean (`def <name>.law : Prop`, proved after the freeze: the next phase's invariant work;
none is proved yet). Draft (2026-11-19, notes/smd-plan.md, "The call DAG", the `fieldpath` rows).

- **The order of path elements.** `PE.compare` (`Defs.lean`) is SMD's `PathElement.Compare`, the
  order of every sorted slice of the package. On well-formed elements (`PE.wf`: the values in a key
  or a set item are canonical, as `isPE` guarantees, `isPE_wf`) it is a strict total order whose
  zero is equality (`PE.compare_eq_zero`, `PE.compare_antisymm`, `PE.compare_trans`), so a sorted
  list is determined by its members (`PE.sorted_ext`): the sorted-slice invariants and
  `slices.BinarySearchFunc`'s monotonicity premise rest on these. They reduce to the same facts of
  `UVal.compare` (the `value` package's, on canonical values; requested there).
- **Cardinality.** `FSet.HasCard s n` (`s` has `n` members) and `FSet.CardLt s b` (every count of
  `s` is below `b`): the size premises of the operations whose model overflows a 64-bit counter
  (`slices.Insert`'s length bound, `SetNodeMap.Size`'s sum, `make`'s capacity in
  `EnsureNamedFieldsAreMembers`). Real Go runs out of memory long before; the model does not.
- **A set's halves.** `PathSet.tops` (the members: one-element paths), `PathSet.deep` (the paths of
  two or more elements: the children), `PathSet.heads` (the children's elements), with
  `PathSet.under` (`Defs.lean`): `isSet_split` gives a client reading a set's fields
  (`typed`'s `ReconcileFieldSetWithSchema` reads `element.Members`/`element.Children`) a
  `PathElementSet` of `tops` and a `SetNodeMap` of `deep`. `PathSet.rdiff` is
  `RecursiveDifference`, `PathSet.prepend` a prefix put before every path.
- **Representation.** `isPEs` (a list of `PathElement` values, persistent), `isPathF` (a `Path`
  slice lent at a fraction: the walkers' reused paths, `Iterate`'s argument); `isPESetV`/`isPESet`
  (a `PathElementSet` at a fraction) and `ownPESetV`/`ownPESet` (owned, with capacity: `typed`'s
  `seen`/`observedKeys`), over `FSet PE`; `ownPEMapV`/`ownPEMap` (`PathElementMap`) and
  `ownPEVMapV`/`ownPEVMap` (`PathElementValueMap`), over a finite map `PEMap`; `isNodesV`/`isNodes`
  (a set's `SetNodeMap`, persistent, over its deep paths); `ownNodesT` (an owned `SetNodeMap` over
  a raw trie, not canonical: `Set.Insert`'s descent). The value-level predicates are sealed; the
  location-level ones are `∃ v, l ↦ v ∗ …V v` (exposed: a client folds them after storing a
  returned struct).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## The order of path elements -/

/-- A well-formed path element: the values it holds are canonical (`isPE_wf`). -/
def PE.wf : PE → Bool
  | .key fl => fl.all (fun f => f.2.canon)
  | .value v => v.canon
  | _ => true

/-- `a` before `b` (`PathElement.Less`). -/
def PE.lt (a b : PE) : Prop := PE.compare a b < 0

instance (a b : PE) : Decidable (PE.lt a b) := inferInstanceAs (Decidable (PE.compare a b < 0))

/-- Strictly sorted by `PE.compare` (a `PathElementSet`'s members, a `SetNodeMap`'s keys). -/
def PE.Sorted (xs : List PE) : Prop := xs.Pairwise PE.lt

/-! ## Cardinality -/

/-- `s` has exactly `n` members. -/
def FSet.HasCard {α : Type} (s : FSet α) (n : Nat) : Prop :=
  ∃ l : List α, l.Nodup ∧ FSet.ofList l = s ∧ l.length = n

/-- Fewer than `b` members (decided: `FSet.card`, the integration's form, 2026-11-19; it was
"every count of `s` is below `b`", equivalent by `FSet.hasCard_card`). -/
def FSet.CardLt {α : Type} [DecidableEq α] (s : FSet α) (b : Nat) : Prop := s.card < b

instance {α : Type} [DecidableEq α] (s : FSet α) (b : Nat) : Decidable (s.CardLt b) :=
  inferInstanceAs (Decidable (s.card < b))

/-! ## Paths and sets of paths -/

/-- The non-empty prefixes of a path, itself included. -/
def Path.nePrefixes (q : Path) : List Path := (List.range q.length).map (fun k => q.take (k + 1))

namespace PathSet
/-- The one-element paths' elements: a set's `Members`. -/
def tops (S : PathSet) : FSet PE := FSet.bind (fun q => match q with | [e] => [e] | _ => []) S
/-- The paths of two or more elements: what a set's `Children` hold. -/
def deep (S : PathSet) : PathSet := FSet.filter (fun q => decide (2 ≤ q.length)) S
/-- The first elements of the paths of two or more elements: a set's children's keys. -/
def heads (S : PathSet) : FSet PE :=
  FSet.bind (fun q => match q with | e :: _ :: _ => [e] | _ => []) S
/-- The paths with no non-empty prefix (themselves included) in `B` (`Set.RecursiveDifference`). -/
def rdiff (A B : PathSet) : PathSet :=
  FSet.filter (fun q => !(q.nePrefixes.any (fun r => FSet.mem B r))) A
/-- `pre` put before every path (`iteratePrefix`'s paths). -/
def prepend (pre : Path) (S : PathSet) : PathSet := FSet.map (fun q => pre ++ q) S
/-- **The nodes of a set's trie**: every non-empty prefix of its paths (D9's measure of a managed
set: `inputsSmall`, `merge/Defs.lean`; `ensureNamed` adds only such prefixes). -/
def nodes (S : PathSet) : PathSet := FSet.bind Path.nePrefixes S
end PathSet

/-! ## Finite maps keyed by path elements (`PathElementMap`, `PathElementValueMap`) -/

/-- A finite map from path elements (finite by construction: `PEMap.HasCard`). -/
abbrev PEMap (α : Type) := PE → Option α

namespace PEMap
variable {α : Type}
def empty : PEMap α := fun _ => none
/-- `m[k] = v`. -/
def insert (M : PEMap α) (k : PE) (v : α) : PEMap α := fun k' => if k' = k then some v else M k'
/-- `M` has exactly `n` keys. -/
def HasCard (M : PEMap α) (n : Nat) : Prop :=
  ∃ l : List PE, l.Nodup ∧ (∀ k, k ∈ l ↔ (M k).isSome) ∧ l.length = n
/-- Fewer than `b` keys. -/
def CardLt (M : PEMap α) (b : Nat) : Prop := ∀ n, M.HasCard n → n < b
end PEMap

/-! ## A raw trie's children (`SetNodeMap.Descend`, internal) -/

/-- The child at `pe`. -/
def nodesLookup (pe : PE) : List (PE × Trie) → Option Trie
  | [] => none
  | (e, t) :: cs => if e = pe then some t else nodesLookup pe cs

/-- The child at `pe` set to `t`: replaced, or inserted in `PE.compare`'s order. -/
def nodesSet (pe : PE) (t : Trie) : List (PE × Trie) → List (PE × Trie)
  | [] => [(pe, t)]
  | (e, t') :: cs =>
    if e = pe then (pe, t) :: cs
    else if PE.compare pe e < 0 then (pe, t) :: (e, t') :: cs
    else (e, t') :: nodesSet pe t cs

/-- The empty trie (`&Set{}`). -/
def Trie.empty : Trie := .mk [] []

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`isPEs es p`**: the `PathElement` values `es` are the path `p` (persistent). -/
@[no_expose] def isPEs (es : List fieldpath.PathElement) (p : Path) : IProp GF := isPEL es p

/-- **`isPathF s dq p`**: the `Path` slice `s`, its elements at fraction `dq`, holds `p`: a path
lent for a call (a walker's path, reused after; `Set.Iterate`'s argument). `isPath s p` is its
instance at the discarded fraction (`isPath_isPathF`). -/
def isPathF (s : GoSlice) (dq : DFrac) (p : Path) : IProp GF :=
  iprop(∃ es : List fieldpath.PathElement, s ↦*{dq} es ∗ isPEs es p)

/-- A `PathElementSet` value whose `members` slice, at fraction `dq`, holds the set `S`, strictly
sorted (internal: sealed). -/
@[no_expose] def isPESetV (v : fieldpath.PathElementSet) (dq : DFrac) (S : FSet PE) : IProp GF :=
  iprop(∃ (es : List fieldpath.PathElement) (xs : List PE),
    v.members' ↦*{dq} es ∗ isPEL es xs ∗ ⌜PE.Sorted xs ∧ FSet.ofList xs = S⌝)

/-- **`isPESet l dq S`**: the `PathElementSet` at `l`, at fraction `dq`, holds `S` (read-only;
persistent at `DFrac.discard`: a set's members, `isSet_split`). -/
def isPESet (l : Loc) (dq : DFrac) (S : FSet PE) : IProp GF :=
  iprop(∃ v : fieldpath.PathElementSet, l ↦{dq} v ∗ isPESetV v dq S)

/-- An owned `PathElementSet` value holding `S`: its slice and capacity owned (sealed). -/
@[no_expose] def ownPESetV (v : fieldpath.PathElementSet) (S : FSet PE) : IProp GF :=
  iprop(∃ (es : List fieldpath.PathElement) (xs : List PE),
    v.members' ↦* es ∗ ownSliceCap fieldpath.PathElement v.members' (DFrac.own 1) ∗
    isPEL es xs ∗ ⌜PE.Sorted xs ∧ FSet.ofList xs = S⌝)

/-- **`ownPESet l S`**: the `PathElementSet` at `l` holds `S`, owned (`typed`'s local sets:
`MakePathElementSet`'s result stored in a variable), which `PathElementSet.Insert` updates. -/
def ownPESet (l : Loc) (S : FSet PE) : IProp GF :=
  iprop(∃ v : fieldpath.PathElementSet, l ↦ v ∗ ownPESetV v S)

/-- An owned `PathElementMap` value holding `M`: its sorted entries' slice and capacity owned
(sealed). -/
@[no_expose] def ownPEMapV (v : fieldpath.PathElementMap) (M : PEMap GoInterface) : IProp GF :=
  iprop(∃ (ns : List fieldpath.pathElementValue) (xs : List (PE × GoInterface)),
    v.members' ↦* ns ∗ ownSliceCap fieldpath.pathElementValue v.members' (DFrac.own 1) ∗
    isPEL (ns.map (·.PathElement')) (xs.map (·.1)) ∗
    ⌜ns.map (·.Value') = xs.map (·.2) ∧ PE.Sorted (xs.map (·.1)) ∧
      ∀ k, M k = (xs.find? (fun kv => decide (kv.1 = k))).map (·.2)⌝)

/-- **`ownPEMap l M`**: the `PathElementMap` at `l` maps each path element `k` to `M k`, owned. -/
def ownPEMap (l : Loc) (M : PEMap GoInterface) : IProp GF :=
  iprop(∃ v : fieldpath.PathElementMap, l ↦ v ∗ ownPEMapV v M)

/-- A `value.Value` that `PathElementValueMap.Get`'s type assertion accepts: a wrapper built by
`NewValueInterface` (every `isValF`'s; a law of the `value` package gives it from `isValF`). -/
def isValuePtr (x : value.Value) : Prop :=
  ∃ p : Loc, x = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p

/-- An owned `PathElementValueMap` value holding `M` (sealed). -/
@[no_expose] def ownPEVMapV (v : fieldpath.PathElementValueMap) (M : PEMap value.Value) :
    IProp GF :=
  iprop(ownPEMapV v.valueMap' M ∗ ⌜∀ k x, M k = some x → isValuePtr x⌝)

/-- **`ownPEVMap l M`**: the `PathElementValueMap` at `l` maps each `k` to `M k`, owned. -/
def ownPEVMap (l : Loc) (M : PEMap value.Value) : IProp GF :=
  iprop(∃ v : fieldpath.PathElementValueMap, l ↦ v ∗ ownPEVMapV v M)

/-- A set's `SetNodeMap` value holding the deep paths `D` (persistent; sealed): sorted keys, each
child a canonical trie with a path. -/
@[no_expose] def isNodesV (m : fieldpath.SetNodeMap) (D : PathSet) : IProp GF :=
  iprop(∃ (ns : List fieldpath.setNode) (cs : List (PE × Trie)),
    m.members' ↦*{DFrac.discard} ns ∗ trieRepC ns cs ∗
    ⌜PE.Sorted (cs.map (·.1)) ∧ Trie.CanonicalC cs ∧ ∀ q, Trie.pathsC cs q ↔ q ∈ D⌝)

/-- **`isNodes l D`**: the `SetNodeMap` at `l` holds the paths `D` (each of two or more elements:
the children of a set, `isSet_split`; persistent). -/
def isNodes (l : Loc) (D : PathSet) : IProp GF :=
  iprop(∃ m : fieldpath.SetNodeMap, l ↦□ m ∗ isNodesV m D)

/-- **`ownNodesT l cs`**: the `SetNodeMap` at `l` holds the raw children `cs` (any trie, not
necessarily canonical: a set under `Set.Insert`'s descent), owned; internal (sealed). -/
@[no_expose] def ownNodesT (l : Loc) (cs : List (PE × Trie)) : IProp GF :=
  iprop(∃ (m : fieldpath.SetNodeMap) (ns : List fieldpath.setNode),
    l ↦ m ∗ m.members' ↦* ns ∗ ownSliceCap fieldpath.setNode m.members' (DFrac.own 1) ∗
    trieOwnC ns cs)

end own

/-! ## Laws (stated; proved after the freeze) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ### The order (pure) -/

/-- `PathElement.Compare` is zero exactly on equal elements (well-formed ones). -/
def PE.compare_eq_zero.law : Prop :=
  ∀ a b : PE, a.wf = true → b.wf = true → (PE.compare a b = 0 ↔ a = b)

/-- ... and antisymmetric in sign. -/
def PE.compare_antisymm.law : Prop :=
  ∀ a b : PE, a.wf = true → b.wf = true → (PE.compare a b < 0 ↔ 0 < PE.compare b a)

/-- ... and transitive. -/
def PE.compare_trans.law : Prop :=
  ∀ a b c : PE, a.wf = true → b.wf = true → c.wf = true → PE.lt a b → PE.lt b c → PE.lt a c

/-- A strictly sorted list of well-formed elements is determined by its members. -/
def PE.sorted_ext.law : Prop :=
  ∀ xs ys : List PE, (∀ x ∈ xs, x.wf = true) → (∀ y ∈ ys, y.wf = true) →
    PE.Sorted xs → PE.Sorted ys → (∀ x, x ∈ xs ↔ x ∈ ys) → xs = ys

/-! ### Finite sets (pure) -/

def FSet.mem_ofList.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (l : List α) (x : α), x ∈ FSet.ofList l ↔ x ∈ l
def FSet.mem_union.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (a b : FSet α) (x : α), x ∈ FSet.union a b ↔ x ∈ a ∨ x ∈ b
def FSet.mem_inter.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (a b : FSet α) (x : α), x ∈ FSet.inter a b ↔ x ∈ a ∧ x ∈ b
def FSet.mem_diff.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (a b : FSet α) (x : α), x ∈ FSet.diff a b ↔ x ∈ a ∧ x ∉ b
def FSet.mem_filter.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (p : α → Bool) (a : FSet α) (x : α),
    x ∈ FSet.filter p a ↔ x ∈ a ∧ p x = true
def FSet.mem_bind.law : Prop :=
  ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → List β) (a : FSet α) (y : β),
    y ∈ FSet.bind f a ↔ ∃ x, x ∈ a ∧ y ∈ f x
def FSet.isEmpty_iff.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (a : FSet α), a.isEmpty = true ↔ ∀ x, x ∉ a
/-- Every set has a count, and only one. -/
def FSet.hasCard_exists.law : Prop := ∀ {α : Type} (a : FSet α), ∃ n, a.HasCard n
def FSet.hasCard_unique.law : Prop :=
  ∀ {α : Type} (a : FSet α) (n m : Nat), a.HasCard n → a.HasCard m → n = m
/-- The count is zero exactly on the empty set. -/
def FSet.hasCard_zero.law : Prop :=
  ∀ {α : Type} (a : FSet α) (n : Nat), a.HasCard n → (n = 0 ↔ a.isEmpty = true)
/-- `card` is the count (the integration's decided `CardLt`, 2026-11-19). -/
def FSet.hasCard_card.law : Prop := ∀ {α : Type} [DecidableEq α] (a : FSet α), a.HasCard a.card
/-- **`CardLt` is monotone under inclusion** (requested by `fieldpath`'s Draft) and in the bound. -/
def FSet.cardLt_mono.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (a b : FSet α) (n m : Nat), (∀ x, x ∈ a → x ∈ b) → n ≤ m →
    b.CardLt n → a.CardLt m
/-- A union counts at most its two sides. -/
def FSet.card_union.law : Prop :=
  ∀ {α : Type} [DecidableEq α] (a b : FSet α), (FSet.union a b).card ≤ a.card + b.card
/-- A set counts at most its trie's nodes (D9: from the managed sets' bound to their counts). -/
def PathSet.card_nodes.law : Prop := ∀ (S : PathSet), S.card ≤ S.nodes.card

/-! ### Sets of paths (pure) -/

def PathSet.mem_ofList.law : Prop :=
  ∀ (ps : List Path) (q : Path), q ∈ PathSet.ofList ps ↔ q ∈ ps ∧ q ≠ []
def PathSet.mem_tops.law : Prop := ∀ (S : PathSet) (e : PE), e ∈ S.tops ↔ [e] ∈ S
def PathSet.mem_deep.law : Prop := ∀ (S : PathSet) (q : Path), q ∈ S.deep ↔ q ∈ S ∧ 2 ≤ q.length
def PathSet.mem_heads.law : Prop :=
  ∀ (S : PathSet) (e : PE), e ∈ S.heads ↔ ∃ q, q ≠ [] ∧ (e :: q) ∈ S
def PathSet.mem_under.law : Prop :=
  ∀ (S : PathSet) (e : PE) (q : Path), q ∈ S.under e ↔ q ≠ [] ∧ (e :: q) ∈ S
def PathSet.mem_rdiff.law : Prop :=
  ∀ (A B : PathSet) (q : Path), q ∈ PathSet.rdiff A B ↔ q ∈ A ∧ ∀ r ∈ q.nePrefixes, r ∉ B
def PathSet.mem_prepend.law : Prop :=
  ∀ (pre : Path) (S : PathSet) (q : Path), q ∈ PathSet.prepend pre S ↔ ∃ r, r ∈ S ∧ q = pre ++ r

/-! ### Representation -/

def isPE_wf.law : Prop := ∀ e pe, isPE (GF := GF) e pe ⊢ ⌜pe.wf = true⌝
def isPE_agree.law : Prop := ∀ e a b, isPE (GF := GF) e a ∗ isPE e b ⊢ ⌜a = b⌝

def isPEs_persistent.law : Prop := ∀ es p, isPEs (GF := GF) es p ⊢ □ isPEs es p
def isPEs_nil.law : Prop := iprop(True) ⊢ isPEs (GF := GF) [] []
def isPEs_cons.law : Prop :=
  ∀ e es pe p, isPEs (GF := GF) (e :: es) (pe :: p) ⊣⊢ isPE e pe ∗ isPEs es p
def isPEs_app.law : Prop :=
  ∀ es es' p p', es.length = p.length →
    isPEs (GF := GF) (es ++ es') (p ++ p') ⊣⊢ isPEs es p ∗ isPEs es' p'
def isPEs_length.law : Prop := ∀ es p, isPEs (GF := GF) es p ⊢ ⌜es.length = p.length⌝

/-- A persistent path is a path lent at the discarded fraction. -/
def isPath_isPathF.law : Prop := ∀ s p, isPath (GF := GF) s p ⊣⊢ isPathF s DFrac.discard p
/-- A lent path's share can be given up for good. -/
def isPathF_persist.law : Prop := ∀ s dq p, isPathF (GF := GF) s dq p ⊢ |==> isPath s p

/-- A set's two halves: its members and its children (`typed` reads both fields). -/
def isSet_split.law : Prop :=
  ∀ p S, isSet (GF := GF) p S ⊢
    isPESet (p.[fieldpath.Set', go!"Members"]) DFrac.discard S.tops ∗
    isNodes (p.[fieldpath.Set', go!"Children"]) S.deep
/-- No set holds the empty path ("no one owns the entire object"). -/
def isSet_ne.law : Prop := ∀ p S, isSet (GF := GF) p S ⊢ ⌜[] ∉ S⌝
/-- An owned set's paths are non-empty likewise. -/
def ownSet_ne.law : Prop := ∀ p S, ownSet (GF := GF) p S ⊢ ⌜[] ∉ S⌝ ∗ ownSet p S

def isPESetV_persistent.law : Prop :=
  ∀ v S, isPESetV (GF := GF) v DFrac.discard S ⊢ □ isPESetV v DFrac.discard S
def isNodes_persistent.law : Prop := ∀ l D, isNodes (GF := GF) l D ⊢ □ isNodes l D
/-- Reading an owned `PathElementSet`: a share of it, and the way back. -/
def ownPESetV_read.law : Prop :=
  ∀ v S, ownPESetV (GF := GF) v S ⊢
    ∃ dq, isPESetV v dq S ∗ (isPESetV v dq S -∗ ownPESetV v S)
/-- An owned `PathElementSet` given up for good. -/
def ownPESetV_persist.law : Prop :=
  ∀ v S, ownPESetV (GF := GF) v S ⊢ |==> isPESetV v DFrac.discard S
/-- The zero `PathElementSet` (`PathElementSet{}`) is the empty set, owned. -/
def ownPESetV_zero.law : Prop :=
  iprop(True) ⊢ ownPESetV (GF := GF) (zero_val fieldpath.PathElementSet) FSet.empty

/-- A finished map of managed fields is handed out persistently (`merge`'s `Apply`/`Update`
result; moved here with `ownMF` at the Draft's integration, 2026-11-19). -/
def ownMF_persist.law : Prop := ∀ m mf, ownMF (GF := GF) m mf ⊢ |==> isMF m mf

/-- `fieldpath.ManagedFields{}`: an owned empty map. -/
def ownMF_empty.law : Prop :=
  ∀ m, m ↦$ (∅ : GMap GoString GoInterface) ⊢ ownMF (GF := GF) m MF.none

/-- **Reading and writing an owned map** (`merge`'s `managers[m]`, `managers[m] = i`,
`delete(managers, m)`, over Perennial's map rules): the map's points-to and its entries' views,
and the way back to any managed fields the new map holds. -/
def ownMF_access.law : Prop :=
  ∀ m mf, ownMF (GF := GF) m mf ⊢ ∃ M : GMap GoString GoInterface, m ↦$ M ∗
    ⌜keysSorted mf = true ∧ ∀ k, (M !! k).isSome = (mf.get k).isSome⌝ ∗
    □ (∀ k i e, ⌜M !! k = some i ∧ mf.get k = some e⌝ -∗ isVSet i e) ∗
    (∀ (M' : GMap GoString GoInterface) (mf' : MF), m ↦$ M' -∗
      ⌜keysSorted mf' = true ∧ ∀ k, (M' !! k).isSome = (mf'.get k).isSome⌝ -∗
      □ (∀ k i e, ⌜M' !! k = some i ∧ mf'.get k = some e⌝ -∗ isVSet i e) -∗ ownMF m mf')

/-- A wrapper is what `PathElementValueMap.Get`'s type assertion accepts (requested by
`fieldpath`'s Draft of `value`). -/
def isValF_isValuePtr.law : Prop := ∀ v dq x, isValF (GF := GF) v dq x ⊢ ⌜isValuePtr v⌝

/-- A `VersionedSet` interface holds a `versionedSet` (a client calling its methods resolves the
dynamic type with this, then uses `versionedSet.Set`/`APIVersion`/`Applied`). -/
def isVSet_concrete.law : Prop :=
  ∀ i e, isVSet (GF := GF) i e ⊢
    ∃ v : fieldpath.versionedSet, ⌜i = interface.mkOk fieldpath.versionedSet.ty #v⌝

end laws

end smd
end EtcdGrove
end Perennial
