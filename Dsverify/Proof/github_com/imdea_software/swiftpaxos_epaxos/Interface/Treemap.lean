/-
**Hypotheses: gods' treemap** as the `state` package uses it (`treemap.NewWith(KeyComparator)`,
`Put`, `Get`, and for `SCAN`: `Select`, `Iterator`, `Iterator.Next`, `Iterator.Value`), over
`state.Key` keys and `state.Value` values (notes/dsv-epaxos.md, "Hypotheses").

The translated gods (v1.18.1, `Dsverify/Code/github_com/emirpasic/gods/**`) is real, but nothing
proves it here (and its red-black tree iterator's `Next`/`Prev` are names only: `goto`); the lab
proved a cut-down copy instead. The coordinator's rule (2026-11-23): take treemap's specs as
hypotheses until the gods model (dsv-tpmodels) lands. So the class `TreemapHyp GF` (a `Prop`-free
structure of predicates and `Prop` specs; every theorem that uses the treemap takes it as an
instance) holds the representation predicates, abstract, and the specs named after the lab's
(`treemap.NewWith.spec`, `treemap.Map.Put.spec`, `treemap.Map.Get.spec`; the lab's
`Proof/wire/State/TreemapIter.lean` for the scan's).

* `isTreeMap m M`: the map `m` (made by `NewWith(KeyComparator)`) maps each key of `M` to the
  `state.Value` slice `M` gives it.
* `iterVal v es`: the iterator value `v` (`Map.Iterator()`'s result) over the entries `es`, in
  increasing (signed) key order (`sortedEntries`), before its first `Next`; stored at `p`, it is
  `ownIter p es none` (`iter_alloc`).
* `ownIter p rest cur`: the iterator at `p`, at entry `cur` (none before the first `Next`), with
  `rest` still to visit.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.state.Base
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The entries `es` are `M`'s, in increasing signed key order. -/
def sortedEntries (M : GMap w64 GoSlice) (es : List (w64 × GoSlice)) : Prop :=
  (es.map Prod.fst).Pairwise (fun a b => sint.Z a < sint.Z b) ∧
    ∀ k sl, (k, sl) ∈ es ↔ M.lookup k = some sl

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]

/-- A key as `KeyComparator` sees it (an `interface{}` holding a `state.Key`). -/
def keyIface (k : w64) : GoInterface := interface.mkOk state.Key.ty #k

/-- A value as the store holds it (an `interface{}` holding a `state.Value`). -/
def valIface (sl : GoSlice) : GoInterface := interface.mkOk state.Value.ty #sl

open github_com.emirpasic.gods.maps.treemap in
/-- **Hypothesis** (the file header): gods' treemap, as `state` uses it. -/
class TreemapHyp (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics]
    [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] where
  isTreeMap : Loc → GMap w64 GoSlice → IProp GF
  iterVal : Iterator → List (w64 × GoSlice) → IProp GF
  ownIter : Loc → List (w64 × GoSlice) → Option (w64 × GoSlice) → IProp GF
  /-- `treemap.NewWith(state.KeyComparator)`: an empty map. -/
  NewWith_spec :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state }}
      (App (Val (@! NewWith)) (Val (@! state.KeyComparator)))
    {{ (m : Loc), RET #m; isTreeMap m ∅ }}
  /-- `m.Put(k, v)` with a `state.Key` and a `state.Value`. -/
  Put_spec : ∀ (m : Loc) (M : GMap w64 GoSlice) (k : w64) (sl : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
        isTreeMap m M }}
      (App (App (Val (m @!! go.GoType.PointerType Map.ty @!! go!"Put")) (Val #(keyIface k)))
        (Val #(valIface sl)))
    {{ RET #(); isTreeMap m (M.insert k sl) }}
  /-- `m.Get(k)` with a `state.Key`: the value and `true` if present, `nil` and `false`
  otherwise. -/
  Get_spec : ∀ (m : Loc) (M : GMap w64 GoSlice) (k : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
        isTreeMap m M }}
      (App (Val (m @!! go.GoType.PointerType Map.ty @!! go!"Get")) (Val #(keyIface k)))
    {{ (v : GoInterface) (ok : Bool), RET (PairV #v #ok); isTreeMap m M ∗
        ⌜match M.lookup k with
          | some sl => v = valIface sl ∧ ok = true
          | none => v = interface.nil ∧ ok = false⌝ }}
  /-- `m.Select(f)` with a function `f` that, from `R`, answers `P k` for a key `k` (and any
  value), keeping `R`: a new map of the entries whose keys satisfy `P`; `m` unchanged. -/
  Select_spec : ∀ (m : Loc) (M : GMap w64 GoSlice) (f : GoFunc) (P : w64 → Bool) (R : IProp GF),
    (∀ (k : w64) (sl : GoSlice),
      {{ R }} (App (App (Val #f) (Val #(keyIface k))) (Val #(valIface sl))) {{ RET #(P k); R }}) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        isTreeMap m M ∗ R }}
      (App (Val (m @!! go.GoType.PointerType Map.ty @!! go!"Select")) (Val #f))
    {{ (m' : Loc), RET #m'; isTreeMap m M ∗ R ∗
        ∃ M' : GMap w64 GoSlice, isTreeMap m' M' ∗
          ⌜∀ k, M'.lookup k = if P k then M.lookup k else none⌝ }}
  /-- `m.Iterator()`: an iterator over `M`'s entries in key order (consuming the map's
  representation: `state` iterates a map it then drops). -/
  Iterator_spec : ∀ (m : Loc) (M : GMap w64 GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        isTreeMap m M }}
      (App (Val (m @!! go.GoType.PointerType Map.ty @!! go!"Iterator")) (Val #()))
    {{ (v : Iterator), RET #v; ∃ es, ⌜sortedEntries M es⌝ ∗ iterVal v es }}
  /-- An iterator value stored at `p` is the iterator at `p`, before its first entry. -/
  iter_alloc : ∀ (p : Loc) (v : Iterator) (es : List (w64 × GoSlice)),
    p ↦ v ∗ iterVal v es ⊢ ownIter p es none
  /-- `it.Next()`: the next entry, if any. -/
  Next_spec : ∀ (p : Loc) (rest : List (w64 × GoSlice)) (cur : Option (w64 × GoSlice)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        ownIter p rest cur }}
      (App (Val (p @!! go.GoType.PointerType Iterator.ty @!! go!"Next")) (Val #()))
    {{ (b : Bool), RET #b;
        match rest with
        | [] => ⌜b = false⌝ ∗ ownIter p [] none
        | e :: r => ⌜b = true⌝ ∗ ownIter p r (some e) }}
  /-- `it.Value()` at entry `(k, sl)`: the value. -/
  Value_spec : ∀ (p : Loc) (rest : List (w64 × GoSlice)) (k : w64) (sl : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        ownIter p rest (some (k, sl)) }}
      (App (Val (p @!! go.GoType.PointerType Iterator.ty @!! go!"Value")) (Val #()))
    {{ RET #(valIface sl); ownIter p rest (some (k, sl)) }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
