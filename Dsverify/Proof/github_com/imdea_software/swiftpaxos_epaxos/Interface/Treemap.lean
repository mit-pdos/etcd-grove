/-
**gods' treemap** as the `state` package uses it (`treemap.NewWith(KeyComparator)`, `Put`, `Get`,
and for `SCAN`: `Select`, `Iterator`, `Iterator.Next`, `Iterator.Value`), over `state.Key` keys and
`state.Value` values (notes/dsv-epaxos.md, "Hypotheses").

The hypothesis is the shared treemap spec set, `github_com.emirpasic.gods.maps.treemap.Hyps`
(`Dsverify/Spec/github_com/emirpasic/gods/maps/treemap/Specs.lean`: generic in the comparator and
the stored values, the swiftpaxos kit states the same specs). The class `StateTreemap GF` here is
its specialization to `state` (every theorem that uses the treemap takes it as an instance), derived
from it by `StateTreemap.ofGods` with `enc = keyIface`, `cmpOk KeyComparator keyIface`
(`state.keyComparator_cmpOk`, wire/State/KeyComparator.lean) and the stored values `valIface sl`:

* `isTreeMap m M`: the map `m` (made by `NewWith(KeyComparator)`) maps each key of `M` to the
  `state.Value` slice `M` gives it: gods' `isTreeMap m keyIface` of some entries `es` in increasing
  key order (`sortedEntries M es`), their values `valIface sl`.
* `iterVal v es`: the iterator value `v` (`Map.Iterator()`'s result) over the entries `es`, in
  increasing (signed) key order, before its first `Next`; stored at `p`, it is `ownIter p es none`
  (`iter_alloc`).
* `ownIter p rest cur`: the iterator at `p`, at entry `cur` (none before the first `Next`), with
  `rest` still to visit.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.state.Base
public import Dsverify.Spec.github_com.emirpasic.gods.maps.treemap.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

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
/-- gods' treemap, as `state` uses it (the file header): derived from the shared hypothesis
(`StateTreemap.ofGods`). -/
class StateTreemap (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics]
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


/-! ## The specialization, from the shared hypothesis -/

/-- An entry of the store as gods holds it: its value the `state.Value` interface. -/
abbrev valE (e : w64 × GoSlice) : w64 × GoInterface := (e.1, valIface e.2)

open github_com.emirpasic.gods.maps.treemap

theorem putE_valE (es : List (w64 × GoSlice)) (k : w64) (sl : GoSlice) :
    putE (es.map valE) k (valIface sl) = (putE es k sl).map valE :=
  putE_map valIface es k sl

theorem lookupE_valE (es : List (w64 × GoSlice)) (k : w64) :
    lookupE (es.map valE) k = (lookupE es k).map valIface :=
  lookupE_map valIface es k

theorem filter_valE (es : List (w64 × GoSlice)) (P : w64 → Bool) :
    (es.map valE).filter (fun e => P e.1) = (es.filter (fun e => P e.1)).map valE := by
  rw [List.filter_map]; rfl

theorem sortedEntries_sortedE {M : GMap w64 GoSlice} {es : List (w64 × GoSlice)}
    (h : sortedEntries M es) : sortedE es := by
  have h1 := h.1
  rw [List.pairwise_map] at h1
  exact h1

theorem sortedEntries_lookupE {M : GMap w64 GoSlice} {es : List (w64 × GoSlice)}
    (h : sortedEntries M es) (k : w64) : lookupE es k = M.lookup k := by
  apply Option.ext; intro x
  rw [lookupE_some_iff es k x (sortedEntries_sortedE h)]
  exact h.2 k x

theorem sortedEntries_empty : sortedEntries (∅ : GMap w64 GoSlice) [] :=
  ⟨List.Pairwise.nil, fun _ sl =>
    ⟨fun h => (List.not_mem_nil h).elim,
     fun h => nomatch (h : (none : Option GoSlice) = some sl)⟩⟩

theorem sortedEntries_put {M : GMap w64 GoSlice} {es : List (w64 × GoSlice)}
    (h : sortedEntries M es) (k : w64) (sl : GoSlice) :
    sortedEntries (M.insert k sl) (putE es k sl) := by
  have hs := sortedEntries_sortedE h
  refine ⟨by rw [List.pairwise_map]; exact sortedE_putE es k sl hs, fun k' x => ?_⟩
  rw [mem_putE es k sl hs k' x]
  show _ ↔ (if k = k' then some sl else M.lookup k') = some x
  by_cases hk : k' = k
  · subst hk
    simp only [ite_true, true_and, ne_eq, not_true_eq_false, and_false, or_false, Option.some.injEq]
    exact eq_comm
  · rw [if_neg (Ne.symm hk), ← h.2 k' x]
    simp [hk]

theorem lookup_filterP (M : GMap w64 GoSlice) (P : w64 → Bool) (k : w64) :
    (M.filter (fun k _ => P k)).lookup k = if P k then M.lookup k else none := by
  show (M.lookup k).filter (fun _ => P k) = _
  cases M.lookup k <;> by_cases hP : P k <;> simp [hP, Option.filter]

theorem sortedEntries_filter {M : GMap w64 GoSlice} {es : List (w64 × GoSlice)}
    (h : sortedEntries M es) (P : w64 → Bool) :
    sortedEntries (M.filter (fun k _ => P k)) (es.filter (fun e => P e.1)) := by
  refine ⟨by rw [List.pairwise_map]; exact sortedE_filter _ es (sortedEntries_sortedE h),
    fun k x => ?_⟩
  rw [lookup_filterP, List.mem_filter, h.2 k x]
  by_cases hP : P k <;> simp [hP]

/-- `state`'s treemap from the shared hypothesis (the file header): `enc = keyIface`, the
comparator `KeyComparator` (`hcmp`: `state.keyComparator_cmpOk`), the values `valIface sl`. -/
def StateTreemap.ofGods {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
    [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
    (H : github_com.emirpasic.gods.maps.treemap.Hyps GF)
    (hcmp : isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ⊢
      cmpOk (GF := GF) (functions state.KeyComparator []) keyIface) : StateTreemap GF where
  isTreeMap m M := iprop(∃ es, H.isTreeMap m keyIface (es.map valE) ∗ ⌜sortedEntries M es⌝)
  iterVal v es := H.iterVal v (es.map valE)
  ownIter p rest cur := H.ownIter p (rest.map valE) (cur.map valE)
  NewWith_spec := by
    wp_start_folded
    ihave #Hst : isPkgInit (PROP := IProp GF)
        pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state $$ []
    · iPkgInit
    ihave #Hc := hcmp $$ Hst
    wp_apply H.NewWith_spec (functions state.KeyComparator []) keyIface $$ [$Hc] as %m Hm
    iapply HΦ
    iexists []
    simp only [List.map_nil]
    iframe Hm
    ipureintro; exact sortedEntries_empty
  Put_spec := by
    intro m M k sl
    wp_start_folded as ⟨%es, Hm, %Hes⟩
    wp_apply H.Put_spec m keyIface (es.map valE) k (valIface sl) $$ [$Hm] as Hm
    iapply HΦ
    iexists putE es k sl
    rw [← putE_valE]
    iframe Hm
    ipureintro; exact sortedEntries_put Hes k sl
  Get_spec := by
    intro m M k
    wp_start_folded as ⟨%es, Hm, %Hes⟩
    wp_apply H.Get_spec m keyIface (es.map valE) k $$ [$Hm] as Hm
    rw [lookupE_valE, sortedEntries_lookupE Hes k]
    iapply HΦ
    isplitl [Hm]
    · iexists es
      iframe Hm
      ipureintro; exact Hes
    ipureintro
    cases M.lookup k <;> simp
  Select_spec := by
    intro m M f P R hf
    wp_start_folded as ⟨⟨%es, Hm, %Hes⟩, HR⟩
    wp_apply H.Select_spec m keyIface (es.map valE) f P R ?hsel $$ [$Hm $HR]
      as %m' ⟨Hm, HR, Hm'⟩
    case hsel =>
      intro k v hv
      obtain ⟨⟨k0, sl⟩, -, hev⟩ := List.mem_map.mp hv
      simp only [valE, Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact hf k0 sl
    iapply HΦ
    iframe HR
    isplitl [Hm]
    · iexists es
      iframe Hm
      ipureintro; exact Hes
    iexists M.filter (fun k _ => P k)
    isplitl [Hm']
    · iexists es.filter (fun e => P e.1)
      rw [← filter_valE]
      iframe Hm'
      ipureintro; exact sortedEntries_filter Hes P
    ipureintro; exact lookup_filterP M P
  Iterator_spec := by
    intro m M
    wp_start_folded as ⟨%es, Hm, %Hes⟩
    wp_apply H.Iterator_spec m keyIface (es.map valE) $$ [$Hm] as %v Hv
    iapply HΦ
    iexists es
    iframe Hv
    ipureintro; exact Hes
  iter_alloc := fun p v es => H.iter_alloc p v (es.map valE)
  Next_spec := by
    intro p rest cur
    wp_start_folded as Hit
    wp_apply H.Next_spec p (rest.map valE) (cur.map valE) $$ [$Hit] as %b Hb
    iapply HΦ
    irevert Hb
    cases rest <;> simp only [List.map_nil, List.map_cons, Option.map_none, Option.map_some]
    all_goals (try (iintro Hb; iexact Hb))
  Value_spec := by
    intro p rest k sl
    wp_start_folded as Hit
    have hv : Option.map valE (some (k, sl)) = some (k, valIface sl) := rfl
    irevert Hit
    rw [hv]
    iintro Hit
    wp_apply H.Value_spec p (rest.map valE) k (valIface sl) $$ [$Hit] as Hit
    iapply HΦ
    iexact Hit

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
