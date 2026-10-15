/- Port of election_proof/proof_ProgressTracker__Visit.v.

Lean notes: Rocq's `wp_if_join` is `wp_join`; Rocq's lemma `wp_visit` is inlined in the
theorem. `cfg` stays nameable inside the `wp_for` (Rocq loses the section variable), so the
facts about it need not travel in the invariant. The range variable is `id` (allocated
before the loop), Rocq's `cur`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.slices.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

private theorem drop_set_self {α : Type} (l : List α) (k : Nat) (a : α) (hk : k < l.length) :
    (l.set k a).drop k = a :: l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k => simp only [List.set_cons_succ, List.drop_succ_cons]; exact ih k (by simp at hk; omega)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The body, as Goose translates it (`Code/go_etcd_io/raft/v3/tracker.lean`,
`ProgressTracker.Visit.impl`):

    n := len(p.Progress)
    var sl [7]uint64
    var ids []uint64
    if len(sl) >= n { ids = sl[:n] } else { ids = make([]uint64, n) }
    for id := range p.Progress { n--; ids[n] = id }
    slices.Sort(ids)
    for _, id := range ids { f(id, p.Progress[id]) }

Three phases. The `if` is joined (`wp_join`) at "`ids` is a slice of `n` slots": on the
fast path it aliases the stack array (`slice_array` + `ownSlice_split_all` give the
`sl[:n]` prefix), on the slow path `wp_slice_make2`. The map range fills the slots from
the back; its invariant says the last `i` slots hold the first `i` enumerated keys,
reversed, so at the end `ids` is `keys.reverse`. `slices.Sort` permutes it. The slice
range then lends `trk ↦ tv`, one `ownProgress` together with the accessor wand back to
the whole tracker (`ownTracker_lookup`) and `I` to the closure for every entry; every
entry is a key of `prs`, which is what makes the `p.Progress[id]` lookup hit.

The loop invariant carries `ownTracker` *whole*: the closure gives the tracker back
rather than the `Progress`, so the split is redone each iteration by
`ownTracker_lookup`, which can because the progress map is held read-only and so
survives the closure call as a persistent hypothesis -- which is exactly what pins `prs`
across a rebuild of the tracker. -/
theorem tracker.ProgressTracker.Visit.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG) := by
  intro c trk tv t f I
  obtain ⟨votes, prs, pvs⟩ := t
  wp_start as ⟨Htrk, Hown, HI, #Hf⟩
  iunfold ownTrackerC at Hown
  iNamed Hown
  dsimp only at *
  wp_auto
  -- `n := len(p.Progress)`
  wp_apply wp_ProgressMap_len $$ Hprs as -
  have Hsz62 : (GMap.size prs : Int) ≤ 2 ^ 62 := Hsize
  have Hsz : (GMap.size prs : Int) < 2 ^ 63 := by omega
  wp_join iprop(∃ (sl : GoSlice) (xs : List w64),
      "n" ∷ n_ptr ↦ W64 (GMap.size prs) ∗
      "ids" ∷ ids_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* xs ∗
      "%Hxs_len" ∷ ⌜xs.length = GMap.size prs⌝) with [n ids sl]
  · -- fast path: `ids = sl[:n]` aliases the stack array
    rw [ite_eq_left (by word)]
    wp_auto
    ihave Hsl := slice_array (V := w64) sl_ptr 7 _ (by decide) $$ sl
    icases (ownSlice_split_all (W64 (GMap.size prs)) _ _ _ (by simp only; word)).1 $$ Hsl
      with ⟨Hsl, -⟩
    wp_join_done
    iexists _, _
    iframe n ids
    unfold slice.slice sliceIndexRef
    simp only [named]
    iframe Hsl
    ipureintro
    rw [show (zero_val (GoArray w64 7)).arr = List.replicate 7 (zero_val w64) from rfl,
      List.length_take, List.length_replicate]
    word
  · -- slow path: `ids = make([]uint64, n)`
    wp_apply wp_slice_make2 (V := w64) (t := go.uint64) (W64 (GMap.size prs)) $$ [] as
      %sl ⟨Hsl, -⟩
    · ipureintro; word
    wp_join_done
    iexists _, _
    simp only [named]
    iframe
    ipureintro
    rw [List.length_replicate]; word
  iintro ⟨%sl, %xs, H⟩
  iNamed H
  wp_auto
  ihave %Hsl_len := ownSlice_len _ _ _ $$ Hsl
  have Hsllen : sint.Z sl.len = (GMap.size prs : Int) := by
    obtain ⟨H1, H2⟩ := Hsl_len; rw [Hxs_len] at H1; word
  -- The map range fills `ids` from the back: after `i` iterations the last `i` slots
  -- hold the first `i` keys, reversed. `0 ≤ i` has to be in the invariant (the body
  -- is quantified over every `i` whose lookup succeeds), and `id` -- assigned on
  -- every iteration -- inside it.
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (xs' : List w64) (x : w64),
      "%Hi" ∷ ⌜0 ≤ i ∧ i ≤ (GMap.size prs : Int)⌝ ∗
      "n" ∷ n_ptr ↦ W64 ((GMap.size prs : Int) - i) ∗
      "ids" ∷ ids_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* xs' ∗
      "%Hxs'_len" ∷ ⌜xs'.length = GMap.size prs⌝ ∗
      "%Hxs'_suffix" ∷ ⌜xs'.drop ((GMap.size prs : Int) - i).toNat = (keys.take i.toNat).reverse⌝ ∗
      "id" ∷ id_ptr ↦ x)) $$ Hprs
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [n ids Hsl id]
  · iexists xs, zero_val w64
    simp only [Int.sub_zero, Int.toNat_natCast, Int.toNat_zero, List.take_zero, List.reverse_nil]
    iframe
    ipureintro
    refine ⟨⟨Int.le_refl _, by omega⟩, Hxs_len, ?_⟩
    rw [← Hxs_len, List.drop_length]
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    have Hi_lt : i.toNat < keys.length := (List.getElem?_eq_some_iff.1 Hkey).1
    wp_auto
    -- `n--; ids[n] = id`
    have Hn' : W64 ((GMap.size prs : Int) - i) - W64 1 = W64 ((GMap.size prs : Int) - (i + 1)) := by
      word
    have Hn'Z : sint.Z (W64 ((GMap.size prs : Int) - (i + 1))) = (GMap.size prs : Int) - (i + 1) := by
      word
    rw [Hn', ite_eq_left (by rw [Hn'Z]; omega)]
    wp_apply wp_store_slice_index (V := w64) (t := go.uint64) sl _ xs' key $$ [$Hsl] as Hsl
    · ipureintro; rw [Hn'Z]; omega
    rw [Hn'Z]
    unfold forMapPostcondition
    iright
    ileft
    isplitr
    · ipureintro; rfl
    iexists _, key
    simp only [named]
    iframe
    ipureintro
    refine ⟨by omega, by rw [List.length_set]; exact Hxs'_len, ?_⟩
    -- the newly written slot is followed by the slots already filled
    rw [drop_set_self _ _ _ (by omega),
      show ((GMap.size prs : Int) - (i + 1)).toNat + 1 = ((GMap.size prs : Int) - i).toNat by omega,
      Hxs'_suffix, show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
    simp
  -- the range is over: `ids` holds the keys of `prs`, reversed
  iintro HP -
  iNamed HP
  rw [Int.sub_self, Int.toNat_zero, List.drop_zero, ← Hklen, Int.toNat_natCast,
    List.take_length] at Hxs'_suffix
  subst Hxs'_suffix
  wp_auto
  -- `slices.Sort(ids)`: a permutation is all the postcondition needs
  wp_apply wp_slices_Sort $$ [$Hsl] as %ys ⟨Hsl, %Hperm, -⟩
  · ipureintro; simp only [List.length_reverse]; omega
  -- every entry of `ids` is a key of `prs`
  have Hys_dom : ∀ y, y ∈ ys → (prs !! y).isSome := by
    intro y Hy
    exact (Hkset y).1 (List.mem_reverse.1 (Hperm.mem_iff.2 Hy))
  ihave %Hys_len := ownSlice_len _ _ _ $$ Hsl
  have Hys_size : ys.length = GMap.size prs := by
    rw [← Hperm.length_eq, List.length_reverse, Hklen]
  have Hyc : ∀ y, y ∈ ys → y ∈ domSet prs := by
    intro y Hy
    rw [GMap.elem_of_dom']
    exact Hys_dom y Hy
  -- `ids` enumerates exactly the tracked ids: what makes `I`'s visited set end at
  -- `domSet prs`
  have Hysc : GMap.listToSet ys = domSet prs := by
    apply GMap.set_eq; intro y
    rw [GMap.elem_of_list_to_set, GMap.elem_of_dom', ← Hperm.mem_iff,
      List.mem_reverse]
    exact Hkset y
  -- re-seal the tracker: the closure is lent all of it
  ihave Hown := ownTrackerC_intro c tv votes prs pvs Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg
  -- The tracker *value* is part of the invariant: the closure may hand back a
  -- different one (see `visitClosure`, `InvTracker.lean`), and the loop only ever
  -- needs `domSet prs = cfg`, which holds at any of them. The range variable `id` is
  -- written on every iteration, so it lives inside the invariant.
  ihave IH : iprop(∃ (j cv : w64) (tvc : tracker.ProgressTracker) (pvsc : GMap w64 Progress),
      "i" ∷ i_ptr ↦ j ∗
      "id" ∷ id_ptr ↦ cv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (ys.length : Int)⌝ ∗
      "Htrk" ∷ trk ↦ tvc ∗
      "HI" ∷ I (GMap.listToSet (ys.take (sint.Z j).toNat)) pvsc ∗
      "Hown" ∷ ownTrackerC c tvc ⟨votes, prs, pvsc⟩ ∗
      "Hsl" ∷ sl ↦* ys) $$ [i id Htrk HI Hown Hsl]
  · iexists W64 0, zero_val w64, tv, pvs
    simp only [named]
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · -- another id to visit: `f(id, p.Progress[id])`
    obtain ⟨y, Hy⟩ : ∃ y, ys[(sint.Z j).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have Hycfg : y ∈ domSet prs := Hyc y (List.mem_of_getElem? Hy)
    rw [ite_eq_left (by word)]
    wp_apply wp_load_slice_index (V := w64) (t := go.uint64) sl (sint.Z j) ys (DFrac.own 1) y
      (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hy
    -- the progress map's points-to at the tracker value the loop currently holds;
    -- the map itself is `prs` at every one of them
    icases ownTrackerC_progress_map c tvc _ $$ Hown with ⟨#Hprsc, %Hdomc, Hown⟩
    obtain ⟨prc, Hprc⟩ : ∃ prc, prs !! y = some prc := by
      rw [GMap.elem_of_dom] at Hycfg; exact Hycfg
    wp_apply wp_map_lookup1 $$ Hprsc as -
    rw [Hprc, Option.getD_some]
    icases ownTrackerC_pure c tvc _ $$ Hown with ⟨%Hpc, Hown⟩
    have HmaxIc := Hpc.2.2.2.2
    icases ownTrackerC_lookup c tvc ⟨votes, prs, pvsc⟩ y prc Hprc $$ Hown
      with ⟨%p, %Hpv, Hpr, Hback⟩
    iunfold visitClosureC at Hf
    wp_apply Hf $$ %y %prc %tvc %pvsc %p %(GMap.listToSet (ys.take (sint.Z j).toNat))
        [Htrk Hpr Hback HI] as ⟨%tv2, %pvs2, Htrk, Hown, HI⟩
    · iframe Htrk Hpr Hback HI
      ipureintro
      exact ⟨Hycfg, Hprc, Hpv, HmaxIc⟩
    have HD : ({[y]} ∪ GMap.listToSet (ys.take (sint.Z j).toNat) : GSet w64) =
        GMap.listToSet (ys.take (sint.Z (j + W64 1)).toNat) := by
      rw [show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 by word, List.take_add_one, Hy]
      apply GMap.set_eq; intro z
      rw [GMap.elem_of_union, GMap.elem_of_singleton, GMap.elem_of_list_to_set,
        GMap.elem_of_list_to_set]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton]
      exact Or.comm
    rw [HD]
    wp_for_post
    iframe
    iexists _, _, tv2, pvs2
    simp only [named]
    iframe
    ipureintro
    word
  · -- every id visited
    iapply HΦ
    iexists tvc, pvsc
    iframe Htrk Hown
    rw [List.take_of_length_le (by word), Hysc]
    iexact HI

end proof

end EtcdGrove
end Perennial
