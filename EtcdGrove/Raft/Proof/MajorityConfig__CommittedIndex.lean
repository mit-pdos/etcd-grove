/- Port of election_proof/proof_MajorityConfig__CommittedIndex.v.

Lean notes: the pure helpers of `proof_MajorityConfig__CommittedIndex_helpers/
committed_index.v` are private lemmas here (`length_omap_le` is `List.length_filterMap_le`,
`length_filter_fmap` is `List.filter_map`, `filter_Forall_id`/`filter_Forall_nil` are
`List.filter_eq_self`/`List.filter_eq_nil_iff`; `insert_replicate_last` is
`set_replicate_last`; `elem_of_filter_set` and `filter_inter_self` are new). `omap` is
`List.filterMap`. Rocq's `go.len_underlying` rewriting is not needed: Perennial's
`wp_map_len` and `pure_wp_map_nil_len` are stated at any type whose underlying type is a
map.
-/
import EtcdGrove.Raft.Spec.MajorityConfig__CommittedIndex
import EtcdGrove.Raft.Spec.slices_Sort

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section helpers

/-- The slice after the fill loop, as a multiset. -/
private theorem fill_perm (f : w64 → Option w64) (l : List w64) :
    l.map (fun v => (f v).getD (W64 0)) ≡ₚ
      List.replicate (l.length - (l.filterMap f).length) (W64 0) ++ (l.filterMap f).reverse := by
  induction l with
  | nil => simp
  | cons x l IH =>
    have Hle := List.length_filterMap_le f l
    cases Hfx : f x with
    | some y =>
      rw [List.map_cons, Hfx, Option.getD_some, List.filterMap_cons, Hfx]
      simp only [List.length_cons, List.reverse_cons, Nat.add_sub_add_right]
      rw [← List.append_assoc]
      exact (IH.cons y).trans (List.perm_append_singleton y _).symm
    | none =>
      rw [List.map_cons, Hfx, Option.getD_none, List.filterMap_cons, Hfx]
      simp only [List.length_cons]
      rw [show l.length + 1 - (l.filterMap f).length = (l.length - (l.filterMap f).length) + 1
        by omega, List.replicate_succ, List.cons_append]
      exact IH.cons _

/-- One step of the fill loop: the last zero slot gets the value. -/
private theorem set_replicate_last {A : Type} (m : Nat) (z a : A) (R : List A) :
    (List.replicate (m + 1) z ++ R).set m a = List.replicate m z ++ a :: R := by
  induction m with
  | zero => simp
  | succ m IH => simp only [List.replicate_succ, List.cons_append, List.set_cons_succ] at IH ⊢; rw [IH]

private theorem elem_of_filter_set (Q : w64 → Prop) [DecidablePred Q] (s : GSet w64) (k : w64) :
    k ∈ GMap.filter (fun v _ => decide (Q v)) s ↔ k ∈ s ∧ Q k := by
  rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_filter]
  cases s !! k <;> simp [Option.filter]

private theorem filter_inter_self (Q : w64 → Prop) [DecidablePred Q] (s : GSet w64) :
    GMap.filter (fun v _ => decide (Q v)) s ∩ s = GMap.filter (fun v _ => decide (Q v)) s := by
  apply GMap.set_eq; intro k
  rw [GMap.elem_of_intersection, elem_of_filter_set]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

/-- How many voters have a value `≥ M`, counted on the sorted slice. -/
private theorem size_filter_sorted (s : GSet w64) (keys : List w64) (g : w64 → w64)
    (ys : List w64) (M : w64) (Hnd : keys.Nodup) (Hks : GMap.listToSet keys = s)
    (Hperm : ys ≡ₚ keys.map g) :
    GMap.size (GMap.filter (fun v _ => decide (uint.Z M ≤ uint.Z (g v))) s) =
      (ys.filter (fun x => decide (uint.Z M ≤ uint.Z x))).length := by
  rw [(Hperm.filter _).length_eq, List.filter_map, List.length_map]
  symm
  apply nsat_size s _ keys (fun v => uint.Z M ≤ uint.Z (g v)) _ _ Hnd Hks
  · intro k _; rw [elem_of_filter_set]; exact ⟨fun h => h.2, fun h => ⟨by assumption, h⟩⟩
  · rw [GMap.elem_of_subseteq]; intro k Hk; exact ((elem_of_filter_set _ _ _).1 Hk).1

private theorem sorted_quorum_index (s : GSet w64) (keys : List w64) (g : w64 → w64)
    (ys : List w64) (N : w64) (Hnd : keys.Nodup) (Hks : GMap.listToSet keys = s)
    (Hlen : keys.length = GMap.size s) (Hpos : 0 < GMap.size s)
    (Hperm : ys ≡ₚ keys.map g)
    (Hsorted : ∀ (i j : Nat) (xi xj : w64), ys[i]? = some xi → ys[j]? = some xj →
      i < j → uint.Z xi ≤ uint.Z xj)
    (HN : ys[GMap.size s - (GMap.size s / 2 + 1)]? = some N) :
    IsQuorumIndex s g N := by
  have Hys : ys.length = GMap.size s := by rw [Hperm.length_eq, List.length_map, Hlen]
  have Hhalf : GMap.size s / 2 + 1 ≤ GMap.size s := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- `N` is some voter's value
    have Hin : N ∈ keys.map g := Hperm.mem_iff.1 (List.mem_of_getElem? HN)
    obtain ⟨k, Hk, rfl⟩ := List.mem_map.1 Hin
    exact ⟨k, by rw [← Hks, GMap.elem_of_list_to_set]; exact Hk, rfl⟩
  · -- the slots from `pos` on are all `≥ N`: `n/2 + 1` of them
    rw [IsQuorum_alt, filter_inter_self, size_filter_sorted s keys g ys N Hnd Hks Hperm,
      ← List.take_append_drop (GMap.size s - (GMap.size s / 2 + 1)) ys, List.filter_append,
      List.length_append]
    rw [(List.filter_eq_self (l := ys.drop (GMap.size s - (GMap.size s / 2 + 1)))).2 ?_]
    · rw [List.length_drop]; omega
    · intro x Hx
      obtain ⟨i, Hi⟩ := List.mem_iff_getElem?.1 Hx
      rw [List.getElem?_drop] at Hi
      simp only [decide_eq_true_eq]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [Nat.add_zero, HN] at Hi; cases Hi; exact Int.le_refl _
      · exact Hsorted _ _ _ _ HN Hi (by omega)
  · -- any larger index: only the slots after `pos` can reach it
    intro N' HN' Hq
    rw [IsQuorum_alt, filter_inter_self, size_filter_sorted s keys g ys N' Hnd Hks Hperm,
      ← List.take_append_drop (GMap.size s - (GMap.size s / 2 + 1) + 1) ys, List.filter_append,
      List.length_append] at Hq
    rw [List.filter_eq_nil_iff.2] at Hq
    · have Hl := List.length_filter_le (fun x => decide (uint.Z N' ≤ uint.Z x))
        (ys.drop (GMap.size s - (GMap.size s / 2 + 1) + 1))
      rw [List.length_drop, Hys] at Hl
      simp only [List.length_nil, Nat.zero_add] at Hq
      omega
    · intro x Hx
      obtain ⟨i, Hi⟩ := List.mem_iff_getElem?.1 Hx
      rw [List.getElem?_take] at Hi
      split at Hi
      · have : uint.Z x ≤ uint.Z N := by
          rcases Nat.lt_or_ge i (GMap.size s - (GMap.size s / 2 + 1)) with h | h
          · exact Hsorted _ _ _ _ Hi HN h
          · rw [show i = GMap.size s - (GMap.size s / 2 + 1) by omega, HN] at Hi
            cases Hi; exact Int.le_refl _
        simp only [decide_eq_true_eq]; omega
      · cases Hi

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The two `len(c) == 0` exits (the nil component, and a real but empty map), then
the main path in four phases: the `if` choosing the stack buffer or a heap slice is
joined at "`srt` is `n` zeros"; the map range fills `srt` from the right (invariant:
after `k` voters, `srt` is `n - J` zeros followed by the `J` acknowledgements among
them, reversed, and `i = n - 1 - J`); `slices.Sort`; the read at `pos = n - (n/2+1)`.
`fill_perm` and `sorted_quorum_index` turn the sorted slice into `IsQuorumIndex`. -/
theorem quorum.MajorityConfig.CommittedIndex.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    quorum.MajorityConfig.CommittedIndex.spec (GF := GF) (hG := hG) := by
  intro cs cref mref l Pres acked
  wp_start as ⟨%Hsz, Hc, Hm, #Hl, HP⟩
  wp_load; wp_pures
  wp_method_call
  wp_call
  wp_call; wp_alloc c_ptr as c; wp_pures; wp_alloc l_ptr as l; wp_pures; wp_load; wp_pures
  icases Hm with (⟨%Hnil, %Hs⟩ | ⟨%ids, %Hids, Hids⟩)
  · -- the nil component: `len(c) == 0`.
    subst Hnil Hs
    wp_pures; wp_alloc n_ptr as n; wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear c l n
    iapply HΦ
    iframe Hc HP
    isplitr
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    ipureintro
    exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
  wp_apply wp_map_len (t := quorum.MajorityConfig.ty) $$ Hids as Hids
  wp_pures; wp_alloc n_ptr as n; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  -- `wp_join` below would substitute `cs := domSet ids` anyway; do it now
  subst Hids
  by_cases Hemp : domSet ids = ∅
  · -- a real but empty map: `len(c) == 0` too
    have Hz : GMap.size ids = 0 := by
      rw [(GMap.dom_empty_iff_L ids).1 Hemp, GMap.map_size_empty]
    rw [Hz]
    wp_pures; iclear c l n
    iapply HΦ
    iframe Hc HP
    isplitl [Hids]
    · iright
      iexists ids
      iframe Hids
      ipureintro; rfl
    ipureintro
    exact ⟨fun _ => rfl, fun h => absurd Hemp h⟩
  have Hpos : 0 < GMap.size ids := by
    rcases Nat.eq_zero_or_pos (GMap.size ids) with h | h
    · exact absurd ((GMap.dom_empty_iff_L ids).2 (GMap.map_size_empty_inv _ h)) Hemp
    · exact h
  have Hsz' : (GMap.size ids : Int) < 2 ^ 63 := by rw [← GMap.size_dom]; exact Hsz
  rw [decide_eq_false (by word)]
  wp_pures; wp_alloc stk_ptr as stk; wp_pures; wp_alloc srt_ptr as srt; wp_pures; wp_load; wp_pures
  iNamed Hl
  subst Hlok
  -- Both arms of the `if` end with `srt` an `n`-slot slice of zeros.
  -- TODO(no-wp-auto): wp_join runs (cont first, then the cases): wp_load; wp_pures | wp_load; wp_pures; iclear stk
  wp_join iprop(∃ (sl : GoSlice) (xs : List w64),
      "n" ∷ n_ptr ↦ W64 (GMap.size ids) ∗
      "srt" ∷ srt_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* xs ∗
      "%Hxs" ∷ ⌜xs = List.replicate (GMap.size ids) (W64 0)⌝) with [n srt stk]
  · -- fast path: `srt = stk[:n]` aliases the stack array
    rw [ite_eq_left (by word)]
    wp_pures; wp_store; wp_pures
    ihave Hsl := slice_array (V := w64) stk_ptr 7 _ (by decide) $$ stk
    icases (ownSlice_split_all (W64 (GMap.size ids)) _ _ _ (by simp only; word)).1 $$ Hsl
      with ⟨Hsl, -⟩
    wp_join_done
    iexists _, _
    iframe n srt
    unfold slice.slice sliceIndexRef
    simp only [named]
    iframe Hsl
    ipureintro
    rw [show (zero_val (GoArray w64 7)).arr = List.replicate 7 (zero_val w64) from rfl,
      List.take_replicate]
    congr 1
    word
  · -- slow path: `srt = make([]uint64, n)`
    wp_apply wp_slice_make2 (V := w64) (t := go.uint64) (W64 (GMap.size ids)) $$ [] as
      %sl ⟨Hsl, -⟩
    · ipureintro; word
    wp_pures; wp_store; wp_pures
    wp_join_done
    iexists _, _
    simp only [named]
    iframe
    ipureintro
    congr 1; word
  iintro ⟨%sl, %xs, H⟩
  iNamed H
  subst Hxs
  wp_pures; wp_load; wp_pures; wp_alloc i_ptr as i; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  wp_alloc id_ptr as id; wp_pures; iclear c
  ihave %Hsl_len := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_replicate] at Hsl_len
  have Hsllen : sint.Z sl.len = (GMap.size ids : Int) := by
    obtain ⟨H1, H2⟩ := Hsl_len; word
  -- The map range fills `srt` from the right: after `k` voters, the acknowledged ones
  -- among them, reversed, occupy the last slots and the rest are still `0`; `i` points
  -- at the last zero.
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (k : Int) => iprop(∃ (idv : w64),
      "%Hk" ∷ ⌜0 ≤ k ∧ k ≤ (GMap.size ids : Int)⌝ ∗
      "srt" ∷ srt_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* (List.replicate (GMap.size ids - ((keys.take k.toNat).filterMap acked).length)
          (W64 0) ++ ((keys.take k.toNat).filterMap acked).reverse) ∗
      "i" ∷ i_ptr ↦ W64 ((GMap.size ids : Int) - 1 - ((keys.take k.toNat).filterMap acked).length) ∗
      "id" ∷ id_ptr ↦ idv ∗
      "l" ∷ l_ptr ↦ GoInterface.ok i ∗
      "HP" ∷ Pres)) $$ Hids
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [srt Hsl i id l HP]
  · iexists zero_val w64
    simp only [Int.toNat_zero, List.take_zero, List.filterMap_nil, List.length_nil,
      Nat.sub_zero, List.reverse_nil, List.append_nil, Int.natCast_zero, Int.sub_zero]
    rw [show W64 ((GMap.size ids : Int) - 1) = W64 (GMap.size ids) - W64 1 by word]
    simp only [named]
    iframe
    ipureintro
    omega
  isplitr
  · imodintro
    iintro %k %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    have Htake : keys.take (k + 1).toNat = keys.take k.toNat ++ [key] := by
      rw [show (k + 1).toNat = k.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hk_lt : k.toNat < keys.length := (List.getElem?_eq_some_iff.1 Hkey).1
    have HJle := List.length_filterMap_le acked (keys.take k.toNat)
    rw [List.length_take] at HJle
    wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures
    -- `l.AckedIndex(id)`; `wp_apply HAckedIndex $$ %key [HP]` does not go through
    ihave Hack := HAckedIndex $$ %key
    wp_bind (App (Val #(methods _ _ _)) (Val #key))
    iapply Hack $$ HP
    imodintro
    iintro HP
    rw [Htake, List.filterMap_append]
    cases Hak : acked key with
    | some a =>
      -- acknowledged: `srt[i] = idx; i--`
      simp only [Option.getD_some, Option.isSome_some, List.filterMap_cons, Hak,
        List.filterMap_nil]
      wp_pures; wp_alloc ok_ptr as ok; wp_pures; wp_alloc idx_ptr as idx; wp_pures; wp_store
      wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_load; wp_pures
      iclear idx ok
      generalize Ho : (keys.take k.toNat).filterMap acked = o at HJle ⊢
      have HJ : o.length < GMap.size ids := by omega
      have HiZ : sint.Z (W64 ((GMap.size ids : Int) - 1 - (o.length : Int))) =
          (GMap.size ids : Int) - 1 - o.length := by word
      rw [ite_eq_left (by rw [HiZ]; omega)]
      wp_apply wp_store_slice_index (V := w64) (t := go.uint64) sl _ _ a $$ [$Hsl] as Hsl
      · ipureintro
        rw [HiZ]
        simp only [List.length_append, List.length_replicate, List.length_reverse]
        omega
      wp_pures; wp_load; wp_pures; wp_store; wp_pures
      rw [HiZ, show ((GMap.size ids : Int) - 1 - o.length).toNat = GMap.size ids - 1 - o.length
        by omega, show GMap.size ids - o.length = (GMap.size ids - 1 - o.length) + 1 by omega,
        set_replicate_last]
      unfold forMapPostcondition
      iright
      ileft
      isplitr
      · ipureintro; rfl
      iexists key
      simp only [named]
      rw [List.length_append, List.reverse_append, List.length_singleton,
        show GMap.size ids - (o.length + 1) = GMap.size ids - 1 - o.length by omega,
        show W64 ((GMap.size ids : Int) - 1 - o.length) - W64 1 =
          W64 ((GMap.size ids : Int) - 1 - ((o.length + 1 : Nat) : Int)) by word]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      iframe
      ipureintro
      omega
    | none =>
      -- not acknowledged: the slot stays `0`
      simp only [Option.getD_none, Option.isSome_none, List.filterMap_cons, Hak,
        List.filterMap_nil, List.append_nil]
      wp_pures; wp_alloc ok_ptr as ok; wp_pures; wp_alloc idx_ptr as idx; wp_pures; wp_store
      wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear idx ok
      unfold forMapPostcondition
      iright
      ileft
      isplitr
      · ipureintro; rfl
      iexists key
      simp only [named]
      iframe
      ipureintro
      omega
  -- the range is over: `srt` holds every acknowledgement, zeros first
  iintro HP Hids
  iNamed HP
  rw [show ((GMap.size ids : Int)).toNat = keys.length by omega, List.take_length]
  wp_pures; wp_load; wp_pures; iclear i id l
  wp_apply wp_slices_Sort $$ [$Hsl] as %ys ⟨Hsl, %Hperm, %Hsorted⟩
  wp_pures; wp_load; wp_load; wp_pures; wp_alloc pos_ptr as pos; wp_pures; wp_store; wp_pures
  wp_load; wp_load; wp_pures; iclear n srt pos
  have Hperm' : ys ≡ₚ keys.map (fun v => (acked v).getD (W64 0)) := by
    have H := fill_perm acked keys
    rw [Hklen] at H
    exact Hperm.symm.trans H.symm
  have Hys_len : ys.length = GMap.size ids := by
    rw [Hperm'.length_eq, List.length_map, Hklen]
  -- `pos := n - (n/2 + 1)`
  have Hhalf : GMap.size ids / 2 + 1 ≤ GMap.size ids := by omega
  have Hposw : sint.Z (W64 (GMap.size ids) -
      (BitVec.sdiv (W64 (GMap.size ids)) (W64 2) + W64 1)) =
      ((GMap.size ids - (GMap.size ids / 2 + 1) : Nat) : Int) := by
    word
  obtain ⟨y, Hy⟩ : ∃ y, ys[GMap.size ids - (GMap.size ids / 2 + 1)]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [Hposw, ite_eq_left (by omega)]
  wp_apply wp_load_slice_index (V := w64) (t := go.uint64) sl _ ys (DFrac.own 1) y (by omega)
    $$ [Hsl] as Hsl
  · iframe; ipureintro; rw [Int.toNat_natCast]; exact Hy
  wp_pures
  have Hks : GMap.listToSet keys = domSet ids := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_list_to_set, Hkset, GMap.elem_of_dom']
    rfl
  iapply HΦ
  iframe Hc HP
  isplitl [Hids]
  · iright; iexists ids; iframe Hids; ipureintro; rfl
  ipureintro
  refine ⟨fun h => absurd h Hemp, fun _ => ?_⟩
  rw [← GMap.size_dom] at Hy Hpos Hklen
  exact sorted_quorum_index (domSet ids) keys _ ys y Hknodup Hks Hklen Hpos Hperm' Hsorted Hy

end proof

end EtcdGrove
end Perennial
