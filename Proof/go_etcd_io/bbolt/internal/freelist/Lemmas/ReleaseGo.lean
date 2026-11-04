/-
`releaseRange` and `ReleasePendingPages` as the code computes them (U2, `notes/bbolt-proof-plan.md`).

**Spec defect (`Model/FL.lean`'s `releaseRangeOne`, hence `FLPg.releaseRange` and
`FLPg.releasePending`).** The model keeps a touched pending entry's remaining (id, allocating
transaction) pairs in their original order (a `filter`). Go's `releaseRange` removes a pair by
moving the last one into its place (`txp.ids[i] = txp.ids[len-1]; txp.ids = txp.ids[:len-1]; i--`),
so the remaining pairs come out in another order, and `ownPending`'s exact slices make the frozen
post false (e.g. pairs `[a, b, c]`, `a` released: the code leaves `[c, b]`, the model `[b, c]`).
`srLoop` is the code's loop; `releaseRangeOneGo`, `FLPg.releaseRangeGo`, `FLPg.releasePendingGo`
are the model's definitions with it in place of the `filter` (the freed ids are the model's: they
are sorted into the free ids). `releaseRangeOneGo_perm` relates the two: the same freed ids and
the same kept pairs up to order.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Release

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- A pair's allocating transaction is in `[b, e]` (`releaseRange`'s inner test). -/
def inRR (b e : w64) (x : w64 × w64) : Bool := decide (b.toNat ≤ x.2.toNat ∧ x.2.toNat ≤ e.toNat)

/-- `releaseRange`'s inner loop from index `j` on the pairs `Q`: the pairs left. -/
def srLoop (b e : w64) (j : Nat) (Q : List (w64 × w64)) : List (w64 × w64) :=
  if h : j < Q.length then
    if inRR b e Q[j] then
      srLoop b e j ((Q.set j (Q[Q.length - 1]'(by omega))).take (Q.length - 1))
    else srLoop b e (j + 1) Q
  else Q
termination_by Q.length - j + Q.length
decreasing_by
  · simp only [List.length_take, List.length_set]; omega
  · omega

theorem srLoop_rm {b e : w64} {j : Nat} {Q : List (w64 × w64)} (h : j < Q.length)
    (hin : inRR b e Q[j] = true) :
    srLoop b e j Q =
      srLoop b e j ((Q.set j (Q[Q.length - 1]'(by omega))).take (Q.length - 1)) := by
  rw [srLoop]; simp only [h, dite_true, hin, ite_true]

theorem srLoop_skip {b e : w64} {j : Nat} {Q : List (w64 × w64)} (h : j < Q.length)
    (hin : inRR b e Q[j] = false) : srLoop b e j Q = srLoop b e (j + 1) Q := by
  rw [srLoop]; simp only [h, dite_true, hin, Bool.false_eq_true, ite_false]

theorem srLoop_end {b e : w64} {j : Nat} {Q : List (w64 × w64)} (h : ¬ j < Q.length) :
    srLoop b e j Q = Q := by
  rw [srLoop]; simp only [h, dite_false]

/-- `l[j] = l[last]; l = l[:last]` and `l[j]`: `l`, up to order. -/
theorem swap_take_perm {α : Type} (l : List α) (j : Nat) (hj : j < l.length) :
    ((l.set j (l[l.length - 1]'(by omega))).take (l.length - 1) ++ [l[j]]).Perm l := by
  obtain ⟨A, x, B, rfl, hA⟩ : ∃ A x B, l = A ++ x :: B ∧ A.length = j :=
    ⟨l.take j, l[j], l.drop (j + 1), by simp, by simp; omega⟩
  subst hA
  rcases List.eq_nil_or_concat B with rfl | ⟨B', y, rfl⟩
  · simp [List.set_append_right, List.take_left']
  · simp only [List.concat_eq_append]
    have hlast : (A ++ x :: (B' ++ [y]))[(A ++ x :: (B' ++ [y])).length - 1]'(by simp) = y := by
      simp [List.getElem_append_right]
    have hj : (A ++ x :: (B' ++ [y]))[A.length]'(by simp) = x := by simp
    rw [hlast, hj, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
    rw [show (A ++ x :: (B' ++ [y])).length - 1 = (A ++ y :: B').length by simp,
      show A ++ y :: (B' ++ [y]) = (A ++ y :: B') ++ [y] by simp, List.take_left]
    rw [List.append_assoc]
    refine List.Perm.append_left A ?_
    exact (List.perm_append_singleton x (y :: B')).trans
      (List.Perm.cons x (List.perm_append_singleton y B').symm)

/-- The loop keeps the pairs allocated outside `[b, e]`, up to order. -/
theorem srLoop_perm (b e : w64) : ∀ (n j : Nat) (Q : List (w64 × w64)),
    Q.length - j + Q.length ≤ n → (∀ x ∈ Q.take j, inRR b e x = false) →
    (srLoop b e j Q).Perm (Q.filter fun x => !inRR b e x)
  | 0, j, Q, hn, h => by
    have : Q = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [srLoop_end (by simp)]; exact List.Perm.refl _
  | n + 1, j, Q, hn, h => by
    by_cases hj : j < Q.length
    · by_cases hin : inRR b e Q[j] = true
      · rw [srLoop_rm hj hin]
        have hsw := swap_take_perm Q j hj
        refine (srLoop_perm b e n j _ (by simp only [List.length_take, List.length_set]; omega)
          ?_).trans ?_
        · intro x hx
          rw [List.take_take, Nat.min_eq_left (by omega), List.take_set_of_le (Nat.le_refl _)] at hx
          exact h x hx
        · have := hsw.filter (fun x => !inRR b e x)
          rw [List.filter_append] at this
          simp only [List.filter_cons, List.filter_nil, hin, Bool.not_true, Bool.false_eq_true,
            ite_false, List.append_nil] at this
          exact this
      · have hin' : inRR b e Q[j] = false := by simpa using hin
        rw [srLoop_skip hj hin']
        refine srLoop_perm b e n (j + 1) Q (by omega) ?_
        intro x hx
        rw [List.take_add_one, List.getElem?_eq_getElem hj] at hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h x hx
        · simp only [Option.toList_some, List.mem_singleton] at hx; subst hx; exact hin'
    · rw [srLoop_end hj]
      rw [List.take_of_length_le (by omega)] at h
      rw [List.filter_eq_self.2 (fun x hx => by rw [h x hx]; rfl)]

/-- `releaseRangeOne` with the code's order of the kept pairs. -/
def releaseRangeOneGo (b e : w64) (p : Pending) : List w64 × Pending :=
  let both := p.ids.zip p.alloctx
  let K := srLoop b e 0 both
  ((both.filter (inRR b e)).map Prod.fst, ⟨K.map Prod.fst, K.map Prod.snd, b⟩)

/-- The code's `releaseRangeOne` and the model's: the same freed ids, the kept pairs up to
order, the same `lastReleaseBegin`. -/
theorem releaseRangeOneGo_perm (b e : w64) (p : Pending) :
    (releaseRangeOneGo b e p).1 = (releaseRangeOne b e p).1 ∧
    ((releaseRangeOneGo b e p).2.ids.zip (releaseRangeOneGo b e p).2.alloctx).Perm
      ((releaseRangeOne b e p).2.ids.zip (releaseRangeOne b e p).2.alloctx) ∧
    (releaseRangeOneGo b e p).2.lastReleaseBegin = (releaseRangeOne b e p).2.lastReleaseBegin := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [releaseRangeOneGo, releaseRangeOne, List.zip_map', inRR]
  have := srLoop_perm b e _ 0 (p.ids.zip p.alloctx) (Nat.le_refl _) (by simp)
  simpa [inRR, List.zip_map'] using this

/-- `FLPg.releaseRange` with the code's order of the kept pairs (`releaseRangeOneGo`). -/
def FLPg.releaseRangeGo (fl : FLPg) (b e : w64) : FLPg :=
  if e.toNat < b.toNat then fl else
  let sel := fun (t : w64) (p : Pending) =>
    decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ p.lastReleaseBegin ≠ b)
  let touched := fl.pending.filter sel
  let freed := touched.toList.flatMap fun kv => (releaseRangeOneGo b e kv.2).1
  let kept := touched.fmap fun p => (releaseRangeOneGo b e p).2
  { fl with
    free := sortPgids (fl.free ++ freed),
    pending := (fl.pending.filter (fun t p => !sel t p)) ∪
      kept.filter (fun _ p => decide (p.ids ≠ [])) }

/-- `FLPg.releasePending` with `FLPg.releaseRangeGo`. -/
def FLPg.releasePendingGo (fl : FLPg) (ro : List w64) : FLPg :=
  let ro := sortPgids ro
  let minid : w64 := (ro.head?).getD (W64 (-1))
  let fl := if 0 < minid.toNat then fl.release (minid - 1) else fl
  let (fl, minid) := ro.foldl (fun (acc : FLPg × w64) t =>
    (acc.1.releaseRangeGo acc.2 (t - 1), t + 1)) (fl, minid)
  fl.releaseRangeGo minid (W64 (-1))

/-! ## The state after the code's `releaseRange` -/

/-- `releaseRange(b, e)` looks at the entry `pd` of `t`. -/
def rrSel (b e t : w64) (pd : Pending) : Bool :=
  decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd.lastReleaseBegin ≠ b)

/-- The entry of `t` after the code's `releaseRange(b, e)`. -/
def rrEntryGo (b e t : w64) (pd : Pending) : Option Pending :=
  if rrSel b e t pd then
    (if (releaseRangeOneGo b e pd).2.ids = [] then none else some (releaseRangeOneGo b e pd).2)
  else some pd

/-- The ids `releaseRange(b, e)` frees of the entry of `t` (none if it is not looked at). -/
def rrRelGo (b e t : w64) (pd : Pending) : List w64 :=
  if rrSel b e t pd then (releaseRangeOneGo b e pd).1 else []

theorem releaseRangeGo_lookup {fl : FLPg} {b e : w64} (hbe : ¬ e.toNat < b.toNat) (k : w64) :
    (fl.releaseRangeGo b e).pending !! k = (fl.pending !! k).bind (rrEntryGo b e k) := by
  unfold FLPg.releaseRangeGo
  rw [if_neg hbe]
  simp only [GMap.lookup_union, lookup_filter', GMap.lookup_fmap]
  cases fl.pending !! k with
  | none => rfl
  | some pd =>
    unfold rrEntryGo rrSel
    by_cases ht : decide (b.toNat ≤ k.toNat ∧ k.toNat ≤ e.toNat ∧ pd.lastReleaseBegin ≠ b) = true
    · have ht' := of_decide_eq_true ht
      by_cases hk : (releaseRangeOneGo b e pd).2.ids = []
      · simp [Option.filter, ht', hk]
      · simp [Option.filter, ht', hk]
    · have ht' : ¬ (b.toNat ≤ k.toNat ∧ k.toNat ≤ e.toNat ∧ pd.lastReleaseBegin ≠ b) := by
        simpa using ht
      simp only [Option.bind_some, ht, Bool.false_eq_true, ite_false]
      simp [Option.filter, ht']

theorem releaseRangeOneGo_ids_perm {pd : Pending} (b e : w64)
    (h : pd.ids.length = pd.alloctx.length) :
    pd.ids.Perm ((releaseRangeOneGo b e pd).1 ++ (releaseRangeOneGo b e pd).2.ids) := by
  have hf : (pd.ids.zip pd.alloctx).map Prod.fst = pd.ids := List.map_fst_zip (by omega)
  have hk := srLoop_perm b e _ 0 (pd.ids.zip pd.alloctx) (Nat.le_refl _) (by simp)
  simp only [releaseRangeOneGo]
  conv => lhs; rw [← hf]
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  exact ((List.filter_append_perm (inRR b e) _).symm.trans
    (List.Perm.append_left _ hk.symm))

theorem releaseRangeOneGo_len (b e : w64) (pd : Pending) :
    (releaseRangeOneGo b e pd).2.ids.length = (releaseRangeOneGo b e pd).2.alloctx.length := by
  simp [releaseRangeOneGo]

/-- Elements contributing nothing can be dropped from a `flatMap`. -/
theorem flatMap_filter_nil {α β : Type} (l : List α) (p : α → Bool) (g : α → List β)
    (h : ∀ a, p a = false → g a = []) : l.flatMap g = (l.filter p).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a = true
    · simp [List.filter_cons, hp, ih]
    · simp [List.filter_cons, hp, ih, h a (by simpa using hp)]

/-- A list gathered over (a superset of) a map's keys, in their order: the same gathered over
the map's bindings. -/
theorem map_flatMap_keys {V : Type} (m : GMap w64 V) (d : V) (f : w64 → V → List w64)
    (keys : List w64) (hk : ∀ k, (m !! k).isSome → k ∈ keys) (hnd : keys.Nodup) :
    (keys.flatMap (fun t => ((m !! t).map (f t)).getD [])).Perm
      (m.toList.flatMap (fun kv => f kv.1 kv.2)) := by
  have hkf : (keys.filter (fun t => (m !! t).isSome)).Nodup := hnd.sublist List.filter_sublist
  have hl : ((keys.filter (fun t => (m !! t).isSome)).map (fun t => (t, (m !! t).getD d))).Perm
      m.toList := by
    refine toList_perm_of (by simpa [List.map_map, Function.comp_def] using hkf) (fun k v => ?_)
    simp only [List.mem_map, List.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨t, ⟨_, ht⟩, rfl, rfl⟩
      cases h : m !! t with
      | none => simp [h] at ht
      | some w => simp
    · intro h
      exact ⟨k, ⟨hk k (by simp [h]), by simp [h]⟩, rfl, by simp [h]⟩
  rw [flatMap_filter_nil keys (fun t => (m !! t).isSome) _
    (fun a ha => by cases h : m !! a <;> simp_all)]
  refine List.Perm.trans ?_ (hl.flatMap_right _)
  rw [List.flatMap_map]
  apply List.Perm.of_eq
  apply flatMap_congr_mem
  intro t ht
  simp only [List.mem_filter] at ht
  cases h : m !! t with
  | none => simp [h] at ht
  | some w => simp

theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap (fun a => f a ++ g a)).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ((List.Perm.append_left _ ih).trans ?_)
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

theorem flatMap_perm_mem {α β : Type} (l : List α) {f g : α → List β}
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (h a (List.mem_cons_self ..))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- After the code's `releaseRange(b, e)`: the entries `G` (`rrEntryGo`), the freed ids `L`
(gathered in the order of the keys), merged into the free ids. -/
theorem releaseRangeGo_ok {fl : FLPg} {b e : w64} {keys L : List w64} {G : GMap w64 Pending}
    (hwf : fl.WF) (hbe : ¬ e.toNat < b.toNat)
    (hk : ∀ k, k ∈ keys ↔ (fl.pending !! k).isSome) (hnd : keys.Nodup)
    (hG : ∀ k, G !! k = (fl.pending !! k).bind (rrEntryGo b e k))
    (hL : L.Perm (keys.flatMap fun t => ((fl.pending !! t).map (rrRelGo b e t)).getD [])) :
    (fl.free ++ L).Nodup ∧ (∀ y ∈ L, 2 ≤ y.toNat) ∧ fl.free.length + L.length < 2 ^ 63 ∧
    (fl.releaseRangeGo b e).free = sortPgids (fl.free ++ L) ∧
    (fl.releaseRangeGo b e).pending = G ∧ (fl.releaseRangeGo b e).allocs = fl.allocs ∧
    (fl.releaseRangeGo b e).WF ∧ (∀ x, x ∈ (fl.releaseRangeGo b e).allIds ↔ x ∈ fl.allIds) := by
  have hGdom : ∀ k, (G !! k).isSome → k ∈ keys := by
    intro k hgk; apply (hk k).2
    rw [hG k] at hgk
    cases h : fl.pending !! k with
    | none => rw [h] at hgk; simp at hgk
    | some _ => simp
  have hper : ∀ t ∈ keys, (((fl.pending !! t).map (fun pd => pd.ids)).getD []).Perm
      (((fl.pending !! t).map (rrRelGo b e t)).getD [] ++
        ((G !! t).map (fun pd => pd.ids)).getD []) := by
    intro t _
    rw [hG t]
    cases h : fl.pending !! t with
    | none => simp
    | some pd =>
      have hl := hwf.2.2.2.2 t pd h
      simp only [Option.map_some, Option.getD_some, Option.bind_some]
      unfold rrRelGo rrEntryGo
      by_cases ht : rrSel b e t pd = true
      · rw [if_pos ht, if_pos ht]
        by_cases hk0 : (releaseRangeOneGo b e pd).2.ids = []
        · rw [if_pos hk0]
          have := releaseRangeOneGo_ids_perm b e hl
          rw [hk0, List.append_nil] at this
          simpa using this
        · rw [if_neg hk0]; simpa using releaseRangeOneGo_ids_perm b e hl
      · rw [if_neg ht, if_neg ht]; simp
  have hFk : ∀ (m : GMap w64 Pending), (∀ k, (m !! k).isSome → k ∈ keys) →
      (keys.flatMap (fun t => ((m !! t).map (fun pd => pd.ids)).getD [])).Perm (flatIds m) :=
    fun m h => map_flatMap_keys m ⟨[], [], 0⟩ (fun _ pd => pd.ids) keys h hnd
  have hpend : fl.pendingIds.Perm (L ++ flatIds G) := by
    rw [pendingIds_eq]
    refine (hFk fl.pending (fun k h => (hk k).2 h)).symm.trans ?_
    refine (flatMap_perm_mem keys hper).trans ((flatMap_append_perm _ _ _).trans ?_)
    exact List.Perm.append hL.symm (hFk G hGdom)
  have hall : fl.allIds.Perm ((fl.free ++ L) ++ flatIds G) := by
    unfold FLPg.allIds; rw [List.append_assoc]; exact List.Perm.append_left _ hpend
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  have hnd' : (fl.free ++ L).Nodup := (List.nodup_append.1 (hall.nodup_iff.1 h1)).1
  have hPend : (fl.releaseRangeGo b e).pending = G := by
    apply GMap.map_eq; intro k; rw [releaseRangeGo_lookup hbe, hG k]
  have hFree : (fl.releaseRangeGo b e).free = sortPgids (fl.free ++ L) := by
    unfold FLPg.releaseRangeGo; rw [if_neg hbe]
    simp only
    apply sortPgids_perm_eq
    refine List.Perm.append_left _ (List.Perm.trans ?_ hL.symm)
    have := map_flatMap_keys (fl.pending.filter (rrSel b e)) ⟨[], [], 0⟩
      (fun _ pd => (releaseRangeOneGo b e pd).1) keys
      (fun k h => (hk k).2 (by rw [lookup_filter'] at h; cases h' : fl.pending !! k <;> simp_all))
      hnd
    refine List.Perm.trans this.symm (List.Perm.of_eq (flatMap_congr_mem fun t _ => ?_))
    rw [lookup_filter']; unfold rrRelGo
    cases fl.pending !! t with
    | none => rfl
    | some pd => by_cases ht : rrSel b e t pd = true <;> simp [Option.filter, ht]
  have hAll : (fl.releaseRangeGo b e).allocs = fl.allocs := by
    unfold FLPg.releaseRangeGo; rw [if_neg hbe]
  have hperm : (fl.releaseRangeGo b e).allIds.Perm fl.allIds := by
    unfold FLPg.allIds FLPg.pendingIds
    rw [hFree, hPend]
    exact (List.Perm.append_right _ (sortPgids_perm _)).trans hall.symm
  refine ⟨hnd', fun y hy => h2 y (hall.mem_iff.2 (List.mem_append_left _ (List.mem_append_right _ hy))),
    by have := hall.length_eq; simp only [List.length_append] at this; omega,
    hFree, hPend, hAll,
    ⟨hperm.nodup_iff.2 h1, fun id hid => h2 id (hperm.mem_iff.1 hid), by rw [hFree]; exact sortPgids_incr hnd',
      by rw [hperm.length_eq]; exact h4, ?_⟩, fun x => hperm.mem_iff⟩
  intro t q hq
  rw [hPend, hG t] at hq
  cases h : fl.pending !! t with
  | none => rw [h] at hq; cases hq
  | some pd =>
    rw [h] at hq
    simp only [Option.bind_some] at hq
    unfold rrEntryGo at hq
    split at hq
    · split at hq
      · cases hq
      · cases hq; exact releaseRangeOneGo_len b e pd
    · cases hq; exact h5 t _ h

theorem releaseRangeGo_empty {fl : FLPg} {b e : w64} (hbe : e.toNat < b.toNat) :
    fl.releaseRangeGo b e = fl := by
  unfold FLPg.releaseRangeGo; rw [if_pos hbe]

end bbolt
end EtcdGrove
end Perennial
