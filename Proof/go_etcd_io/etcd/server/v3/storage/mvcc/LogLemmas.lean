/-
The index as a function of the log (`Model.lean`), key by key: the index built from the events
(`indexOf`) holds, for every key, the key index built from that key's events alone
(`kiOfKey`, `indexOf_rep`); and what that key index answers at a revision is the key-value of
the state at that revision (`kiGet_kiOfKey`, the model's main theorem). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### The index, key by key -/

/-- One event applied to a key's index: `idxApply` seen from the key. A tombstone of a key
whose last generation is empty (or that has no index: `kiEmpty`) changes nothing. -/
def kiApply (ki : KeyIndex) (ev : Ev) : KeyIndex :=
  if ev.tomb then (if kiLastEmpty ki then ki else kiTombstone ki ev.rev) else kiPut ki ev.rev

/-- The key index of `k` after the events `evs`: those of `k`, applied to the empty index. -/
def kiOfKey (evs : List Ev) (k : GoString) : KeyIndex :=
  (evs.filter fun ev => decide (ev.key = k)).foldl kiApply kiEmpty

theorem kiOfKey_nil (k : GoString) : kiOfKey [] k = kiEmpty := rfl

theorem kiOfKey_append (evs : List Ev) (ev : Ev) (k : GoString) :
    kiOfKey (evs ++ [ev]) k = if ev.key = k then kiApply (kiOfKey evs k) ev else kiOfKey evs k := by
  unfold kiOfKey
  rw [List.filter_append, List.foldl_append, List.filter_cons, List.filter_nil]
  by_cases h : ev.key = k
  · simp only [h, decide_true, ↓reduceIte, List.foldl_cons, List.foldl_nil]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, List.foldl_nil]

/-- The index `idx` represents the events `evs`: sorted, and holding each key's index (absent
keys have the empty one). -/
def IdxRep (evs : List Ev) (idx : IndexM) : Prop :=
  idx.Pairwise idxLess ∧ ∀ k, (idxGet idx k).getD kiEmpty = kiOfKey evs k

theorem idxLess_swo : StrictWeakOrder idxLess where
  irrefl a := goStringLt_irrefl a.1
  trans _ _ _ h1 h2 := goStringLt_trans h1 h2
  incomp_trans a b c h1 h2 h3 h4 := by
    have e1 := goStringLt_eq_of_not_lt h1 h2
    have e2 := goStringLt_eq_of_not_lt h3 h4
    unfold idxLess
    rw [e1, e2]
    exact ⟨goStringLt_irrefl _, goStringLt_irrefl _⟩

theorem idxLess_iff (a b : GoString × KeyIndex) : idxLess a b ↔ go.GoStringLt a.1 b.1 := Iff.rfl

/-- `btFind` of a key after `btInsert` of a pair, on a list sorted by key. -/
theorem btFind_btInsert_idx (k' : GoString) (ki : KeyIndex) (k : GoString) (x : KeyIndex) :
    ∀ (idx : IndexM), idx.Pairwise idxLess →
      btFind idxLess (k, x) (btInsert idxLess (k', ki) idx) =
        if k' = k then some (k', ki) else btFind idxLess (k, x) idx
  | [], _ => by
    simp only [btInsert, btFind, idxLess_iff]
    by_cases h1 : go.GoStringLt k' k
    · have : k' ≠ k := fun e => goStringLt_irrefl _ (e ▸ h1)
      simp [h1, this]
    · by_cases h2 : go.GoStringLt k k'
      · have : k' ≠ k := fun e => goStringLt_irrefl _ (e ▸ h2)
        simp [h1, h2, this]
      · have := goStringLt_eq_of_not_lt h1 h2
        subst this
        simp [goStringLt_irrefl]
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    have ih := btFind_btInsert_idx k' ki k x ws hs.2
    unfold btInsert
    by_cases h1 : idxLess w (k', ki)
    · rw [if_pos h1]
      rw [idxLess_iff] at h1
      unfold btFind
      by_cases hwk : idxLess w (k, x)
      · rw [if_pos hwk, if_pos hwk, ih]
      · rw [if_neg hwk, if_neg hwk]
        rw [idxLess_iff] at hwk
        have : k' ≠ k := by
          intro e; subst e; exact hwk h1
        simp only [this, ↓reduceIte]
    · rw [if_neg h1]
      rw [idxLess_iff] at h1
      by_cases h2 : idxLess (k', ki) w
      · rw [if_pos h2]
        rw [idxLess_iff] at h2
        conv => lhs; unfold btFind
        simp only [idxLess_iff]
        by_cases h3 : go.GoStringLt k' k
        · have : k' ≠ k := fun e => goStringLt_irrefl _ (e ▸ h3)
          simp only [h3, ↓reduceIte, this]
        · by_cases h4 : go.GoStringLt k k'
          · have : k' ≠ k := fun e => goStringLt_irrefl _ (e ▸ h4)
            simp only [h3, h4, ↓reduceIte, this]
            unfold btFind
            have h5 : ¬ go.GoStringLt w.1 k := fun h => goStringLt_irrefl _
              (goStringLt_trans (goStringLt_trans h h4) h2)
            have h6 : go.GoStringLt k w.1 := goStringLt_trans h4 h2
            simp only [idxLess_iff, h5, h6, ↓reduceIte]
          · have := goStringLt_eq_of_not_lt h3 h4
            subst this
            simp only [goStringLt_irrefl, ↓reduceIte]
      · rw [if_neg h2]
        rw [idxLess_iff] at h2
        have hw : w.1 = k' := goStringLt_eq_of_not_lt h1 h2
        conv => lhs; unfold btFind
        conv => rhs; unfold btFind
        simp only [idxLess_iff, hw]
        by_cases h3 : go.GoStringLt k' k
        · have : k' ≠ k := fun e => goStringLt_irrefl _ (e ▸ h3)
          simp only [h3, ↓reduceIte, this]
        · by_cases h4 : go.GoStringLt k k'
          · have : k' ≠ k := fun e => goStringLt_irrefl _ (e ▸ h4)
            simp only [h3, h4, ↓reduceIte, this]
          · have := goStringLt_eq_of_not_lt h3 h4
            subst this
            simp only [goStringLt_irrefl, ↓reduceIte]

theorem idxGet_btInsert {idx : IndexM} (hs : idx.Pairwise idxLess) (k' : GoString) (ki : KeyIndex)
    (k : GoString) :
    idxGet (btInsert idxLess (k', ki) idx) k = if k' = k then some ki else idxGet idx k := by
  unfold idxGet
  rw [btFind_btInsert_idx k' ki k KeyIndex.fresh idx hs]
  by_cases h : k' = k <;> simp [h]

/-- `idxPut`, through the key's index (the empty one if the key has none). -/
theorem idxPut_eq (idx : IndexM) (k : GoString) (rev : Rev) :
    idxPut idx k rev = btInsert idxLess (k, kiPut ((idxGet idx k).getD kiEmpty) rev) idx := by
  unfold idxPut
  cases idxGet idx k with
  | none => rw [kiPut_fresh]; rfl
  | some ki => rfl

/-- `idxTombstone`, through the key's index: nothing if it is empty. -/
theorem idxTombstone_eq (idx : IndexM) (k : GoString) (rev : Rev) :
    idxTombstone idx k rev =
      if kiLastEmpty ((idxGet idx k).getD kiEmpty) then idx
      else btInsert idxLess (k, kiTombstone ((idxGet idx k).getD kiEmpty) rev) idx := by
  unfold idxTombstone
  cases idxGet idx k with
  | none => simp [kiLastEmpty_kiEmpty]
  | some ki => rfl

theorem IdxRep.nil : IdxRep [] [] := ⟨List.Pairwise.nil, fun _ => rfl⟩

theorem IdxRep.step {evs : List Ev} {idx : IndexM} (h : IdxRep evs idx) (ev : Ev) :
    IdxRep (evs ++ [ev]) (idxApply idx ev) := by
  obtain ⟨hs, hk⟩ := h
  unfold idxApply
  by_cases ht : ev.tomb
  · simp only [ht, ↓reduceIte]
    rw [idxTombstone_eq, hk]
    by_cases he : kiLastEmpty (kiOfKey evs ev.key)
    · rw [if_pos he]
      refine ⟨hs, fun k => ?_⟩
      rw [hk, kiOfKey_append]
      by_cases hkk : ev.key = k
      · subst hkk
        simp only [↓reduceIte, kiApply, ht, he]
      · rw [if_neg hkk]
    · rw [if_neg he]
      refine ⟨btInsert_sorted idxLess_swo hs, fun k => ?_⟩
      rw [idxGet_btInsert hs, kiOfKey_append]
      by_cases hkk : ev.key = k
      · subst hkk
        simp only [↓reduceIte, kiApply, ht, Option.getD_some]
        rw [if_neg he]
      · rw [if_neg hkk, if_neg hkk, hk]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]
    rw [idxPut_eq, hk]
    refine ⟨btInsert_sorted idxLess_swo hs, fun k => ?_⟩
    rw [idxGet_btInsert hs, kiOfKey_append]
    by_cases hkk : ev.key = k
    · subst hkk
      simp only [↓reduceIte, kiApply, ht, Bool.false_eq_true, Option.getD_some]
    · rw [if_neg hkk, if_neg hkk, hk]

theorem IdxRep.foldl (evs : List Ev) : ∀ (pre : List Ev) (idx : IndexM), IdxRep pre idx →
    IdxRep (pre ++ evs) (evs.foldl idxApply idx)
  | pre, idx, h => by
    induction evs generalizing pre idx with
    | nil => rw [List.append_nil]; exact h
    | cons ev evs ih =>
      rw [List.foldl_cons, show pre ++ ev :: evs = (pre ++ [ev]) ++ evs by simp]
      exact ih _ _ (h.step ev)

theorem indexOf_rep (evs : List Ev) : IdxRep evs (indexOf evs) :=
  List.nil_append evs ▸ IdxRep.foldl evs [] [] IdxRep.nil

/-- What the index answers of a key at a revision: through the key's own index. -/
theorem idxGet_indexOf_bind (evs : List Ev) (k : GoString) (r : w64) :
    (idxGet (indexOf evs) k).bind (fun ki => kiGet ki r) = kiGet (kiOfKey evs k) r := by
  rw [← (indexOf_rep evs).2 k]
  cases idxGet (indexOf evs) k with
  | none => simp [kiGet_kiEmpty]
  | some ki => rfl

/-! ### The state: `findKey` through a put and a delete -/

theorem findKey_cons (w : EtcdKv) (ws : List EtcdKv) (k : GoString) :
    findKey k (w :: ws) = if w.key = k then some w else findKey k ws := by
  unfold findKey; by_cases h : w.key = k <;> simp [h]

theorem findKey_nil (k : GoString) : findKey k [] = none := rfl

/-- `btInsert` on a state sorted by key: the inserted key-value replaces its key's. -/
theorem findKey_btInsert (nv : EtcdKv) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess → ∀ k,
      findKey k (btInsert etcdKvLess nv s) = if nv.key = k then some nv else findKey k s
  | [], _, k => by simp [btInsert, findKey]
  | w :: ws, hs, k => by
    rw [List.pairwise_cons] at hs
    unfold btInsert
    split
    · rename_i hwv
      rw [findKey_cons, findKey_btInsert nv ws hs.2 k, findKey_cons]
      by_cases hwk : w.key = k
      · have : nv.key ≠ k := by
          intro h; unfold etcdKvLess at hwv; rw [hwk, h] at hwv; exact goStringLt_irrefl _ hwv
        simp [hwk, this]
      · simp [hwk]
    · split
      · rw [findKey_cons, findKey_cons]
      · rename_i hwv hvw
        have heq : w.key = nv.key := goStringLt_eq_of_not_lt hwv hvw
        rw [findKey_cons, findKey_cons]
        by_cases hwk : w.key = k
        · simp [hwk, ← heq]
        · simp [hwk, ← heq]

theorem findKey_filter_ne (k k' : GoString) :
    ∀ (s : List EtcdKv),
      findKey k (s.filter fun x => !decide (x.key = k')) = if k' = k then none else findKey k s
  | [] => by simp [findKey]
  | w :: ws => by
    rw [List.filter_cons]
    by_cases hw : w.key = k'
    · simp only [hw, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, findKey_cons]
      rw [findKey_filter_ne k k' ws]
      by_cases hk : k' = k
      · simp [hk]
      · simp [hk, show w.key ≠ k by rw [hw]; exact hk]
    · simp only [hw, decide_false, Bool.not_false, ↓reduceIte, findKey_cons]
      rw [findKey_filter_ne k k' ws]
      by_cases hk : k' = k
      · simp [hk, show w.key ≠ k by rw [← hk]; exact hw]
      · by_cases hwk : w.key = k <;> simp [hwk, hk]

theorem putKv_sorted {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (k v : GoString)
    (l : w64) : (putKv r k v l s).Pairwise etcdKvLess :=
  btInsert_sorted etcdKvLess_swo hs

theorem applyChange_sorted {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (c : Change) :
    (applyChange r s c).Pairwise etcdKvLess := by
  cases c with
  | put k v l => exact putKv_sorted hs r k v l
  | del k => exact hs.filter _

theorem applyChanges_sorted (r : w64) (cs : List Change) :
    ∀ {s : List EtcdKv}, s.Pairwise etcdKvLess → (applyChanges r s cs).Pairwise etcdKvLess := by
  induction cs with
  | nil => intro s hs; exact hs
  | cons c cs ih => intro s hs; exact ih (applyChange_sorted hs r c)

/-- `findKey` of the put key after `putKv`: the new key-value, modified at `r`, created at the
old one's create revision (`r` if there was none), with version + 1 (1 if there was none). -/
theorem findKey_putKv_self {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (k v : GoString)
    (l : w64) :
    ∃ nv, findKey k (putKv r k v l s) = some nv ∧ nv.key = k ∧ nv.modRev = r ∧
      nv.createRev = ((findKey k s).map EtcdKv.createRev).getD r ∧
      nv.version = ((findKey k s).map EtcdKv.version).getD (W64 0) + W64 1 := by
  unfold putKv
  simp only
  rw [findKey_btInsert _ s hs]
  cases h : findKey k s with
  | none =>
    unfold findKey at h
    simp only [h, Option.map_none, Option.getD_none]
    refine ⟨{ key := k, createRev := r, modRev := r, version := W64 1, value := v, lease := l },
      by simp, rfl, rfl, rfl, ?_⟩
    simp only
    word
  | some kv =>
    unfold findKey at h
    simp only [h, Option.map_some, Option.getD_some]
    have hk : kv.key = k := by
      have := List.find?_some h
      simpa using this
    exact ⟨{ kv with modRev := r, version := kv.version + W64 1, value := v, lease := l },
      by simp [hk], hk, rfl, rfl, rfl⟩

theorem findKey_putKv_other {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (k k' v : GoString)
    (l : w64) (hne : k' ≠ k) : findKey k (putKv r k' v l s) = findKey k s := by
  unfold putKv
  simp only
  rw [findKey_btInsert _ s hs]
  cases h : findKey k' s with
  | none => unfold findKey at h; simp [h, hne]
  | some kv =>
    unfold findKey at h
    have hk : kv.key = k' := by simpa using List.find?_some h
    simp [h, hk, hne]

/-! ### The log: states and events of an appended revision -/

theorem stateAfter_append (log : Log) (cs : List Change) :
    stateAfter (log ++ [cs]) = applyChanges (W64 log.length) (stateAfter log) cs := by
  unfold stateAfter
  rw [List.zipIdx_append, List.foldl_append]
  simp

theorem stateAt_append_lt (log : Log) (cs : List Change) {r : Nat} (hr : r < log.length) :
    stateAt (log ++ [cs]) r = stateAt log r := by
  unfold stateAt
  rw [List.take_append_of_le_length (by omega)]

theorem stateAt_append_ge (log : Log) (cs : List Change) {r : Nat} (hr : log.length ≤ r) :
    stateAt (log ++ [cs]) r = applyChanges (W64 log.length) (stateAfter log) cs := by
  unfold stateAt
  rw [List.take_of_length_le (by simp; omega), stateAfter_append]

theorem stateAt_last (log : Log) : stateAt log (log.length - 1) = stateAfter log := by
  unfold stateAt
  rw [List.take_of_length_le (by omega)]

theorem stateAt_ge (log : Log) {r : Nat} (hr : log.length ≤ r) : stateAt log r = stateAfter log := by
  unfold stateAt
  rw [List.take_of_length_le (by omega)]

theorem stateAfter_sorted (log : Log) : (stateAfter log).Pairwise etcdKvLess := by
  unfold stateAfter
  generalize List.zipIdx log = ps
  generalize hs0 : ([] : List EtcdKv) = s0
  have : s0.Pairwise etcdKvLess := by rw [← hs0]; exact List.Pairwise.nil
  clear hs0
  induction ps generalizing s0 with
  | nil => exact this
  | cons p ps ih => exact ih _ (applyChanges_sorted _ _ this)

theorem stateAt_sorted (log : Log) (r : Nat) : (stateAt log r).Pairwise etcdKvLess :=
  stateAfter_sorted _

theorem evsOf_append (log : Log) (cs : List Change) :
    evsOf (log ++ [cs]) = evsOf log ++ evsOfRev log.length cs := by
  unfold evsOf
  rw [List.zipIdx_append, List.map_append, List.flatten_append]
  simp

theorem evsOfRev_take_succ (m : Nat) (cs : List Change) {i : Nat} (hi : i < cs.length) :
    evsOfRev m (cs.take (i + 1)) =
      evsOfRev m (cs.take i) ++
        [{ rev := ⟨W64 m, W64 i⟩, key := cs[i].key, tomb := cs[i].isDel }] := by
  unfold evsOfRev
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.zipIdx_append,
    List.map_append]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]

theorem applyChanges_take_succ (r : w64) (s : List EtcdKv) (cs : List Change) {i : Nat}
    (hi : i < cs.length) :
    applyChanges r s (cs.take (i + 1)) = applyChange r (applyChanges r s (cs.take i)) cs[i] := by
  unfold applyChanges
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-! ### A read at the top of a key index -/

/-- Below the last generation, the scan finds nothing when every revision is at or below the
read (each generation's tail is). -/
theorem kiFindGenAux_none_of_above {ki : KeyIndex} (hwf : KiWf ki) {r : w64} (habove : KiAbove ki ⟨r, W64 0⟩) :
    ∀ fuel, fuel + 1 < ki.gens.length + 1 → kiFindGenAux ki.gens r fuel = none
  | 0, _ => rfl
  | cg + 1, h => by
    rw [kiFindGenAux_succ]
    have hne := hwf.nonlast cg (by omega)
    have hmem : (ki.gens.getD cg Gen.empty) ∈ ki.gens := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    have htail := habove _ (kiRevs_mem hmem (getLastD_mem _ Rev.zero hne))
    simp only at htail
    simp only [hne, ↓reduceIte, ne_eq]
    rw [if_pos ⟨by omega, htail⟩]

/-- `findGeneration` at or above every revision: the last generation, if it is not empty. -/
theorem kiFindGen_top {ki : KeyIndex} (hwf : KiWf ki) {r : w64} (habove : KiAbove ki ⟨r, W64 0⟩) :
    kiFindGen ki r =
      if (ki.gens.getLastD Gen.empty).revs = [] then none else some (ki.gens.length - 1) := by
  have hne := hwf.ne
  have hpos := hwf.len_pos
  obtain ⟨m, hm⟩ : ∃ m, ki.gens.length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hg : ki.gens.getD m Gen.empty = ki.gens.getLastD Gen.empty := by
    rw [getLastD_eq_getD _ _ hne, hm, Nat.add_sub_cancel]
  unfold kiFindGen
  rw [hm, kiFindGenAux_succ, Nat.add_sub_cancel]
  simp only [hg]
  by_cases he : (ki.gens.getLastD Gen.empty).revs = []
  · simp only [he, ↓reduceIte]
    exact kiFindGenAux_none_of_above hwf habove m (by omega)
  · have hhead := habove _ (kiRevs_mem (getLastD_mem _ _ hne) (headD_mem he))
    simp only at hhead
    simp only [he, ↓reduceIte, ne_eq, hm, Nat.add_sub_cancel, not_true_eq_false, false_and, hhead]

/-- `walk` when every revision passes: the last one. -/
theorem genWalk_all_false {revs : List Rev} (hne : revs ≠ []) {p : Rev → Bool}
    (h : ∀ r ∈ revs, p r = false) : genWalk revs p = ((revs.length - 1 : Nat) : Int) := by
  have hpos := List.length_pos_iff.2 hne
  apply genWalk_eq_some (revs.length - 1) (by omega)
  · exact h _ (List.getElem_mem _)
  · intro k hk hlt; omega

/-- `get` at or above every revision: the last generation's last revision, its create
revision and its version; nothing if the last generation is empty. -/
theorem kiGet_top {ki : KeyIndex} (hwf : KiWf ki) {r : w64} (habove : KiAbove ki ⟨r, W64 0⟩) :
    kiGet ki r =
      if (ki.gens.getLastD Gen.empty).revs = [] then none
      else some ((ki.gens.getLastD Gen.empty).revs.getLastD Rev.zero,
        (ki.gens.getLastD Gen.empty).created, (ki.gens.getLastD Gen.empty).ver) := by
  have hne := hwf.ne
  rw [kiGet_eq, kiFindGen_top hwf habove]
  by_cases he : (ki.gens.getLastD Gen.empty).revs = []
  · simp only [he, ↓reduceIte, Option.bind_none]
  · simp only [he, ↓reduceIte, Option.bind_some]
    unfold genGet
    rw [← getLastD_eq_getD _ _ hne]
    simp only [he, ↓reduceIte]
    have hw : genWalk (ki.gens.getLastD Gen.empty).revs (pAbove r) =
        (((ki.gens.getLastD Gen.empty).revs.length - 1 : Nat) : Int) := by
      apply genWalk_all_false he
      intro x hx
      have := habove _ (kiRevs_mem (getLastD_mem _ _ hne) hx)
      simp [pAbove]; omega
    have hpos := List.length_pos_iff.2 he
    have hne1 : ((((ki.gens.getLastD Gen.empty).revs.length - 1 : Nat)) : Int) ≠ -1 := by omega
    simp only [hw, hne1, ↓reduceIte, Int.toNat_natCast]
    rw [← getLastD_eq_getD _ _ he]
    rw [show (((ki.gens.getLastD Gen.empty).revs.length : Int) -
      (((ki.gens.getLastD Gen.empty).revs.length - 1 : Nat) : Int) - 1) = 0 by omega]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    word

/-- What `get` returns is a revision of the index. -/
theorem kiGet_mem {ki : KeyIndex} {r : w64} {rev created : Rev} {ver : w64}
    (h : kiGet ki r = some (rev, created, ver)) : rev ∈ kiRevs ki := by
  rw [kiGet_eq] at h
  cases hf : kiFindGen ki r with
  | none => rw [hf] at h; simp at h
  | some gi =>
    rw [hf] at h
    simp only [Option.bind_some] at h
    have hgi := kiFindGen_lt hf
    have hmem : (ki.gens.getD gi Gen.empty) ∈ ki.gens := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgi]
      exact List.getElem_mem _
    unfold genGet at h
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hrev, -, -⟩ := h
        have hrange := genWalk_range (ki.gens.getD gi Gen.empty).revs (pAbove r)
        rename_i hn
        have hlt : (genWalk (ki.gens.getD gi Gen.empty).revs (pAbove r)).toNat <
            (ki.gens.getD gi Gen.empty).revs.length := by omega
        rw [← hrev, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact kiRevs_mem hmem (List.getElem_mem _)

/-! ### The main theorem: what the key index answers is the state's key-value -/

/-- The bucket holds, at revision `rev`, the key-value `kv`: `rev`'s change wrote it
(`changeKv`, what `bucketOfRev` encodes). -/
def BucketHas (log : Log) (rev : Rev) (kv : EtcdKv) : Prop :=
  ∃ cs, log[rev.main.toNat]? = some cs ∧
    changeKv rev.main (stateAt log (rev.main.toNat - 1)) cs rev.sub.toNat = some kv

/-- `kiGet`'s answer against the state's key-value: both absent, or the key-value's mod
revision, create revision and version are the answer's, and the bucket has the key-value at
the answer's revision. -/
def KvMatch (log : Log) : Option (Rev × Rev × w64) → Option EtcdKv → Prop
  | none, none => True
  | some (rev, created, ver), some kv =>
    kv.modRev = rev.main ∧ kv.createRev = created.main ∧ kv.version = ver ∧ BucketHas log rev kv
  | _, _ => False

theorem BucketHas_append {log : Log} {rev : Rev} {kv : EtcdKv} (h : BucketHas log rev kv)
    (hlt : rev.main.toNat < log.length) (cs : List Change) : BucketHas (log ++ [cs]) rev kv := by
  obtain ⟨cs0, h1, h2⟩ := h
  refine ⟨cs0, ?_, ?_⟩
  · rw [List.getElem?_append_left hlt]; exact h1
  · rw [stateAt_append_lt _ _ (by omega)]; exact h2

theorem KvMatch_append {log : Log} {o : Option (Rev × Rev × w64)} {kvo : Option EtcdKv}
    (h : KvMatch log o kvo)
    (hlt : ∀ rev created ver, o = some (rev, created, ver) → rev.main.toNat < log.length)
    (cs : List Change) : KvMatch (log ++ [cs]) o kvo := by
  match o, kvo, h with
  | none, none, _ => trivial
  | some (rev, created, ver), some kv, ⟨h1, h2, h3, h4⟩ =>
    exact ⟨h1, h2, h3, BucketHas_append h4 (hlt _ _ _ rfl) cs⟩

theorem KvMatch_none_right {log : Log} {o : Option (Rev × Rev × w64)} (h : KvMatch log o none) :
    o = none := by
  match o, h with
  | none, _ => rfl

theorem KvMatch_none_left {log : Log} {kvo : Option EtcdKv} (h : KvMatch log none kvo) :
    kvo = none := by
  match kvo, h with
  | none, _ => rfl

/-- The key index `ki` of `k` stands for the log: well-formed, its revisions' mains below the
log's length, and its answer at every revision matching the state at it. -/
structure KeyLink (log : Log) (k : GoString) (ki : KeyIndex) : Prop where
  wf : KiWf ki
  revs : ∀ r ∈ kiRevs ki, r.main.toNat < log.length
  match_ : ∀ r : Nat, r < 2 ^ 63 → KvMatch log (kiGet ki (W64 r)) (findKey k (stateAt log r))

/-- A key's events folded onto a key index. -/
def kiFold (ki0 : KeyIndex) (evs : List Ev) (k : GoString) : KeyIndex :=
  (evs.filter fun ev => decide (ev.key = k)).foldl kiApply ki0

theorem kiOfKey_eq_kiFold (evs : List Ev) (k : GoString) : kiOfKey evs k = kiFold kiEmpty evs k := rfl

theorem kiFold_append (ki0 : KeyIndex) (evs evs' : List Ev) (k : GoString) :
    kiFold ki0 (evs ++ evs') k = kiFold (kiFold ki0 evs k) evs' k := by
  unfold kiFold; rw [List.filter_append, List.foldl_append]

theorem kiFold_nil (ki0 : KeyIndex) (k : GoString) : kiFold ki0 [] k = ki0 := rfl

theorem kiFold_singleton (ki0 : KeyIndex) (ev : Ev) (k : GoString) :
    kiFold ki0 [ev] k = if ev.key = k then kiApply ki0 ev else ki0 := by
  unfold kiFold
  rw [List.filter_cons, List.filter_nil]
  by_cases h : ev.key = k
  · simp [h]
  · simp [h]

/-- The well-formedness of a log the induction carries: revision 0 (if any) is empty, and
every delete is of a key present at that point. `LogWf` implies it, and it holds of every
prefix. -/
def LogWf' (log : Log) : Prop :=
  (log ≠ [] → log[0]? = some []) ∧
  ∀ (r : Nat) (cs : List Change) (i : Nat) (k : GoString), log[r]? = some cs →
    cs[i]? = some (.del k) →
    (findKey k (applyChanges (W64 r) (stateAt log (r - 1)) (cs.take i))).isSome

theorem LogWf'.of_wf {log : Log} (h : LogWf log) : LogWf' log := ⟨fun _ => h.1, h.2⟩

theorem LogWf'.prefix {log : Log} {cs : List Change} (h : LogWf' (log ++ [cs])) : LogWf' log := by
  refine ⟨fun hne => ?_, fun r cs' i k hr hi => ?_⟩
  · have := h.1 (by simp)
    rw [List.getElem?_append_left (List.length_pos_iff.2 hne)] at this
    exact this
  · have hlt : r < log.length := (List.getElem?_eq_some_iff.1 hr).1
    have := h.2 r cs' i k (by rw [List.getElem?_append_left hlt]; exact hr) hi
    rw [stateAt_append_lt _ _ (by omega)] at this
    exact this

theorem LogWf'.nil : LogWf' [] := ⟨fun h => absurd rfl h, fun r cs i k hr => by simp at hr⟩

/-- `KiAbove` from the mains' bound. -/
theorem kiAbove_of_le {ki : KeyIndex} {m : Nat} (hm : m < 2 ^ 63)
    (h : ∀ r ∈ kiRevs ki, r.main.toNat ≤ m) {r : Nat} (hr : m ≤ r) (hr2 : r < 2 ^ 63) :
    KiAbove ki ⟨W64 r, W64 0⟩ := by
  intro x hx
  have := h x hx
  simp only
  word

/-- One revision's changes, one by one: the key's index after the first `i` of them stands
for the state after them. -/
theorem rev_step (log : Log) (cs : List Change) (hlen : log.length + 1 < 2 ^ 63)
    (hcs : cs.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (k : GoString) (ki0 : KeyIndex)
    (h0 : KeyLink log k ki0) :
    ∀ i, i ≤ cs.length →
      KiWf (kiFold ki0 (evsOfRev log.length (cs.take i)) k) ∧
      (∀ r ∈ kiRevs (kiFold ki0 (evsOfRev log.length (cs.take i)) k), r.main.toNat ≤ log.length) ∧
      (∀ r : Nat, r < log.length →
        kiGet (kiFold ki0 (evsOfRev log.length (cs.take i)) k) (W64 r) = kiGet ki0 (W64 r)) ∧
      (∀ r : Nat, log.length ≤ r → r < 2 ^ 63 →
        KvMatch (log ++ [cs]) (kiGet (kiFold ki0 (evsOfRev log.length (cs.take i)) k) (W64 r))
          (findKey k (applyChanges (W64 log.length) (stateAfter log) (cs.take i))))
  | 0, _ => by
    simp only [List.take_zero, evsOfRev, List.zipIdx_nil, List.map_nil, kiFold_nil, applyChanges,
      List.foldl_nil]
    refine ⟨h0.wf, fun r hr => Nat.le_of_lt (h0.revs r hr), fun _ _ => trivial, fun r hr hr2 => ?_⟩
    have := h0.match_ r hr2
    rw [stateAt_ge _ hr] at this
    exact KvMatch_append this (fun rev created ver he => h0.revs rev (kiGet_mem he)) cs
  | i + 1, hi => by
    obtain ⟨hwf_i, hrevs_i, hlow_i, hmatch_i⟩ := rev_step log cs hlen hcs hwf k ki0 h0 i (by omega)
    have hi' : i < cs.length := by omega
    have hm0 : log ≠ [] := by
      intro he
      have := hwf.1 (by simp)
      rw [he] at this
      simp at this
      rw [this] at hi'
      simp at hi'
    have hmpos : 0 < log.length := List.length_pos_iff.2 hm0
    have hs_sorted : (applyChanges (W64 log.length) (stateAfter log) (cs.take i)).Pairwise etcdKvLess :=
      applyChanges_sorted _ _ (stateAfter_sorted log)
    -- the bucket's state before this revision is the state after the log
    have hbefore : stateAt (log ++ [cs]) (log.length - 1) = stateAfter log := by
      rw [stateAt_append_lt _ _ (by omega), stateAt_last]
    have hlogm : (log ++ [cs])[log.length]? = some cs := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    rw [evsOfRev_take_succ log.length cs hi', kiFold_append, kiFold_singleton,
      applyChanges_take_succ _ _ _ hi']
    generalize hm : log.length = m at hlen hs_sorted hbefore hlogm hwf_i hrevs_i hlow_i hmatch_i hmpos ⊢
    generalize hs : applyChanges (W64 m) (stateAfter log) (cs.take i) = s at hs_sorted hmatch_i ⊢
    generalize hki : kiFold ki0 (evsOfRev m (cs.take i)) k = ki at hwf_i hrevs_i hlow_i hmatch_i ⊢
    simp only
    have hmt : (W64 m).toNat = m := by word
    have hit : (W64 i).toNat = i := by word
    have htop : KiAbove ki ⟨W64 m, W64 0⟩ :=
      kiAbove_of_le (by omega) hrevs_i (Nat.le_refl _) (by omega)
    have hget_top := kiGet_top hwf_i htop
    have hmatch_top := hmatch_i m (Nat.le_refl _) (by omega)
    by_cases hkk : cs[i].key = k
    · rw [if_pos hkk]
      cases hc : cs[i] with
      | put k' v l =>
        rw [hc] at hkk
        simp only [Change.key] at hkk
        subst hkk
        simp only [Change.isDel, kiApply, Bool.false_eq_true, ↓reduceIte, applyChange]
        have hne := hwf_i.ne
        have habove : KiAbove ki ⟨W64 m, W64 i⟩ := by
          intro x hx; have := hrevs_i x hx; simp only; word
        refine ⟨hwf_i.put _, ?_, ?_, ?_⟩
        · intro r hr
          rw [kiRevs_kiPut hne, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | hr
          · exact hrevs_i r hr
          · rw [hr]; simp only; word
        · intro r hr
          rw [kiGet_kiPut_below hwf_i habove (by simp only; word)]
          exact hlow_i r hr
        · intro r hr hr2
          rw [kiGet_kiPut_above hwf_i habove (by simp only; word)]
          obtain ⟨nv, hnv, hnvk, hmod, hcreate, hver⟩ := findKey_putKv_self hs_sorted (W64 m) k' v l
          rw [hnv]
          simp only [KvMatch]
          have hbucket : BucketHas (log ++ [cs]) ⟨W64 m, W64 i⟩ nv := by
            refine ⟨cs, ?_, ?_⟩
            · simp only
              rw [hmt]
              exact hlogm
            · simp only
              rw [hmt, hit, hbefore]
              unfold changeKv
              rw [List.getElem?_eq_getElem hi', hc]
              simp only
              rw [applyChanges_take_succ _ _ _ hi', hc, hs]
              simp only [applyChange]
              exact hnv
          refine ⟨hmod, ?_, ?_, hbucket⟩
          · rw [hcreate]
            by_cases he : (ki.gens.getLastD Gen.empty).revs = []
            · rw [if_pos he]
              rw [if_pos he] at hget_top
              rw [hget_top] at hmatch_top
              rw [KvMatch_none_left hmatch_top]
              rfl
            · rw [if_neg he]
              rw [if_neg he] at hget_top
              rw [hget_top] at hmatch_top
              cases hf : findKey k' s with
              | none => rw [hf] at hmatch_top; exact absurd hmatch_top (by simp [KvMatch])
              | some kv =>
                rw [hf] at hmatch_top
                simp only [KvMatch] at hmatch_top
                simp only [Option.map_some, Option.getD_some]
                exact hmatch_top.2.1
          · rw [hver]
            by_cases he : (ki.gens.getLastD Gen.empty).revs = []
            · rw [if_pos he] at hget_top
              rw [hget_top] at hmatch_top
              rw [KvMatch_none_left hmatch_top]
              have hwfl := hwf_i.last_wf
              rw [hwfl.1, he]
              simp
            · rw [if_neg he] at hget_top
              rw [hget_top] at hmatch_top
              cases hf : findKey k' s with
              | none => rw [hf] at hmatch_top; exact absurd hmatch_top (by simp [KvMatch])
              | some kv =>
                rw [hf] at hmatch_top
                simp only [KvMatch] at hmatch_top
                simp only [Option.map_some, Option.getD_some]
                rw [hmatch_top.2.2.1]
      | del k' =>
        rw [hc] at hkk
        simp only [Change.key] at hkk
        subst hkk
        simp only [Change.isDel, kiApply, ↓reduceIte, applyChange]
        have hne := hwf_i.ne
        -- the key is present (the log is well formed), so the last generation is not empty
        have hpresent := hwf.2 m cs i k' hlogm (by rw [List.getElem?_eq_getElem hi', hc])
        rw [hbefore, hs] at hpresent
        have hlast : kiLastEmpty ki = false := by
          unfold kiLastEmpty
          by_cases he : (ki.gens.getLastD Gen.empty).revs = []
          · rw [if_pos he] at hget_top
            rw [hget_top] at hmatch_top
            rw [KvMatch_none_left hmatch_top] at hpresent
            simp at hpresent
          · simp only [he, decide_false]
        rw [hlast]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have habove : KiAbove ki ⟨W64 m, W64 i⟩ := by
          intro x hx; have := hrevs_i x hx; simp only; word
        refine ⟨hwf_i.tombstone _, ?_, ?_, ?_⟩
        · intro r hr
          rw [kiRevs_kiTombstone hne, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | hr
          · exact hrevs_i r hr
          · rw [hr]; simp only; word
        · intro r hr
          rw [kiGet_kiTombstone_below hwf_i habove (by simp only; word)]
          exact hlow_i r hr
        · intro r hr hr2
          rw [kiGet_kiTombstone_above hwf_i habove (by simp only; word), findKey_filter_ne,
            if_pos rfl]
          trivial
    · rw [if_neg hkk]
      refine ⟨hwf_i, hrevs_i, hlow_i, fun r hr hr2 => ?_⟩
      have := hmatch_i r hr hr2
      cases hc : cs[i] with
      | put k' v l =>
        rw [hc] at hkk
        simp only [Change.key] at hkk
        simp only [applyChange]
        rw [findKey_putKv_other hs_sorted _ _ _ _ _ hkk]
        exact this
      | del k' =>
        rw [hc] at hkk
        simp only [Change.key] at hkk
        simp only [applyChange]
        rw [findKey_filter_ne, if_neg hkk]
        exact this

/-- The link, through an appended revision. -/
theorem keyLink_append {log : Log} {cs : List Change} (hlen : log.length + 1 < 2 ^ 63)
    (hcs : cs.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (k : GoString)
    (h0 : KeyLink log k (kiOfKey (evsOf log) k)) :
    KeyLink (log ++ [cs]) k (kiOfKey (evsOf (log ++ [cs])) k) := by
  obtain ⟨hwf', hrevs, hlow, hmatch⟩ :=
    rev_step log cs hlen hcs hwf k _ h0 cs.length (Nat.le_refl _)
  rw [List.take_length] at hwf' hrevs hlow hmatch
  have hki : kiOfKey (evsOf (log ++ [cs])) k = kiFold (kiOfKey (evsOf log) k) (evsOfRev log.length cs) k := by
    rw [evsOf_append, kiOfKey_eq_kiFold, kiFold_append]; rfl
  rw [hki]
  refine ⟨hwf', fun r hr => ?_, fun r hr2 => ?_⟩
  · have := hrevs r hr
    rw [List.length_append, List.length_singleton]
    omega
  · by_cases hr : r < log.length
    · rw [hlow r hr, stateAt_append_lt _ _ hr]
      exact KvMatch_append (h0.match_ r hr2) (fun rev created ver he => h0.revs rev (kiGet_mem he)) cs
    · rw [stateAt_append_ge _ _ (by omega)]
      exact hmatch r (by omega) hr2

theorem keyLink_nil (k : GoString) : KeyLink [] k (kiOfKey (evsOf []) k) := by
  refine ⟨KiWf.kiEmpty, fun r hr => ?_, fun r _ => ?_⟩
  · simp [evsOf, kiOfKey, kiRevs, kiEmpty, Gen.empty] at hr
  · simp only [evsOf, List.zipIdx_nil, List.map_nil, List.flatten_nil, kiOfKey, List.filter_nil,
      List.foldl_nil, kiGet_kiEmpty, stateAt, List.take_nil, stateAfter, findKey_nil]
    trivial

theorem keyLink_of_rev (k : GoString) :
    ∀ (rl : List (List Change)), rl.length < 2 ^ 63 → (∀ cs ∈ rl, cs.length < 2 ^ 63) →
      LogWf' rl.reverse → KeyLink rl.reverse k (kiOfKey (evsOf rl.reverse) k)
  | [], _, _, _ => keyLink_nil k
  | cs :: rl, hlen, hcs, hwf => by
    rw [List.reverse_cons] at hwf ⊢
    have hlen' : rl.reverse.length + 1 < 2 ^ 63 := by simp at hlen ⊢; omega
    exact keyLink_append hlen' (hcs cs List.mem_cons_self) hwf k
      (keyLink_of_rev k rl (by simp at hlen; omega) (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
        hwf.prefix)

/-- **The model's main theorem.** For a well-formed log, what the index built from its
events answers of a key at a revision (`keyIndex.get` through `treeIndex.Get`) is the
key-value of the state at that revision: nothing if the key is absent, else the key-value's
mod revision, create revision and version, and the bucket holds the key-value at the mod
revision. -/
theorem kiGet_indexOf (log : Log) (hlen : log.length < 2 ^ 63) (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63)
    (hwf : LogWf log) (k : GoString) (r : Nat) (hr : r < 2 ^ 63) :
    KvMatch log ((idxGet (indexOf (evsOf log)) k).bind (fun ki => kiGet ki (W64 r)))
      (findKey k (stateAt log r)) := by
  rw [idxGet_indexOf_bind]
  have := keyLink_of_rev k log.reverse (by simp; exact hlen)
    (fun cs hcs' => hcs cs (List.mem_reverse.1 hcs'))
    (by rw [List.reverse_reverse]; exact LogWf'.of_wf hwf)
  rw [List.reverse_reverse] at this
  exact this.match_ r hr

end mvcc
end EtcdGrove
end Perennial
