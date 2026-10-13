/-
Lemmas of the buffers' pure model (`Model.lean`): the canonical form, sortedness, the
transitions' well-formedness. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-! ## Auxiliary facts -/

theorem strLt_total {a b : GoString} (h : ¬ strLt a b) : a = b ∨ strLt b a := by
  by_cases h' : strLt b a
  · exact Or.inr h'
  · exact Or.inl (strLt_eq_of_not_lt h h')

theorem entLe_true {a b : Ent} : entLe a b = true ↔ ¬ strLt b.1 a.1 := by
  simp [entLe]

theorem entLe_trans' (a b c : Ent) (h1 : entLe a b = true) (h2 : entLe b c = true) :
    entLe a c = true := by
  rw [entLe_true] at *
  intro h
  rcases strLt_total h1 with e | e
  · rw [← e] at h; exact h2 h
  · exact h2 (strLt_trans h e)

theorem entLe_total' (a b : Ent) : (entLe a b || entLe b a) = true := by
  by_cases h : strLt b.1 a.1
  · have : entLe b a = true := entLe_true.mpr (strLt_asymm h)
    simp [this]
  · have : entLe a b = true := entLe_true.mpr h
    simp [this]

/-- The entries of one key. -/
abbrev keyIs (k : GoString) : Ent → Bool := fun e => decide (e.1 = k)

theorem lastVal_eq_filter (l : List Ent) (k : GoString) :
    lastVal l k = ((l.filter (keyIs k)).getLast?).map Prod.snd := by
  unfold lastVal
  rw [← List.head?_filter, List.filter_reverse, List.head?_reverse]

theorem lastVal_cons (e : Ent) (l : List Ent) (k : GoString) :
    lastVal (e :: l) k = (lastVal l k).or (if e.1 = k then some e.2 else none) := by
  unfold lastVal
  rw [List.reverse_cons, List.find?_append]
  cases h : l.reverse.find? (fun e => decide (e.1 = k)) with
  | some x => simp
  | none =>
    by_cases he : e.1 = k
    · simp [he, List.find?]
    · simp [he, List.find?]

theorem lastVal_eq_none {l : List Ent} {k : GoString} (h : ∀ e ∈ l, e.1 ≠ k) :
    lastVal l k = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [lastVal_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp [h e List.mem_cons_self]

theorem dedupLast_eq {e f : Ent} {rest : List Ent} (h : e.1 = f.1) :
    dedupLast (e :: f :: rest) = dedupLast (f :: rest) := by
  simp [dedupLast, h]

theorem dedupLast_ne {e f : Ent} {rest : List Ent} (h : ¬ e.1 = f.1) :
    dedupLast (e :: f :: rest) = e :: dedupLast (f :: rest) := by
  simp [dedupLast, h]

theorem lastVal_dedupLast (l : List Ent) (k : GoString) :
    lastVal (dedupLast l) k = lastVal l k := by
  induction l using dedupLast.induct with
  | case1 => rfl
  | case2 e => rfl
  | case3 e f rest h ih =>
    rw [dedupLast_eq h, ih, lastVal_cons e, lastVal_cons f]
    by_cases hk : f.1 = k
    · have : e.1 = k := h.trans hk
      cases lastVal rest k <;> simp [hk, this]
    · have : e.1 ≠ k := fun h' => hk (h.symm.trans h')
      simp [this]
  | case4 e f rest h ih =>
    rw [dedupLast_ne h, lastVal_cons e, lastVal_cons e, ih]

theorem dedupLast_sublist (l : List Ent) : (dedupLast l).Sublist l := by
  induction l using dedupLast.induct with
  | case1 => exact List.Sublist.slnil
  | case2 e => exact List.Sublist.refl _
  | case3 e f rest h ih => rw [dedupLast_eq h]; exact ih.cons e
  | case4 e f rest h ih => rw [dedupLast_ne h]; exact ih.cons_cons e

theorem dedupLast_sorted {l : List Ent} (h : l.Pairwise (fun a b => ¬ strLt b.1 a.1)) :
    entsSorted (dedupLast l) := by
  induction l using dedupLast.induct with
  | case1 => exact List.Pairwise.nil
  | case2 e => exact List.pairwise_singleton _ _
  | case3 e f rest he ih => rw [dedupLast_eq he]; exact ih h.of_cons
  | case4 e f rest he ih =>
    rw [dedupLast_ne he]
    have ih' := ih h.of_cons
    refine List.Pairwise.cons ?_ ih'
    have hef : strLt e.1 f.1 := by
      rcases strLt_total (List.rel_of_pairwise_cons h List.mem_cons_self) with e' | e'
      · exact absurd e'.symm he
      · exact e'
    intro x hx
    have hx' := (dedupLast_sublist _).subset hx
    rcases List.mem_cons.mp hx' with rfl | hx''
    · exact hef
    · rcases strLt_total (List.rel_of_pairwise_cons h.of_cons hx'') with e' | e'
      · rw [e']; exact hef
      · exact strLt_trans hef e'

theorem dedupLast_of_sorted {l : List Ent} (h : entsSorted l) : dedupLast l = l := by
  induction l using dedupLast.induct with
  | case1 => rfl
  | case2 e => rfl
  | case3 e f rest he ih =>
    exact absurd (he ▸ List.rel_of_pairwise_cons h List.mem_cons_self) (strLt_irrefl _)
  | case4 e f rest he ih => rw [dedupLast_ne he, ih h.of_cons]

theorem dedupLast_length_le (l : List Ent) : (dedupLast l).length ≤ l.length :=
  (dedupLast_sublist l).length_le

theorem mergeSort_pairwise (l : List Ent) :
    (l.mergeSort entLe).Pairwise (fun a b => ¬ strLt b.1 a.1) :=
  (List.pairwise_mergeSort entLe_trans' entLe_total' l).imp (fun h => entLe_true.mp h)

/-- The stable sort keeps the entries of each key in their order. -/
theorem filter_mergeSort (l : List Ent) (k : GoString) :
    (l.mergeSort entLe).filter (keyIs k) = l.filter (keyIs k) := by
  have hpw : (l.filter (keyIs k)).Pairwise (fun a b => entLe a b = true) := by
    rw [List.pairwise_filter]
    refine List.pairwise_of_forall (fun a b ha hb => ?_)
    simp only [keyIs, decide_eq_true_eq] at ha hb
    rw [entLe_true, ha, hb]; exact strLt_irrefl _
  have hs := List.sublist_mergeSort entLe_trans' entLe_total' hpw
    (List.filter_sublist (p := keyIs k))
  have hs' := hs.filter (keyIs k)
  rw [List.filter_filter] at hs'
  have : (l.filter (fun a => keyIs k a && keyIs k a)) = l.filter (keyIs k) := by simp
  rw [this] at hs'
  exact (hs'.eq_of_length
    (((List.mergeSort_perm l entLe).filter (keyIs k)).length_eq.symm)).symm

theorem lastVal_mergeSort (l : List Ent) (k : GoString) :
    lastVal (l.mergeSort entLe) k = lastVal l k := by
  rw [lastVal_eq_filter, lastVal_eq_filter, filter_mergeSort]

theorem filter_key_length_le {b : List Ent} (hn : (b.map Prod.fst).Nodup) (k : GoString) :
    (b.filter (keyIs k)).length ≤ 1 := by
  have hn' : ((b.filter (keyIs k)).map Prod.fst).Nodup :=
    hn.sublist ((List.filter_sublist).map _)
  have hall : ∀ e ∈ b.filter (keyIs k), e.1 = k := fun e he => by
    simpa [keyIs] using (List.mem_filter.mp he).2
  generalize b.filter (keyIs k) = c at hn' hall
  match c, hn', hall with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: _, hn', hall =>
    exfalso
    have hx := hall x List.mem_cons_self
    have hy := hall y (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hn'
    exact hn'.1 (Or.inl (hx.trans hy.symm))

/-! ## The order on entries -/

/-- `bucketBuffer.Less` (keys compared) is a strict weak order, as `sort.Sort`/`sort.Stable`
need. -/
theorem entLt_swo :
    slices.StrictWeakOrder (fun a b : Ent => decide (strLt a.1 b.1) = true) := by
  simp only [decide_eq_true_eq]
  exact {
    strict_weak_order_irrefl := fun _ => strLt_irrefl _
    strict_weak_order_trans := fun _ _ _ h1 h2 => strLt_trans h1 h2
    strict_weak_order_equiv := {
      refl := fun _ => ⟨strLt_irrefl _, strLt_irrefl _⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun h1 h2 => by
        have e1 := strLt_eq_of_not_lt h1.1 h1.2
        have e2 := strLt_eq_of_not_lt h2.1 h2.2
        refine ⟨?_, ?_⟩ <;> rw [e1, e2] <;> exact strLt_irrefl _ } }

/-- Sorted entries have distinct keys. -/
theorem entsSorted_nodup {es : List Ent} (h : entsSorted es) : (es.map Prod.fst).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  refine h.imp ?_
  intro a b hab heq
  rw [heq] at hab
  exact strLt_irrefl _ hab

theorem entsSorted_nil : entsSorted [] := List.Pairwise.nil

theorem entsSorted_append {a b : List Ent} :
    entsSorted (a ++ b) ↔ entsSorted a ∧ entsSorted b ∧ ∀ x ∈ a, ∀ y ∈ b, strLt x.1 y.1 := by
  exact List.pairwise_append

/-- What `sort.Sort` gives of entries with distinct keys (a permutation with no later key
below an earlier one) is sorted. -/
theorem entsSorted_of_sorted_nodup {l l' : List Ent} (hp : l.Perm l')
    (hn : (l.map Prod.fst).Nodup)
    (hs : ∀ (i j : Nat) (a b : Ent), l'[i]? = some a → l'[j]? = some b → i < j →
      decide (strLt b.1 a.1) = false) :
    entsSorted l' := by
  have hn' : (l'.map Prod.fst).Nodup := (hp.map _).nodup_iff.mp hn
  rw [List.Nodup, List.pairwise_map] at hn'
  have hle : l'.Pairwise (fun a b => ¬ strLt b.1 a.1) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij h
    have := hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
    simp only [decide_eq_false_iff_not] at this
    exact this h
  unfold entsSorted
  refine (hle.and hn').imp (fun ⟨h1, h2⟩ => ?_)
  rcases strLt_total h1 with e | e
  · exact absurd e.symm h2
  · exact e

/-! ## The canonical form -/

theorem canon_sorted (l : List Ent) : entsSorted (canon l) := by
  exact dedupLast_sorted (mergeSort_pairwise l)

theorem canon_of_sorted {l : List Ent} (h : entsSorted l) : canon l = l := by
  unfold canon
  rw [List.mergeSort_of_pairwise (h.imp (fun hab => entLe_true.mpr (strLt_asymm hab)))]
  exact dedupLast_of_sorted h

/-- A key's newest value is the canonical form's. -/
theorem lastVal_canon (l : List Ent) (k : GoString) : lastVal (canon l) k = lastVal l k := by
  rw [canon, lastVal_dedupLast, lastVal_mergeSort]

/-- Sorted lists with the same newest values are equal. -/
theorem eq_of_sorted_lastVal {a b : List Ent} (ha : entsSorted a) (hb : entsSorted b)
    (h : ∀ k, lastVal a k = lastVal b k) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y b =>
      have := h y.1
      rw [lastVal_cons] at this
      cases lastVal b y.1 <;> simp [lastVal] at this
  | cons x a ih =>
    cases b with
    | nil =>
      have := h x.1
      rw [lastVal_cons] at this
      cases lastVal a x.1 <;> simp [lastVal] at this
    | cons y b =>
      have hxa : ∀ e ∈ a, strLt x.1 e.1 := fun e he => List.rel_of_pairwise_cons ha he
      have hyb : ∀ e ∈ b, strLt y.1 e.1 := fun e he => List.rel_of_pairwise_cons hb he
      have hna : lastVal a x.1 = none :=
        lastVal_eq_none (fun e he h' => strLt_irrefl x.1 (h' ▸ hxa e he))
      have hnb : lastVal b y.1 = none :=
        lastVal_eq_none (fun e he h' => strLt_irrefl y.1 (h' ▸ hyb e he))
      have hk : x.1 = y.1 := by
        apply strLt_eq_of_not_lt
        · intro hlt
          have := h x.1
          have hyx : y.1 ≠ x.1 := fun h' => strLt_irrefl _ (h' ▸ hlt)
          rw [lastVal_cons, lastVal_cons, hna, lastVal_eq_none (l := b)] at this
          · simp [hyx] at this
          · intro e he h'; exact strLt_irrefl _ (strLt_trans hlt (h' ▸ hyb e he))
        · intro hlt
          have := h y.1
          have hxy : x.1 ≠ y.1 := fun h' => strLt_irrefl _ (h' ▸ hlt)
          rw [lastVal_cons, lastVal_cons, hnb, lastVal_eq_none (l := a)] at this
          · simp [hxy] at this
          · intro e he h'; exact strLt_irrefl _ (strLt_trans hlt (h' ▸ hxa e he))
      have hv : x.2 = y.2 := by
        have := h x.1
        rw [lastVal_cons, lastVal_cons, hna, hk, hnb] at this
        simpa using this
      have hxy : x = y := Prod.ext hk hv
      subst hxy
      congr 1
      apply ih ha.of_cons hb.of_cons
      intro k
      by_cases hkx : x.1 = k
      · subst hkx; rw [hna, hnb]
      · have := h k
        rw [lastVal_cons, lastVal_cons] at this
        simpa [hkx] using this

/-- The canonical form of entries followed by others does not depend on the order of the
others when their keys are distinct (`writeback` sorts them with `sort.Sort`, not stably). -/
theorem canon_append_perm {a b b' : List Ent} (hp : b.Perm b') (hn : (b.map Prod.fst).Nodup) :
    canon (a ++ b) = canon (a ++ b') := by
  apply eq_of_sorted_lastVal (canon_sorted _) (canon_sorted _)
  intro k
  rw [lastVal_canon, lastVal_canon, lastVal_eq_filter, lastVal_eq_filter, List.filter_append,
    List.filter_append]
  have hpf := hp.filter (keyIs k)
  have hlen := filter_key_length_le hn k
  have hf : b.filter (keyIs k) = b'.filter (keyIs k) := by
    generalize b.filter (keyIs k) = c at hpf hlen
    match c, hpf, hlen with
    | [], hpf, _ => exact (List.Perm.nil_eq hpf)
    | [_], hpf, _ => exact (List.perm_singleton.mp hpf.symm).symm
    | _ :: _ :: _, _, hlen => simp at hlen
  rw [hf]

theorem canon_length_le (l : List Ent) : (canon l).length ≤ l.length := by
  unfold canon
  exact Nat.le_trans (dedupLast_length_le _) (by simp)

theorem canon_nil : canon [] = [] := by
  simp [canon, dedupLast]

/-- `dedupe`'s loop: after `sort.Stable` (the stable sort by key, `List.mergeSort entLe`),
keeping the last entry of each run of one key gives the canonical form (by definition). -/
theorem canon_eq (l : List Ent) : canon l = dedupLast (l.mergeSort entLe) := rfl

/-! ## The buffers' transitions -/

theorem bkOf_wbAdd (B : GMap w64 (List Ent)) (id id' : w64) (e : Ent) :
    bkOf (wbAdd B id e) id' = if id = id' then bkOf B id ++ [e] else bkOf B id' := by
  simp only [bkOf, wbAdd, GMap.lookup_insert_eq_iff]
  split <;> simp_all

theorem WBuf.put_wf {W : WBuf} {id : w64} {e : Ent} (hW : W.Wf)
    (he : e.1 ∉ (bkOf W.bks id).map Prod.fst) : (W.put id e).Wf := by
  intro id' es h
  simp only [WBuf.put, wbAdd, GMap.lookup_insert_eq_iff] at h ⊢
  by_cases hid : id = id'
  · subst hid
    simp only [↓reduceIte, Option.some.injEq] at h ⊢
    subst h
    unfold wbBucketOk
    simp only [↓reduceIte]
    have hold : ((bkOf W.bks id).map Prod.fst).Nodup := by
      unfold bkOf
      cases hl : W.bks.lookup id with
      | none => simp
      | some es0 =>
        have := hW id es0 hl
        unfold wbBucketOk at this
        split at this
        · simpa using this
        · simpa using entsSorted_nodup this
    rw [List.map_append, List.nodup_append]
    refine ⟨hold, (by simp), ?_⟩
    intro a ha b hb hab
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb hab
    exact he ha
  · simp only [hid, ↓reduceIte] at h ⊢
    exact hW id' es h

theorem WBuf.putSeq_wf {W : WBuf} {id : w64} {e : Ent} (hW : W.Wf)
    (he : ∀ x ∈ bkOf W.bks id, strLt x.1 e.1) : (W.putSeq id e).Wf := by
  intro id' es h
  simp only [WBuf.putSeq, wbAdd, GMap.lookup_insert_eq_iff] at h ⊢
  by_cases hid : id = id'
  · subst hid
    simp only [↓reduceIte, Option.some.injEq] at h
    subst h
    have hold : wbBucketOk (W.seq.lookup id) (bkOf W.bks id) := by
      unfold bkOf
      cases hl : W.bks.lookup id with
      | none => unfold wbBucketOk; split <;> simp [entsSorted]
      | some es0 => exact hW id es0 hl
    unfold wbBucketOk at hold ⊢
    split
    · rename_i hs
      simp only [hs, ↓reduceIte] at hold
      rw [List.map_append, List.nodup_append]
      refine ⟨hold, (by simp), ?_⟩
      intro a ha b hb hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      subst hb
      exact strLt_irrefl _ (hab ▸ he x hx)
    · rename_i hs
      simp only [hs, ↓reduceIte] at hold
      refine entsSorted_append.mpr ⟨hold, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact he x hx
  · simp only [hid, ↓reduceIte] at h
    exact hW id' es h

/-! ## The relaxed well-formedness (`WBuf.WfR`) -/

theorem WBuf.WfR.of_Wf {W : WBuf} (D : w64 → Prop) (hW : W.Wf) : W.WfR D :=
  fun id es h => Or.inl (hW id es h)

theorem WBuf.WfR.mono {W : WBuf} {D D' : w64 → Prop} (hW : W.WfR D) (h : ∀ id, D id → D' id) :
    W.WfR D' := by
  intro id es hl
  rcases hW id es hl with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, h id h3⟩

/-- Where `D` allows nothing, `WfR` is `Wf`. -/
theorem WBuf.WfR.wf {W : WBuf} {D : w64 → Prop} (hW : W.WfR D) (h : ∀ id, ¬ D id) : W.Wf := by
  intro id es hl
  rcases hW id es hl with h1 | ⟨-, h3⟩
  · exact h1
  · exact absurd h3 (h id)

theorem WBuf.WfR.put {W : WBuf} {D : w64 → Prop} {id : w64} {e : Ent} (hW : W.WfR D)
    (he : e.1 ∉ (bkOf W.bks id).map Prod.fst ∨ D id) : (W.put id e).WfR D := by
  intro id' es h
  by_cases hid : id = id'
  · subst hid
    by_cases hD : D id
    · right
      refine ⟨?_, hD⟩
      simp [WBuf.put, GMap.lookup_insert_eq_iff]
    · left
      have he' := he.resolve_right hD
      simp only [WBuf.put, wbAdd, GMap.lookup_insert_eq_iff] at h ⊢
      simp only [↓reduceIte, Option.some.injEq] at h ⊢
      subst h
      unfold wbBucketOk
      simp only [↓reduceIte]
      have hold : ((bkOf W.bks id).map Prod.fst).Nodup := by
        unfold bkOf
        cases hl : W.bks.lookup id with
        | none => simp
        | some es0 =>
          rcases hW id es0 hl with h1 | ⟨-, h2⟩
          · unfold wbBucketOk at h1
            split at h1
            · simpa using h1
            · simpa using entsSorted_nodup h1
          · exact absurd h2 hD
      rw [List.map_append, List.nodup_append]
      refine ⟨hold, (by simp), ?_⟩
      intro a ha b hb hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb hab
      exact he' ha
  · have h' : W.bks.lookup id' = some es := by
      simpa [WBuf.put, wbAdd, GMap.lookup_insert_eq_iff, hid] using h
    have hs : (W.put id e).seq.lookup id' = W.seq.lookup id' := by
      simp [WBuf.put, GMap.lookup_insert_eq_iff, hid]
    rw [hs]
    exact hW id' es h'

theorem WBuf.WfR.putSeq {W : WBuf} {D : w64 → Prop} {id : w64} {e : Ent} (hW : W.WfR D)
    (he : ∀ x ∈ bkOf W.bks id, strLt x.1 e.1) : (W.putSeq id e).WfR D := by
  intro id' es h
  by_cases hid : id = id'
  · subst hid
    have hs : (W.putSeq id e).seq = W.seq := rfl
    rw [hs]
    have hb : bkOf W.bks id ++ [e] = es := by
      simpa [WBuf.putSeq, wbAdd, GMap.lookup_insert_eq_iff] using h
    cases hl : W.bks.lookup id with
    | none =>
      -- a new bucket: one entry
      have h0 : bkOf W.bks id = [] := by unfold bkOf; rw [hl]; rfl
      rw [h0] at hb
      subst hb
      left
      unfold wbBucketOk
      split <;> simp [entsSorted]
    | some es0 =>
      have h0 : bkOf W.bks id = es0 := by unfold bkOf; rw [hl]; rfl
      rw [h0] at hb he
      subst hb
      rcases hW id es0 hl with h1 | ⟨h2, h3⟩
      · left
        unfold wbBucketOk at h1 ⊢
        split
        · rename_i hs
          simp only [hs, ↓reduceIte] at h1
          rw [List.map_append, List.nodup_append]
          refine ⟨h1, (by simp), ?_⟩
          intro a ha b hb hab
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
          subst hb
          exact strLt_irrefl _ (hab ▸ he x hx)
        · rename_i hs
          simp only [hs, ↓reduceIte] at h1
          refine entsSorted_append.mpr ⟨h1, List.pairwise_singleton _ _, ?_⟩
          intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst hy
          exact he x hx
      · right; exact ⟨h2, h3⟩
  · have h' : W.bks.lookup id' = some es := by
      simpa [WBuf.putSeq, wbAdd, GMap.lookup_insert_eq_iff, hid] using h
    exact hW id' es h'

theorem WBuf.reset_wf (W : WBuf) : W.reset.Wf := by
  intro id es h
  simp only [WBuf.reset, bksReset, GMap.lookup_fmap, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  unfold wbBucketOk
  split <;> simp [entsSorted]

theorem writebackW_wf (W : WBuf) (R : RBuf) : (writebackW W R).Wf := by
  exact WBuf.reset_wf _

theorem writebackR_wf (W : WBuf) {R : RBuf} (hR : R.Wf) : (writebackR W R).Wf := by
  intro id es h
  simp only [writebackR, wbMerge] at h
  change ((gmapImap _ W.bks).lookup id).or (R.bks.lookup id) = some es at h
  cases hw : W.bks.lookup id with
  | none =>
    simp only [gmapImap, GMap.lookup_mk, hw, Option.map_none, Option.none_or] at h
    exact hR id es h
  | some ws =>
    simp only [gmapImap, GMap.lookup_mk, hw, Option.map_some, Option.some_or,
      Option.some.injEq] at h
    subst h
    exact canon_sorted _

theorem RBuf.reset_wf {R : RBuf} (hR : R.Wf) : R.reset.Wf := by
  intro id es h
  simp only [RBuf.reset, bksReset, GMap.lookup_fmap, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  exact List.Pairwise.nil

theorem bbRange_nil (key endKey : GoString) (limit : w64) : bbRange [] key endKey limit = [] := by
  rfl

end backend
end EtcdGrove
end Perennial
