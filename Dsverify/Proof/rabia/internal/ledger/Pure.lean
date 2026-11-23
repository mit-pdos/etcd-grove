/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Pure.lean`, run `rabia-r1wake-1`.)

Pure lemmas of the ledger's abstract state: the shapes of `addProp` and `put`, and that they keep
the state well formed (given the totals' bounds).
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Sorting

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open model

theorem pairwise_get? {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) (i j : Nat)
    (a b : α) (hij : i < j) (ha : l[i]? = some a) (hb : l[j]? = some b) : R a b := by
  rw [List.getElem?_eq_some_iff] at ha hb
  obtain ⟨hi, rfl⟩ := ha; obtain ⟨hj, rfl⟩ := hb
  exact List.pairwise_iff_getElem.1 h i j hi hj hij

theorem sameId_true_iff (a b : ObjV) :
    a.sameId b = true ↔ (a.proSeq = b.proSeq ∧ a.proId = b.proId) := by
  unfold ObjV.sameId; simp

theorem sameId_trans {a b c : ObjV} (h1 : a.sameId b = true) (h2 : b.sameId c = true) :
    a.sameId c = true := by
  rw [sameId_true_iff] at *; exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem sameId_symm {a b : ObjV} (h : a.sameId b = true) : b.sameId a = true := by
  rw [sameId_comm]; exact h

@[simp] theorem SlotSt.addProp_isDone (st : SlotSt) (o : ObjV) : (st.addProp o).isDone = st.isDone := rfl
@[simp] theorem SlotSt.addProp_hasRecvDec (st : SlotSt) (o : ObjV) :
    (st.addProp o).hasRecvDec = st.hasRecvDec := rfl
@[simp] theorem SlotSt.addProp_decision (st : SlotSt) (o : ObjV) :
    (st.addProp o).decision = st.decision := rfl
@[simp] theorem SlotSt.addProp_bc (st : SlotSt) (o : ObjV) : (st.addProp o).bc = st.bc := rfl

theorem SlotSt.wf_total_ok (st : SlotSt) (h : st.wf) (p r : Nat) : cntOk (st.total p r) := by
  obtain ⟨-, -, -, -, h5, -⟩ := h
  unfold SlotSt.total
  rcases ht : st.bcT[p]? with _ | ⟨t1, t2⟩
  · simp [cntOk]
  · have := h5 _ (List.mem_of_getElem? ht)
    simp only; split <;> simp_all

theorem SlotSt.wf_counts_le (st : SlotSt) (h : st.wf) (p r : Nat) :
    (st.counts p r).1 ≤ st.total p r ∧ (st.counts p r).2.1 ≤ st.total p r ∧
      (st.counts p r).2.2 ≤ st.total p r := by
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := h
  unfold SlotSt.counts SlotSt.total
  rcases hc : st.bc[p]? with _ | c
  · simp
  · have hp := (List.getElem?_eq_some_iff.1 hc).1
    obtain ⟨t, ht⟩ : ∃ t, st.bcT[p]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [ht]
    have := h4 p c t hc ht
    obtain ⟨c1, c2⟩ := c; obtain ⟨t1, t2⟩ := t
    simp only at this ⊢
    split <;> omega

theorem SlotSt.wf_counts_ok (st : SlotSt) (h : st.wf) (p r : Nat) :
    cntOk (st.counts p r).1 ∧ cntOk (st.counts p r).2.1 ∧ cntOk (st.counts p r).2.2 := by
  have := st.wf_total_ok h p r
  have := st.wf_counts_le h p r
  unfold cntOk at *; omega

/-- The proposals' total after `bcT.modify 0 (+1, ·)`. -/
theorem total_modify0 (bcT : List (Nat × Nat)) (h : 1 ≤ bcT.length) (st : SlotSt) :
    ({ st with bcT := bcT.modify 0 (fun p => (p.1 + 1, p.2)) } : SlotSt).total 0 1 =
      ({ st with bcT := bcT } : SlotSt).total 0 1 + 1 := by
  unfold SlotSt.total
  simp only [List.getElem?_modify, ↓reduceIte]
  rcases hb : bcT[0]? with _ | ⟨t1, t2⟩
  · rw [List.getElem?_eq_none_iff] at hb; omega
  · simp

theorem SlotSt.addProp_bcT (st : SlotSt) (o : ObjV) (h : 1 ≤ st.bcT.length) :
    (st.addProp o).bcT = st.bcT.modify 0 (fun p => (p.1 + 1, p.2)) := by
  unfold SlotSt.addProp
  simp only
  rw [show 1 - st.bcT.length = 0 by omega, List.replicate_zero, List.append_nil]

theorem SlotSt.addProp_total (st : SlotSt) (o : ObjV) (h : 1 ≤ st.bcT.length) :
    (st.addProp o).total 0 1 = st.total 0 1 + 1 := by
  have e : st.addProp o = { st.addProp o with bcT := st.bcT.modify 0 (fun p => (p.1 + 1, p.2)) } := by
    rw [← st.addProp_bcT o h]
  rw [e, total_modify0 _ h]
  rfl

/-- `addProp` when the tally of `o`'s id is at index `i`. -/
theorem SlotSt.addProp_props_found (st : SlotSt) (o : ObjV) (hd : distinctIds st.props) (i : Nat)
    (x : ObjV × Nat) (hx : st.props[i]? = some x) (hs : x.1.sameId o = true) :
    (st.addProp o).props = st.props.set i (x.1, x.2 + 1) := by
  unfold SlotSt.addProp
  have hany : st.props.any (fun t => t.1.sameId o) = true :=
    List.any_eq_true.2 ⟨x, List.mem_of_getElem? hx, hs⟩
  simp only [hany, ↓reduceIte]
  rw [distinctIds_iff] at hd
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, List.getElem?_set]
  by_cases hk : i = k
  · subst hk
    rw [hx]; simp [hs, (List.getElem?_eq_some_iff.1 hx).1]
  · rw [if_neg hk]
    rcases hy : st.props[k]? with _ | y
    · rfl
    · simp only [Option.map_some]
      have hne : y.1.sameId o = false := by
        rcases Bool.eq_false_or_eq_true (y.1.sameId o) with h | h
        · exfalso
          have hyx : y.1.sameId x.1 = true := sameId_trans h (sameId_symm hs)
          rcases Nat.lt_or_gt_of_ne hk with hlt | hlt
          · have := pairwise_get? hd i k x y hlt hx hy; rw [sameId_comm] at this
            rw [this] at hyx; cases hyx
          · have := pairwise_get? hd k i y x hlt hy hx; rw [this] at hyx; cases hyx
        · exact h
      simp [hne]

/-- `addProp` when no tally has `o`'s id. -/
theorem SlotSt.addProp_props_new (st : SlotSt) (o : ObjV)
    (hn : ∀ x ∈ st.props, x.1.sameId o = false) :
    (st.addProp o).props = st.props ++ [(o, 1)] := by
  unfold SlotSt.addProp
  have hany : st.props.any (fun t => t.1.sameId o) = false := by
    rw [List.any_eq_false]; intro x hx; simp [hn x hx]
  simp only [hany, Bool.false_eq_true, ↓reduceIte]

/-- `addProp` keeps the state well formed, if the proposals' total stays below `2^62`. -/
theorem SlotSt.wf_addProp (st : SlotSt) (o : ObjV) (h : st.wf)
    (hb : cntOk (st.total 0 1 + 1)) : (st.addProp o).wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hT : 1 ≤ st.bcT.length := by omega
  have htot := st.addProp_total o hT
  have hbcT := st.addProp_bcT o hT
  have hbc : (st.addProp o).bc = st.bc := rfl
  -- the props
  have hprops : (∀ t ∈ (st.addProp o).props, t.2 ≤ st.total 0 1 + 1) ∧
      (st.addProp o).props.length ≤ st.total 0 1 + 1 ∧
      distinctIds (st.addProp o).props := by
    by_cases hf : ∃ x ∈ st.props, x.1.sameId o = true
    · obtain ⟨x, hxm, hs⟩ := hf
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hxm
      rw [st.addProp_props_found o h1 i x hi hs]
      refine ⟨?_, by simp; omega, ?_⟩
      · intro t ht
        rcases List.mem_iff_getElem?.1 ht with ⟨k, hk⟩
        rw [List.getElem?_set] at hk
        split at hk
        · split at hk
          · cases hk; have := h2 x hxm; simp; omega
          · cases hk
        · have := h2 t (List.mem_of_getElem? hk); omega
      · have e : (st.props.set i (x.1, x.2 + 1)).map Prod.fst = st.props.map Prod.fst := by
          apply List.ext_getElem?; intro k
          rw [List.getElem?_map, List.getElem?_map, List.getElem?_set]
          split
          · rename_i hk; subst hk; rw [hi]; simp [(List.getElem?_eq_some_iff.1 hi).1]
          · rfl
        unfold distinctIds; rw [e]; exact h1
    · have hn : ∀ x ∈ st.props, x.1.sameId o = false := by
        intro x hx; rcases Bool.eq_false_or_eq_true (x.1.sameId o) with h' | h'
        · exact absurd ⟨x, hx, h'⟩ hf
        · exact h'
      rw [st.addProp_props_new o hn]
      refine ⟨?_, by simp; omega, ?_⟩
      · intro t ht
        rcases List.mem_append.1 ht with ht | ht
        · have := h2 t ht; omega
        · simp at ht; subst ht; simp
      · unfold distinctIds
        rw [List.map_append, List.pairwise_append]
        refine ⟨h1, by simp, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        rcases List.mem_map.1 ha with ⟨x, hx, rfl⟩
        exact hn x hx
  obtain ⟨p1, p2, p3⟩ := hprops
  refine ⟨p3, by rw [htot]; exact p1, by rw [htot]; exact p2, ?_, ?_, ?_, ?_, ?_⟩
  · intro p c t hc ht
    rw [hbc] at hc
    rw [hbcT, List.getElem?_modify] at ht
    by_cases hp : 0 = p
    · subst hp
      rcases ht0 : st.bcT[0]? with _ | t0
      · rw [ht0] at ht; cases ht
      · rw [ht0] at ht; simp at ht; subst ht
        have := h4 0 c t0 hc ht0; simp; omega
    · simp [hp] at ht
      exact h4 p c t hc ht
  · intro t ht
    rw [hbcT] at ht
    rcases List.mem_iff_getElem?.1 ht with ⟨k, hk⟩
    rw [List.getElem?_modify] at hk
    by_cases hp : 0 = k
    · subst hp
      rcases ht0 : st.bcT[0]? with _ | t0
      · rw [ht0] at hk; cases hk
      · rw [ht0] at hk; simp at hk; subst hk
        have := h5 t0 (List.mem_of_getElem? ht0)
        have htt : st.total 0 1 = t0.1 := by unfold SlotSt.total; rw [ht0]; rfl
        unfold cntOk at *; simp; omega
    · simp [hp] at hk
      exact h5 t (List.mem_of_getElem? hk)
  · rw [hbc]; exact h6
  · rw [hbc, hbcT, List.length_modify]; exact h7
  · rw [hbc]; exact h8

/-! ### `put` -/

theorem getElem?_pad {α : Type} (l : List α) (k q : Nat) (d : α) :
    (l ++ List.replicate k d)[q]? =
      if q < l.length then l[q]? else if q < l.length + k then some d else none := by
  rw [List.getElem?_append]
  split
  · rfl
  · rw [List.getElem?_replicate]
    split <;> split <;> first | rfl | omega

/-- `put`'s increment of one count. -/
def incC (x : Nat) (c : Counts) : Counts :=
  if x = 0 then (c.1 + 1, c.2.1, c.2.2) else if x = 1 then (c.1, c.2.1 + 1, c.2.2)
  else (c.1, c.2.1, c.2.2 + 1)

/-- `put`'s increment of a phase's counts. -/
def incBC (r x : Nat) (q : Counts × Counts) : Counts × Counts :=
  if r = 1 then (incC x q.1, q.2) else (q.1, incC x q.2)

/-- `put`'s increment of a phase's totals. -/
def incT (r : Nat) (q : Nat × Nat) : Nat × Nat := if r = 1 then (q.1 + 1, q.2) else (q.1, q.2 + 1)

theorem SlotSt.put_bc (st : SlotSt) (p r x : Nat) :
    (st.put p r x).bc =
      (st.bc ++ List.replicate (p + 1 - st.bc.length) ((0, 0, 0), (0, 0, 0))).modify p (incBC r x) :=
  rfl

theorem SlotSt.put_bcT (st : SlotSt) (p r x : Nat) :
    (st.put p r x).bcT = (st.bcT ++ List.replicate (p + 1 - st.bcT.length) (0, 0)).modify p (incT r) :=
  rfl

@[simp] theorem SlotSt.put_props (st : SlotSt) (p r x : Nat) : (st.put p r x).props = st.props := rfl
@[simp] theorem SlotSt.put_isDone (st : SlotSt) (p r x : Nat) : (st.put p r x).isDone = st.isDone :=
  rfl
@[simp] theorem SlotSt.put_hasRecvDec (st : SlotSt) (p r x : Nat) :
    (st.put p r x).hasRecvDec = st.hasRecvDec := rfl
@[simp] theorem SlotSt.put_decision (st : SlotSt) (p r x : Nat) :
    (st.put p r x).decision = st.decision := rfl

/-- The totals only grow. -/
theorem SlotSt.put_total_ge (st : SlotSt) (p r x q r' : Nat) :
    st.total q r' ≤ (st.put p r x).total q r' := by
  unfold SlotSt.total
  rw [st.put_bcT, List.getElem?_modify, getElem?_pad]
  rcases hq : st.bcT[q]? with _ | ⟨t1, t2⟩
  · simp
  · have hl := (List.getElem?_eq_some_iff.1 hq).1
    simp only [hl, ↓reduceIte, hq, Option.map_eq_map, Option.map_some]
    unfold incT
    split <;> split <;> simp_all <;> split <;> simp_all

/-- The counts are bounded by the totals. -/
def cntLe (c : Counts × Counts) (t : Nat × Nat) : Prop :=
  c.1.1 ≤ t.1 ∧ c.1.2.1 ≤ t.1 ∧ c.1.2.2 ≤ t.1 ∧ c.2.1 ≤ t.2 ∧ c.2.2.1 ≤ t.2 ∧ c.2.2.2 ≤ t.2

theorem cntLe_inc (c : Counts × Counts) (t : Nat × Nat) (r x : Nat) (h : cntLe c t) :
    cntLe (incBC r x c) (incT r t) := by
  unfold cntLe incBC incT incC at *
  split <;> split <;> (try split) <;> simp only at * <;> omega

/-- `put` keeps the state well formed, if the total it increments stays below `2^62` and the
arrays below `2^32` entries. -/
theorem SlotSt.wf_put (st : SlotSt) (p r x : Nat) (h : st.wf) (hb : cntOk (st.total p r + 1))
    (hp : p + 1 < 2 ^ 32) : (st.put p r x).wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hmono := st.put_total_ge p r x 0 1
  refine ⟨h1, fun t ht => Nat.le_trans (h2 t ht) hmono, Nat.le_trans h3 hmono, ?_, ?_, ?_, ?_, ?_⟩
  · -- the counts below the totals
    have hpad : ∀ (q : Nat) (c : Counts × Counts) (t : Nat × Nat),
        (st.bc ++ List.replicate (p + 1 - st.bc.length) ((0, 0, 0), (0, 0, 0)))[q]? = some c →
        (st.bcT ++ List.replicate (p + 1 - st.bcT.length) (0, 0))[q]? = some t → cntLe c t := by
      intro q c t hc ht
      rw [getElem?_pad] at hc ht
      split at hc
      · rw [if_pos (by omega)] at ht
        exact h4 q c t hc ht
      · rw [if_neg (by omega)] at ht
        split at hc
        · rw [if_pos (by omega)] at ht
          cases hc; cases ht; simp [cntLe]
        · cases hc
    intro q c t hc ht
    rw [st.put_bc, List.getElem?_modify] at hc
    rw [st.put_bcT, List.getElem?_modify] at ht
    by_cases hq : p = q
    · subst hq
      simp only [↓reduceIte] at hc ht
      rcases hc0 : (st.bc ++ List.replicate (p + 1 - st.bc.length) ((0, 0, 0), (0, 0, 0)))[p]?
        with _ | c0
      · rw [hc0] at hc; cases hc
      rcases ht0 : (st.bcT ++ List.replicate (p + 1 - st.bcT.length) (0, 0))[p]? with _ | t0
      · rw [ht0] at ht; cases ht
      rw [hc0] at hc; rw [ht0] at ht
      simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hc ht
      subst hc ht
      exact cntLe_inc c0 t0 r x (hpad p c0 t0 hc0 ht0)
    · simp only [hq, ↓reduceIte, Option.map_eq_map, Option.map_id_fun', id] at hc ht
      exact hpad q c t hc ht
  · -- the totals' bound
    intro t ht
    rw [st.put_bcT] at ht
    rcases List.mem_iff_getElem?.1 ht with ⟨q, hq⟩
    rw [List.getElem?_modify, getElem?_pad] at hq
    by_cases hqp : p = q
    · subst hqp
      have htot : ∀ t0, st.bcT[p]? = some t0 → st.total p r = if r = 1 then t0.1 else t0.2 := by
        intro t0 h'; unfold SlotSt.total; rw [h']
      have htot0 : st.bcT.length ≤ p → st.total p r = 0 := by
        intro hle; unfold SlotSt.total; rw [List.getElem?_eq_none hle]
      simp only [↓reduceIte] at hq
      split at hq
      · rename_i hlt
        rcases h' : st.bcT[p]? with _ | t0
        · rw [h'] at hq; cases hq
        rw [h'] at hq
        simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hq
        subst hq
        have := h5 t0 (List.mem_of_getElem? h')
        rw [htot t0 h'] at hb
        unfold incT; unfold cntOk at *
        split <;> simp_all <;> omega
      · split at hq
        · simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hq
          subst hq
          rw [htot0 (by omega)] at hb
          unfold incT cntOk at *; split <;> simp <;> omega
        · cases hq
    · simp only [hqp, ↓reduceIte, Option.map_eq_map, Option.map_id_fun', id] at hq
      split at hq
      · exact h5 t (List.mem_of_getElem? hq)
      · split at hq
        · cases hq; simp [cntOk]
        · cases hq
  · rw [st.put_bc]; simp; omega
  · rw [st.put_bc, st.put_bcT]; simp; omega
  · rw [st.put_bc]; simp; omega

end Perennial.rabia.internal.ledger
