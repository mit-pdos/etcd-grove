/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/Pure.lean`, run `rabia-r1wake-1`.)

The consensus package's pure lemmas: the slots' tallies (`TallyOk`) under the ledger's updates, the
majority reads of two counted messages, and the slot invariant's transitions (`SlotOk`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec
public import Dsverify.Proof.rabia.internal.ledger.Pure
public import Dsverify.Proof.rabia.internal.ledger.Sorting

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open model rabia.internal.message rabia.internal.ledger rabia

variable {cf : RCfg}

/-! ## Helpers -/

theorem tally_append (ents : List Ent) (e : Ent) (ρ : Nat) :
    tally (ents ++ [e]) ρ = tally ents ρ ++ (if e.1 = ρ then [e] else []) := by
  unfold tally
  rw [List.filter_append]
  by_cases h : e.1 = ρ <;> simp [h]

theorem countsOf_snoc (vs : List Nat) (x : Nat) :
    countsOf (vs ++ [x]) = incC x (countsOf vs) := by
  unfold countsOf incC
  simp only [List.count_append, List.filter_append, List.length_append]
  by_cases h0 : x = 0
  · subst h0; simp
  · by_cases h1 : x = 1
    · subst h1; simp
    · simp [h0, h1, List.count_singleton, Ne.symm h0, Ne.symm h1]

theorem SlotSt.put_total' (st : SlotSt) (p r x q r' : Nat) (hr : r = 1 ∨ r = 2)
    (hr' : r' = 1 ∨ r' = 2) :
    (st.put p r x).total q r' = if q = p ∧ r' = r then st.total q r' + 1 else st.total q r' := by
  unfold SlotSt.total
  rw [st.put_bcT, List.getElem?_modify, getElem?_pad]
  by_cases hq : q = p
  · subst hq
    simp only [↓reduceIte, true_and]
    by_cases hl : q < st.bcT.length
    · rcases hb : st.bcT[q]? with _ | ⟨t1, t2⟩
      · rw [List.getElem?_eq_none_iff] at hb; omega
      · simp only [hl, ↓reduceIte, hb, Option.map_some, incT]
        rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> simp
    · have hb : st.bcT[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
      simp only [hl, ↓reduceIte, hb, show q < st.bcT.length + (q + 1 - st.bcT.length) by omega,
        Option.map_some, incT]
      rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> simp
  · simp only [Ne.symm hq, ↓reduceIte, hq, false_and]
    by_cases hl : q < st.bcT.length
    · simp [hl]
    · have hb : st.bcT[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
      rw [hb]
      simp only [hl, ↓reduceIte, Option.map_eq_map, Option.map_none]
      (repeat' split) <;> simp_all <;> (rename_i h; obtain ⟨_, h1, h2⟩ := h; rw [← h1, ← h2])

theorem SlotSt.put_counts' (st : SlotSt) (p r x q r' : Nat) (hr : r = 1 ∨ r = 2)
    (hr' : r' = 1 ∨ r' = 2) :
    (st.put p r x).counts q r' =
      if q = p ∧ r' = r then incC x (st.counts q r') else st.counts q r' := by
  unfold SlotSt.counts
  rw [st.put_bc, List.getElem?_modify, getElem?_pad]
  by_cases hq : q = p
  · subst hq
    simp only [↓reduceIte, true_and]
    by_cases hl : q < st.bc.length
    · rcases hb : st.bc[q]? with _ | ⟨c1, c2⟩
      · rw [List.getElem?_eq_none_iff] at hb; omega
      · simp only [hl, ↓reduceIte, hb, Option.map_some, incBC]
        rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> simp
    · have hb : st.bc[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
      simp only [hl, ↓reduceIte, hb, show q < st.bc.length + (q + 1 - st.bc.length) by omega,
        Option.map_some, incBC]
      rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> simp
  · simp only [Ne.symm hq, ↓reduceIte, hq, false_and]
    by_cases hl : q < st.bc.length
    · simp [hl]
    · have hb : st.bc[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
      rw [hb]
      simp only [hl, ↓reduceIte, Option.map_eq_map, Option.map_none]
      (repeat' split) <;> simp_all <;> (rename_i h; obtain ⟨_, h1, h2⟩ := h; rw [← h1, ← h2])

theorem SlotSt.addProp_total' (st : SlotSt) (o : ObjV) (q r' : Nat) (hr' : r' = 1 ∨ r' = 2) :
    (st.addProp o).total q r' = if q = 0 ∧ r' = 1 then st.total q r' + 1 else st.total q r' := by
  unfold SlotSt.total
  show (match ((st.bcT ++ List.replicate (1 - st.bcT.length) (0, 0)).modify 0
      (fun p => (p.1 + 1, p.2)))[q]? with
    | some (t1, t2) => if r' = 1 then t1 else t2 | none => 0) = _
  rw [List.getElem?_modify, getElem?_pad]
  by_cases hq : q = 0
  · subst hq
    simp only [↓reduceIte, true_and]
    by_cases hl : 0 < st.bcT.length
    · rcases hb : st.bcT[0]? with _ | ⟨t1, t2⟩
      · rw [List.getElem?_eq_none_iff] at hb; omega
      · simp only [hl, ↓reduceIte, hb, Option.map_some]
        rcases hr' with rfl | rfl <;> simp
    · have hb : st.bcT[0]? = none := List.getElem?_eq_none_iff.2 (by omega)
      simp only [hl, ↓reduceIte, hb, show 0 < st.bcT.length + (1 - st.bcT.length) by omega,
        Option.map_some]
      rcases hr' with rfl | rfl <;> simp
  · simp only [Ne.symm hq, ↓reduceIte, hq, false_and]
    by_cases hl : q < st.bcT.length
    · simp [hl]
    · have hb : st.bcT[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
      rw [hb]
      simp only [hl, ↓reduceIte, Option.map_eq_map, Option.map_none]
      (repeat' split) <;> simp_all <;> (rename_i h; obtain ⟨_, h1, h2⟩ := h; rw [← h1, ← h2])

theorem addPropL_perm {P Q : List (ObjV × Nat)} (h : P.Perm Q) (o : ObjV) :
    (addPropL P o).Perm (addPropL Q o) := by
  unfold addPropL
  rw [h.any_eq]
  split
  · exact h.map _
  · exact h.append_right _

theorem groupProps_snoc (os : List ObjV) (o : ObjV) :
    groupProps (os ++ [o]) = addPropL (groupProps os) o := by
  unfold groupProps; rw [List.foldl_append]; rfl

/-! ## Tallies -/

theorem TallyOk.total {st : SlotSt} {ents : List Ent} (h : TallyOk st ents) {p r : Nat}
    (hr : r = 1 ∨ r = 2) : st.total p r = (tally ents (2 * p + r - 1)).length := by
  rcases hr with rfl | rfl
  · by_cases hp : p = 0
    · subst hp; exact h.1
    · exact (h.2.2 p 1 (Or.inl ⟨rfl, by omega⟩)).1
  · exact (h.2.2 p 2 (Or.inr rfl)).1

/-- `PutRecvBCMsgs(p, r, x)` with the counted message `e` of round `2p + r - 1` (a state of phase
`p ≥ 1`, or a vote). -/
theorem TallyOk.put {st : SlotSt} {ents : List Ent} (h : TallyOk st ents) {p r : Nat}
    (hr : (r = 1 ∧ 1 ≤ p) ∨ r = 2) (e : Ent) (he : e.1 = 2 * p + r - 1) :
    TallyOk (st.put p r e.2.2.2.value.toNat) (ents ++ [e]) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hr12 : r = 1 ∨ r = 2 := by omega
  have he0 : e.1 ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [SlotSt.put_total' _ _ _ _ _ _ hr12 (Or.inl rfl), tally_append, if_neg (by omega), h1]
    simp [he0]
  · rw [SlotSt.put_props, tally_append, if_neg he0, List.append_nil]; exact h2
  · intro q r' hq
    have hr'12 : r' = 1 ∨ r' = 2 := by omega
    obtain ⟨ht, hc⟩ := h3 q r' hq
    rw [SlotSt.put_total' _ _ _ _ _ _ hr12 hr'12, SlotSt.put_counts' _ _ _ _ _ _ hr12 hr'12,
      tally_append]
    by_cases hqp : q = p ∧ r' = r
    · obtain ⟨rfl, rfl⟩ := hqp
      simp only [and_self, ↓reduceIte, he, List.length_append, List.length_singleton, ht,
        List.map_append, List.map_cons, List.map_nil, hc, countsOf_snoc]
    · have hne : ¬ e.1 = 2 * q + r' - 1 := by omega
      simp only [hqp, ↓reduceIte, hne, List.append_nil, ht, hc, and_self]

/-- `PutRecvProposals(o)` with the counted proposal `e` (of round 0, carrying `o`). -/
theorem TallyOk.addProp {st : SlotSt} {ents : List Ent} (h : TallyOk st ents) (e : Ent)
    (he : e.1 = 0) (o : ObjV) (ho : e.2.2.2.obj = some o) :
    TallyOk (st.addProp o) (ents ++ [e]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [SlotSt.addProp_total' _ _ _ _ (Or.inl rfl), tally_append, if_pos he, h1]
    simp
  · show (addPropL st.props o).Perm _
    rw [tally_append, if_pos he, List.filterMap_append]
    simp only [List.filterMap_cons, ho, List.filterMap_nil]
    rw [groupProps_snoc]
    exact addPropL_perm h2 o
  · intro q r' hq
    have hr'12 : r' = 1 ∨ r' = 2 := by omega
    obtain ⟨ht, hc⟩ := h3 q r' hq
    have hne : ¬ e.1 = 2 * q + r' - 1 := by omega
    rw [SlotSt.addProp_total' _ _ _ _ hr'12, tally_append, if_neg hne, List.append_nil]
    refine ⟨?_, hc⟩
    rw [if_neg (by omega)]; exact ht

/-- Sorting the proposals' tallies (`RecvProposalsMajV/MajT`). -/
theorem TallyOk.sort {st : SlotSt} {ents : List Ent} (h : TallyOk st ents) :
    TallyOk { st with props := sortProps st.props } ents := by
  exact ⟨h.1, (List.mergeSort_perm _ _).trans h.2.1, h.2.2⟩

/-! ## Quorums: the frozen tally's proposals and values -/


/-- An object's id. -/
def objId (o : ObjV) : ObjId := (o.proId.toNat, o.proSeq.toNat)

theorem sameId_iff_objId (a b : ObjV) : a.sameId b = true ↔ objId a = objId b := by
  rw [sameId_true_iff]; unfold objId
  constructor
  · rintro ⟨h1, h2⟩; rw [h1, h2]
  · intro h; simp only [Prod.mk.injEq] at h
    exact ⟨BitVec.eq_of_toNat_eq h.2, BitVec.eq_of_toNat_eq h.1⟩

theorem sameId_false_objId (a b : ObjV) : a.sameId b = false ↔ objId a ≠ objId b := by
  rw [ne_eq, ← sameId_iff_objId]; simp

/-- `groupProps`' tallies: distinct ids, each an object of `os` with its count, every object's id
tallied. -/
def GroupOk (os : List ObjV) (ps : List (ObjV × Nat)) : Prop :=
  distinctIds ps ∧ (∀ t ∈ ps, t.1 ∈ os ∧ t.2 = (os.map objId).count (objId t.1)) ∧
  ∀ o ∈ os, ∃ t ∈ ps, objId t.1 = objId o

theorem groupOk_snoc {os : List ObjV} {ps : List (ObjV × Nat)} (h : GroupOk os ps) (o : ObjV) :
    GroupOk (os ++ [o]) (addPropL ps o) := by
  obtain ⟨hd, hc, hcov⟩ := h
  unfold addPropL
  split
  · rename_i hany
    obtain ⟨t0, ht0, hs0⟩ := List.any_eq_true.1 hany
    rw [sameId_iff_objId] at hs0
    refine ⟨?_, ?_, ?_⟩
    · unfold distinctIds at hd ⊢
      rw [List.map_map]
      have : (Prod.fst ∘ fun t : ObjV × Nat => if t.1.sameId o then (t.1, t.2 + 1) else t) =
          Prod.fst := by
        funext t; simp only [Function.comp]; split <;> rfl
      rw [this]; exact hd
    · intro t' ht'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
      obtain ⟨hm, hcnt⟩ := hc t ht
      split
      · rename_i hs
        rw [sameId_iff_objId] at hs
        simp only [List.mem_append, hm, true_or, List.map_append, List.map_cons, List.map_nil,
          List.count_append, hcnt, true_and]
        rw [List.count_singleton, hs]; simp
      · rename_i hs
        have hs' : objId t.1 ≠ objId o := fun he => hs ((sameId_iff_objId _ _).2 he)
        simp only [List.mem_append, hm, true_or, List.map_append, List.map_cons, List.map_nil,
          List.count_append, hcnt, true_and, List.count_singleton]
        simp [Ne.symm hs']
    · intro o' ho'
      rcases List.mem_append.1 ho' with ho' | ho'
      · obtain ⟨t, ht, he⟩ := hcov o' ho'
        refine ⟨_, List.mem_map_of_mem ht, ?_⟩
        split <;> exact he
      · simp at ho'; subst ho'
        refine ⟨_, List.mem_map_of_mem ht0, ?_⟩
        rw [if_pos ((sameId_iff_objId _ _).2 hs0)]; exact hs0
  · rename_i hany
    have hno : ∀ t ∈ ps, objId t.1 ≠ objId o := by
      intro t ht he
      apply hany
      exact List.any_eq_true.2 ⟨t, ht, (sameId_iff_objId _ _).2 he⟩
    have h0 : (os.map objId).count (objId o) = 0 := by
      rw [List.count_eq_zero]
      intro hm
      obtain ⟨o', ho', he⟩ := List.mem_map.1 hm
      obtain ⟨t, ht, he'⟩ := hcov o' ho'
      exact hno t ht (he'.trans he)
    refine ⟨?_, ?_, ?_⟩
    · rw [distinctIds_iff] at hd ⊢
      rw [List.pairwise_append]
      refine ⟨hd, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      exact (sameId_false_objId _ _).2 (hno a ha)
    · intro t' ht'
      rcases List.mem_append.1 ht' with ht | ht
      · obtain ⟨hm, hcnt⟩ := hc t' ht
        refine ⟨List.mem_append_left _ hm, ?_⟩
        simp only [List.map_append, List.map_cons, List.map_nil, List.count_append, hcnt,
          List.count_singleton]
        simp [Ne.symm (hno t' ht)]
      · simp at ht; subst ht
        refine ⟨by simp, ?_⟩
        simp only [List.map_append, List.map_cons, List.map_nil, List.count_append, h0,
          List.count_singleton]
        simp
    · intro o' ho'
      rcases List.mem_append.1 ho' with ho' | ho'
      · obtain ⟨t, ht, he⟩ := hcov o' ho'
        exact ⟨t, List.mem_append_left _ ht, he⟩
      · simp at ho'; subst ho'
        exact ⟨(o', 1), by simp, rfl⟩

theorem groupOk_foldl : ∀ (os os0 : List ObjV) (ps : List (ObjV × Nat)), GroupOk os0 ps →
    GroupOk (os0 ++ os) (os.foldl addPropL ps)
  | [], os0, ps, h => by simpa using h
  | o :: os, os0, ps, h => by
    have := groupOk_foldl os (os0 ++ [o]) (addPropL ps o) (groupOk_snoc h o)
    simpa using this

theorem groupOk_groupProps (os : List ObjV) : GroupOk os (groupProps os) := by
  have := groupOk_foldl os [] [] ⟨by simp [distinctIds], by simp, by simp⟩
  simpa [groupProps] using this

/-- The first tally after sorting: an object of `os` with the largest count. -/
theorem props_head {props : List (ObjV × Nat)} {os : List ObjV} (hp : props.Perm (groupProps os))
    (hne : os ≠ []) :
    props ≠ [] ∧ ∃ o k, (sortProps props).head? = some (o, k) ∧ o ∈ os ∧
      k = (os.map objId).count (objId o) ∧ ∀ id, (os.map objId).count id ≤ k := by
  obtain ⟨hd, hc, hcov⟩ := groupOk_groupProps os
  have hd' : distinctIds props := distinctIds_perm hd hp.symm
  have hsp : (sortProps props).Perm props := List.mergeSort_perm _ _
  have hsorted := sortProps_pairwise props hd'
  have hmem : ∀ t, t ∈ sortProps props ↔ t ∈ groupProps os := fun t =>
    (hsp.trans hp).mem_iff
  obtain ⟨o0, ho0⟩ := List.exists_mem_of_ne_nil os hne
  obtain ⟨t0, ht0, _⟩ := hcov o0 ho0
  have hne' : props ≠ [] := by
    intro h; rw [h] at hp; have := hp.symm.subset ht0; simp at this
  refine ⟨hne', ?_⟩
  rcases hs : sortProps props with _ | ⟨⟨o, k⟩, rest⟩
  · have := (hmem t0).2 ht0; rw [hs] at this; simp at this
  · have hh : (o, k) ∈ groupProps os := (hmem _).1 (by rw [hs]; simp)
    obtain ⟨hmo, hk⟩ := hc _ hh
    refine ⟨o, k, rfl, hmo, hk, ?_⟩
    intro id
    by_cases hz : (os.map objId).count id = 0
    · omega
    have hin : id ∈ os.map objId := List.count_pos_iff.1 (by omega)
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hin
    obtain ⟨t, ht, he⟩ := hcov o' ho'
    obtain ⟨_, htc⟩ := hc t ht
    rw [← he, ← htc]
    have ht' : t ∈ (o, k) :: rest := by rw [← hs]; exact (hmem t).2 ht
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact Nat.le_refl _
    · rw [hs] at hsorted
      have := List.rel_of_pairwise_cons hsorted ht'
      rw [tallyLt_iff] at this
      simp only at this
      omega




theorem majV_le1 (vs : List Nat) : majV vs ≤ 1 := by unfold majV; split <;> omega

theorem majT_eq_count (vs : List Nat) : majT vs = vs.count (majV vs) := by
  unfold majT majV; split <;> rfl

theorem majT_le_length (vs : List Nat) : majT vs ≤ vs.length := by
  rw [majT_eq_count]; exact List.count_le_length

theorem countsOf_majT (vs : List Nat) : (countsOf vs).majT = majT vs := rfl
theorem countsOf_majV (vs : List Nat) : (countsOf vs).majV = majV vs := rfl

/-- The senders of the messages of `W` with value `b`. -/
def sendersOf {α : Type} [BEq α] (W : List (Nat × α)) (b : α) : List Nat :=
  (W.filter (fun x => x.2 == b)).map Prod.fst

theorem sendersOf_spec {α : Type} [BEq α] [LawfulBEq α] {c : RCfg} {W : List (Nat × α)}
    (hS : Senders c W) (b : α) :
    ((sendersOf W b).Nodup ∧ ∀ X ∈ sendersOf W b, X < c.n) ∧
      (sendersOf W b).length = (W.map Prod.snd).count b ∧ ∀ X ∈ sendersOf W b, (X, b) ∈ W := by
  unfold sendersOf
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact hS.1.sublist ((List.filter_sublist).map _)
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hX
    exact hS.2 x (List.mem_filter.1 hx).1
  · rw [List.length_map, List.count, List.countP_map, List.countP_eq_length_filter]
    congr 1
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hX
    have := List.mem_filter.1 hx
    have hb : x.2 = b := beq_iff_eq.1 this.2
    rw [← hb]; exact this.1

/-- The facts a list of keyed values gives. -/
theorem facts_of_mem {M : Facts} {S : List (FKey × FVal)} (h : ∀ kv ∈ S, M kv.1 = some kv.2)
    {k : FKey} {v : FVal} (hm : (k, v) ∈ S) : M k = some v := h _ hm



section rules
variable {c : RCfg}

/-- The facts of a quorum of states (`r = 1`) or votes (`r = 2`) of phase `p` of slot `s`. -/
def bitFacts (s p r : Nat) (W : List (Nat × Nat)) : List (FKey × FVal) :=
  W.map (fun x => ((if r = 1 then FKey.st x.1 s p else FKey.vt x.1 s p), FVal.bit x.2))

/-- The facts of a quorum of proposals of slot `s`. -/
def propFacts (s : Nat) (W : List (Nat × ObjId)) : List (FKey × FVal) :=
  W.map (fun x => (FKey.prop x.1 s, FVal.obj x.2))

/-- The configuration's fact. -/
def cfgFact (c : RCfg) : FKey × FVal := (.cfg, .cfgv c)

theorem bitFacts_mem {M : Facts} {s p r : Nat} {W : List (Nat × Nat)}
    (h : ∀ kv ∈ bitFacts s p r W, M kv.1 = some kv.2) :
    ∀ x ∈ W, M (if r = 1 then .st x.1 s p else .vt x.1 s p) = some (.bit x.2) :=
  fun x hx => h _ (List.mem_map_of_mem (f := fun x : Nat × Nat =>
    ((if r = 1 then FKey.st x.1 s p else FKey.vt x.1 s p), FVal.bit x.2)) hx)

theorem propFacts_mem {M : Facts} {s : Nat} {W : List (Nat × ObjId)}
    (h : ∀ kv ∈ propFacts s W, M kv.1 = some kv.2) :
    ∀ x ∈ W, M (.prop x.1 s) = some (.obj x.2) :=
  fun x hx => h _ (List.mem_map_of_mem (f := fun x : Nat × ObjId => (FKey.prop x.1 s, FVal.obj x.2)) hx)

theorem cfgOf_of {M : Facts} {S : List (FKey × FVal)} (h : ∀ kv ∈ cfgFact c :: S, M kv.1 = some kv.2) :
    CfgOf M c := h _ List.mem_cons_self

theorem facts_tail {M : Facts} {a : FKey × FVal} {S : List (FKey × FVal)}
    (h : ∀ kv ∈ a :: S, M kv.1 = some kv.2) : ∀ kv ∈ S, M kv.1 = some kv.2 :=
  fun kv hkv => h kv (List.mem_cons_of_mem _ hkv)

theorem majProp_of {M : Facts} {s : Nat} {W : List (Nat × ObjId)} (hS : Senders c W)
    (hf : ∀ x ∈ W, M (.prop x.1 s) = some (.obj x.2)) {id : ObjId}
    (hc : (W.map Prod.snd).count id ≥ c.maj) : MajProp c M s id := by
  obtain ⟨h1, h2, h3⟩ := sendersOf_spec hS id
  exact ⟨sendersOf W id, h1, by rw [h2]; exact hc, fun X hX => hf _ (h3 X hX)⟩

theorem decEv_props {M : Facts} {s : Nat} {W : List (Nat × ObjId)} (hS : Senders c W)
    (hf : ∀ x ∈ W, M (.prop x.1 s) = some (.obj x.2)) {id : ObjId}
    (hc : (W.map Prod.snd).count id ≥ c.mpf) : DecEvidence c M s (.obj id) := by
  obtain ⟨h1, h2, h3⟩ := sendersOf_spec hS id
  exact Or.inr (Or.inr ⟨id, sendersOf W id, h1, by rw [h2]; exact hc, fun X hX => hf _ (h3 X hX),
    rfl⟩)

theorem decEv_votes {M : Facts} {s p : Nat} {W : List (Nat × Nat)} (hS : Senders c W)
    (hf : ∀ x ∈ W, M (.vt x.1 s p) = some (.bit x.2)) (ht : majT (W.map Prod.snd) ≥ c.fp1)
    {d : DVal} (hd : BitDec c M s (majV (W.map Prod.snd)) d) : DecEvidence c M s d := by
  obtain ⟨h1, h2, h3⟩ := sendersOf_spec hS (majV (W.map Prod.snd))
  exact Or.inl ⟨p, _, sendersOf W _, h1, by rw [h2, ← majT_eq_count]; exact ht,
    fun X hX => hf _ (h3 X hX), hd⟩

theorem decEv_states {M : Facts} {s p : Nat} (hp : p ≥ 1) {W : List (Nat × Nat)} (hS : Senders c W)
    (hf : ∀ x ∈ W, M (.st x.1 s p) = some (.bit x.2)) (ht : majT (W.map Prod.snd) ≥ c.mpf)
    {d : DVal} (hd : BitDec c M s (majV (W.map Prod.snd)) d) : DecEvidence c M s d := by
  obtain ⟨h1, h2, h3⟩ := sendersOf_spec hS (majV (W.map Prod.snd))
  exact Or.inr (Or.inl ⟨p, _, sendersOf W _, hp, h1, by rw [h2, ← majT_eq_count]; exact ht,
    fun X hX => hf _ (h3 X hX), hd⟩)

theorem bitDec_null {M : Facts} {s : Nat} : BitDec c M s 0 .null :=
  ⟨by omega, fun _ => rfl, fun h => by omega⟩

theorem bitDec_obj {M : Facts} {s : Nat} {id : ObjId} (hm : MajProp c M s id) :
    BitDec c M s 1 (.obj id) :=
  ⟨by omega, fun h => by omega, fun _ => ⟨id, rfl, hm⟩⟩

/-- The vote of a phase `p ≥ 1` after a quorum `W` of states. -/
theorem vote_valid {k s p : Nat} {W : List (Nat × Nat)} (hk : k < c.n) (hp : p ≠ 0)
    (hS : Senders c W) (hl : W.length = c.q) :
    ∀ M, Valid M → (∀ kv ∈ cfgFact c :: bitFacts s p 1 W, M kv.1 = some kv.2) →
      M (.vt k s p) = none →
      Valid (M.set (.vt k s p)
        (.bit (if majT (W.map Prod.snd) ≥ c.maj then majV (W.map Prod.snd) else 2))) := by
  intro M hM hS' hfree
  have hf := bitFacts_mem (facts_tail hS')
  apply Valid.insert M (cfgOf_of hS') hM _ _ hfree
  · simp only [Justified]
    refine ⟨hk, ?_⟩
    split
    · have := majV_le1 (W.map Prod.snd); omega
    · omega
  · exact ⟨by simp, fun id X r => ⟨by simp, by simp⟩⟩
  · intro X' s' p' b' h; cases h
  · intro X' s' p' b' h hb
    cases h; cases hb
    unfold VoteOk
    simp only [hp, ↓reduceIte]
    exact ⟨W, ⟨hS, hl, hf⟩, rfl⟩
  · intro s' h; cases h
  · intro X' s' h; cases h

/-- The vote `1` of phase 0 after a majority of proposals of one object. -/
theorem vote0_one_valid {k s : Nat} {W : List (Nat × ObjId)} (hk : k < c.n) (hS : Senders c W)
    {id : ObjId} (hc : (W.map Prod.snd).count id ≥ c.maj) :
    ∀ M, Valid M → (∀ kv ∈ cfgFact c :: propFacts s W, M kv.1 = some kv.2) →
      M (.vt k s 0) = none → Valid (M.set (.vt k s 0) (.bit 1)) := by
  intro M hM hS' hfree
  have hf := propFacts_mem (facts_tail hS')
  apply Valid.insert M (cfgOf_of hS') hM _ _ hfree
  · simp only [Justified]; exact ⟨hk, by omega⟩
  · exact ⟨by simp, fun id X r => ⟨by simp, by simp⟩⟩
  · intro X' s' p' b' h; cases h
  · intro X' s' p' b' h hb
    cases h; cases hb
    unfold VoteOk
    simp only [↓reduceIte]
    exact Or.inl ⟨trivial, id, majProp_of hS hf hc⟩
  · intro s' h; cases h
  · intro X' s' h; cases h

theorem filter_snd_length {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (W : List (Nat × α)) (b : α) :
    (W.filter (·.2 = b)).length = (W.map Prod.snd).count b := by
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp]
  by_cases h : x.2 = b <;> simp [h]

/-- The vote `?` of phase 0 after a quorum of proposals where no object has a majority. -/
theorem vote0_q_valid {k s : Nat} {W : List (Nat × ObjId)} (hk : k < c.n) (hS : Senders c W)
    (hl : W.length = c.q) (hlt : ∀ id, (W.map Prod.snd).count id < c.maj) :
    ∀ M, Valid M → (∀ kv ∈ cfgFact c :: propFacts s W, M kv.1 = some kv.2) →
      M (.vt k s 0) = none → Valid (M.set (.vt k s 0) (.bit 2)) := by
  intro M hM hS' hfree
  have hf := propFacts_mem (facts_tail hS')
  apply Valid.insert M (cfgOf_of hS') hM _ _ hfree
  · simp only [Justified]; exact ⟨hk, by omega⟩
  · exact ⟨by simp, fun id X r => ⟨by simp, by simp⟩⟩
  · intro X' s' p' b' h; cases h
  · intro X' s' p' b' h hb
    cases h; cases hb
    unfold VoteOk
    simp only [↓reduceIte]
    refine Or.inr ⟨trivial, W, ⟨hS, hl, hf⟩, fun id => ?_⟩
    rw [filter_snd_length]; exact hlt id
  · intro s' h; cases h
  · intro X' s' h; cases h

/-- The state of phase `p + 1` after a quorum `W` of votes of phase `p` that does not decide. -/
theorem state_valid {k s p B : Nat} {W : List (Nat × Nat)} (hk : k < c.n) (hS : Senders c W)
    (hl : W.length = c.q) (hlt : majT (W.map Prod.snd) < c.fp1)
    (hB : if majT (W.map Prod.snd) ≥ 1 then B = majV (W.map Prod.snd)
      else (if p = 0 then B = 0 else B ≤ 1)) :
    ∀ M, Valid M → (∀ kv ∈ cfgFact c :: bitFacts s p 2 W, M kv.1 = some kv.2) →
      M (.st k s (p + 1)) = none → Valid (M.set (.st k s (p + 1)) (.bit B)) := by
  intro M hM hS' hfree
  have hf := bitFacts_mem (facts_tail hS')
  have hB1 : B ≤ 1 := by
    split at hB
    · rw [hB]; exact majV_le1 _
    · split at hB <;> omega
  apply Valid.insert M (cfgOf_of hS') hM _ _ hfree
  · simp only [Justified]; exact ⟨hk, hB1⟩
  · exact ⟨by simp, fun id X r => ⟨by simp, by simp⟩⟩
  · intro X' s' p' b' h hb
    cases h; cases hb
    refine ⟨by omega, ?_⟩
    simp only [Nat.add_sub_cancel]
    exact ⟨W, ⟨hS, hl, hf⟩, hlt, hB⟩
  · intro X' s' p' b' h; cases h
  · intro s' h; cases h
  · intro X' s' h; cases h

end rules


/-! ### A frozen tally's quorum -/

/-- The (sender, value) pairs of counted states or votes. -/
def bitPairs (T : List Ent) : List (Nat × Nat) := T.map (fun e => (e.2.1, e.2.2.2.value.toNat))

/-- The (sender, object id) pairs of counted proposals. -/
def propPairs (T : List Ent) : List (Nat × ObjId) :=
  T.filterMap (fun e => e.2.2.2.obj.map (fun o => (e.2.1, objId o)))

theorem bitPairs_snd (T : List Ent) :
    (bitPairs T).map Prod.snd = T.map (fun e => e.2.2.2.value.toNat) := by
  unfold bitPairs; rw [List.map_map]; rfl

theorem bitPairs_length (T : List Ent) : (bitPairs T).length = T.length := by
  unfold bitPairs; simp

theorem bitPairs_senders {c : RCfg} {T : List Ent} (hX : ∀ e ∈ T, e.2.1 < c.n)
    (hnd : (T.map (fun e => e.2.1)).Nodup) : Senders c (bitPairs T) := by
  unfold Senders bitPairs
  refine ⟨by rw [List.map_map]; exact hnd, ?_⟩
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  exact hX e he

theorem propPairs_snd : ∀ T : List Ent,
    (propPairs T).map Prod.snd = (T.filterMap (fun e => e.2.2.2.obj)).map objId
  | [] => rfl
  | e :: T => by
    have ih := propPairs_snd T
    unfold propPairs at ih ⊢
    rcases ho : e.2.2.2.obj with _ | o <;> simp [List.filterMap_cons, ho, ih]

theorem propPairs_fst_sublist : ∀ T : List Ent,
    ((propPairs T).map Prod.fst).Sublist (T.map (fun e => e.2.1))
  | [] => List.Sublist.slnil
  | e :: T => by
    have ih := propPairs_fst_sublist T
    unfold propPairs at ih ⊢
    rcases ho : e.2.2.2.obj with _ | o
    · simp only [List.filterMap_cons, ho, Option.map_none, List.map_cons]
      exact ih.cons _
    · simp only [List.filterMap_cons, ho, Option.map_some, List.map_cons]
      exact ih.cons₂ _

theorem propPairs_mem {T : List Ent} {x : Nat × ObjId} (h : x ∈ propPairs T) :
    ∃ e ∈ T, ∃ o, e.2.2.2.obj = some o ∧ x = (e.2.1, objId o) := by
  unfold propPairs at h
  obtain ⟨e, he, hx⟩ := List.mem_filterMap.1 h
  rcases ho : e.2.2.2.obj with _ | o
  · rw [ho] at hx; cases hx
  · rw [ho] at hx; simp only [Option.map_some, Option.some.injEq] at hx
    exact ⟨e, he, o, ho, hx.symm⟩

theorem propPairs_length : ∀ T : List Ent, (∀ e ∈ T, e.2.2.2.obj ≠ none) →
    (propPairs T).length = T.length
  | [], _ => rfl
  | e :: T, h => by
    have ih := propPairs_length T (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    unfold propPairs at ih ⊢
    rcases ho : e.2.2.2.obj with _ | o
    · exact absurd ho (h e List.mem_cons_self)
    · simp [List.filterMap_cons, ho, ih]

theorem propPairs_senders {c : RCfg} {T : List Ent} (hX : ∀ e ∈ T, e.2.1 < c.n)
    (hnd : (T.map (fun e => e.2.1)).Nodup) : Senders c (propPairs T) := by
  refine ⟨hnd.sublist (propPairs_fst_sublist T), ?_⟩
  intro x hx
  obtain ⟨e, he, o, _, rfl⟩ := propPairs_mem hx
  exact hX e he

/-- The counts of a frozen round read the majority of its values. -/
theorem TallyOk.majT_eq {st : SlotSt} {ents : List Ent} (h : TallyOk st ents) {p r : Nat}
    (hr : (r = 1 ∧ 1 ≤ p) ∨ r = 2) :
    (st.counts p r).majT = majT ((tally ents (2 * p + r - 1)).map (fun e => e.2.2.2.value.toNat)) ∧
    (st.counts p r).majV = majV ((tally ents (2 * p + r - 1)).map (fun e => e.2.2.2.value.toNat)) := by
  rw [(h.2.2 p r hr).2]; exact ⟨rfl, rfl⟩

/-- The proposals' tallies of a round with proposals `os`: the first after sorting is an object
of `os` with the largest count. -/
theorem TallyOk.props_head {st : SlotSt} {ents : List Ent} (h : TallyOk st ents)
    (hne : (tally ents 0).filterMap (fun e => e.2.2.2.obj) ≠ []) :
    st.props ≠ [] ∧ ∃ o k, (sortProps st.props).head? = some (o, k) ∧
      o ∈ (tally ents 0).filterMap (fun e => e.2.2.2.obj) ∧
      k = (((tally ents 0).filterMap (fun e => e.2.2.2.obj)).map objId).count (objId o) ∧
      ∀ id, (((tally ents 0).filterMap (fun e => e.2.2.2.obj)).map objId).count id ≤ k :=
  _root_.Perennial.rabia.roles.server.layers.consensus.props_head h.2.1 hne

/-! ## The slot invariant's transitions -/

/-- The handler counts message `e = (ρ, X, j, m)` (round `ρ` not full, `X` not counted at `ρ`): the
round becomes full exactly when it now has two, and then its notification is pending. -/
theorem SlotOk.count {s : Nat} {st st' : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql none exd dl rl) (e : Ent) (hX : e.2.1 < cf.n)
    (hm : msgRound e.2.2.2 = some (s, e.1)) (hlt : (tally ents e.1).length < cf.q)
    (hnew : e.2.1 ∉ (tally ents e.1).map (fun e => e.2.1))
    (htally : TallyOk st' (ents ++ [e])) (hd : st'.isDone = st.isDone)
    (hr : st'.hasRecvDec = st.hasRecvDec) :
    SlotOk cf s st' (ents ++ [e]) ql
      (if (tally (ents ++ [e]) e.1).length = cf.q then some (some e.1) else none) exd dl rl := by
  obtain ⟨_, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨htally, ?_, ?_, h4, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h2 x hx
    · exact ⟨hX, hm⟩
  · intro ρ
    rw [tally_append]
    by_cases hρ : e.1 = ρ
    · subst hρ
      simp only [↓reduceIte, List.length_append, List.length_singleton, List.map_append,
        List.map_cons, List.map_nil]
      refine ⟨by omega, ?_⟩
      rw [List.nodup_append]
      refine ⟨(h3 e.1).2, by simp, ?_⟩
      intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact hnew ha
    · simp only [hρ, ↓reduceIte, List.append_nil]; exact h3 ρ
  · intro ρ
    have hlen : (tally (ents ++ [e]) e.1).length = (tally ents e.1).length + 1 := by
      rw [tally_append]; simp
    have h5' := h5 ρ
    by_cases hρ : e.1 = ρ
    · subst hρ
      rw [hlen]
      by_cases hf : (tally ents e.1).length + 1 = cf.q
      · simp [hf]
      · have : ¬ some e.1 ∈ ql := fun hin => by have := h5'.1 (Or.inl hin); omega
        simp [hf, this]
    · rw [hlen, tally_append, if_neg hρ, List.append_nil, ← h5']
      split <;> simp [hρ]
  · rw [hr, h6]
    constructor
    · rintro ⟨h1, _⟩; exact ⟨h1, by split <;> simp⟩
    · rintro ⟨h1, _⟩; exact ⟨h1, by simp⟩
  · rw [hd]; exact h7
  · intro h; rw [hd]; exact h8 h
  · intro h; rw [hr]; exact h9 h

/-- A round `ρ` whose `q` distinct senders were each counted at `ρ` (or `ρ` was notified) is
notified (with no pending notification). -/
theorem SlotOk.prev_notified {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {exd : Bool} {dl rl : List Unit} (h : SlotOk cf s st ents ql none exd dl rl) {ρ : Nat}
    (Xs : List Nat) (hnd : Xs.Nodup) (hlen : Xs.length = cf.q)
    (hw : ∀ X ∈ Xs, (∃ j m, (ρ, X, j, m) ∈ ents) ∨ some ρ ∈ ql) : some ρ ∈ ql := by
  by_cases hin : some ρ ∈ ql
  · exact hin
  have hsub : Xs ⊆ (tally ents ρ).map (fun e => e.2.1) := by
    intro X hX
    rcases hw X hX with ⟨j, m, hm⟩ | h'
    · exact List.mem_map.2 ⟨(ρ, X, j, m), by simp [tally, hm], rfl⟩
    · exact absurd h' hin
  have hle : Xs.length ≤ ((tally ents ρ).map (fun e => e.2.1)).length :=
    (List.subperm_of_subset hnd hsub).length_le
  rw [List.length_map] at hle
  have h2 := (h.2.2.1 ρ).1
  have := (h.2.2.2.2.1 ρ).2 (by omega)
  simpa using this

/-- The pending notification of round `ρ` is sent (rounds in order: `ρ - 1` notified, `ρ` not). -/
theorem SlotOk.notify {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {exd : Bool} {dl rl : List Unit} {ρ : Nat} (h : SlotOk cf s st ents ql (some (some ρ)) exd dl rl)
    (hprev : ρ = 0 ∨ some (ρ - 1) ∈ ql) (hnot : some ρ ∉ ql) :
    SlotOk cf s st ents (ql ++ [some ρ]) none exd dl rl ∧
    (ql.filterMap id) = List.range ρ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hmem : ∀ n, n ∈ ql.filterMap id ↔ some n ∈ ql := by
    intro n; simp [List.mem_filterMap]
  have hn : (ql.filterMap id).length = ρ := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_lt; intro hlt
      apply hnot; rw [← hmem, h4]; simp [hlt]
    · rcases hprev with rfl | hp
      · omega
      · rw [← hmem, h4] at hp; simp at hp; omega
  have hfm : ql.filterMap id = List.range ρ := by rw [h4, hn]
  refine ⟨⟨h1, h2, h3, ?_, ?_, ?_, h7, h8, h9⟩, hfm⟩
  · rw [List.filterMap_append, hfm]; simp [List.range_succ]
  · intro ρ'
    rw [← h5 ρ']
    simp only [List.mem_append, List.mem_singleton, Option.some.injEq, reduceCtorEq, or_false]
    constructor
    · rintro (h | rfl) <;> simp_all
    · rintro (h | h) <;> simp_all
  · rw [h6]; simp

/-- A round not full is not notified (nor pending, with no pending notification). -/
theorem SlotOk.not_notified {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {pend : Option (Option Nat)} {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql pend exd dl rl) {ρ : Nat} (hlt : (tally ents ρ).length < cf.q) :
    some ρ ∉ ql := by
  intro hin
  have := (h.2.2.2.2.1 ρ).1 (Or.inl hin)
  omega

/-- The decision's notification: sent when `hasRecvDec` is false (then none was sent), pending until
`SetHasRecvDec`. -/
theorem SlotOk.dec_send {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {exd : Bool} {dl rl : List Unit} (h : SlotOk cf s st ents ql none exd dl rl)
    (hrd : st.hasRecvDec = false) :
    none ∉ ql ∧ SlotOk cf s st ents (ql ++ [none]) (some none) exd dl rl := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hn : none ∉ ql := by
    intro hin; rw [hrd] at h6; exact absurd (h6.2 ⟨hin, by simp⟩) (by simp)
  refine ⟨hn, h1, h2, h3, ?_, ?_, ?_, h7, h8, h9⟩
  · rw [List.filterMap_append]; simp only [List.filterMap_cons, id, List.filterMap_nil,
      List.append_nil]; exact h4
  · intro ρ; rw [← h5 ρ]; simp
  · rw [hrd]; simp

theorem SlotOk.dec_set {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {exd : Bool} {dl rl : List Unit} (h : SlotOk cf s st ents ql (some none) exd dl rl)
    (hin : none ∈ ql) :
    SlotOk cf s { st with hasRecvDec := true } ents ql none exd dl rl := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, h7, h8, fun _ => rfl⟩
  · intro ρ; rw [← h5 ρ]; simp
  · simp [hin]

end Perennial.rabia.roles.server.layers.consensus
