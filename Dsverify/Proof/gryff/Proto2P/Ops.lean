/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Ops.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): the client operations of a history (`pure.ops`) and its replies
(`extsAt`, `replyAt`, `RepliesTo`) under extension of the history.
-/
module

public import Dsverify.Proof.gryff.Proto2P.Tokens

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure

theorem sintZ_inj {a b : w32} (h : sint.Z a = sint.Z b) : a = b := BitVec.toInt_inj.1 h

/-- The operation created at label `g` of `l`, if any. -/
noncomputable def opAt (l : List Label) (g : Nat) : Option Op :=
  match l[g]? with
  | some (r, e) => e.clientReq.map fun x =>
      { g, r, j := (projR (l.take g) r).length, cid := x.1, rid := x.2.1, inp := x.2.2 }
  | none => none

theorem ops_eq (l : List Label) : ops l = (List.range l.length).filterMap (opAt l) := rfl

theorem opAt_append (l l' : List Label) {g : Nat} (hg : g < l.length) :
    opAt (l ++ l') g = opAt l g := by
  unfold opAt
  rw [List.getElem?_append_left hg, List.take_append_of_le_length (Nat.le_of_lt hg)]

theorem opAt_spec {l : List Label} {g : Nat} {o : Op} (h : opAt l g = some o) :
    o.g = g ∧ g < l.length ∧ ∃ e, l[g]? = some (o.r, e) ∧ e.clientReq = some (o.cid, o.rid, o.inp) ∧
      o.j = (projR (l.take g) o.r).length := by
  unfold opAt at h
  rcases hl : l[g]? with _ | ⟨r, e⟩
  · rw [hl] at h; cases h
  · rw [hl] at h
    simp only at h
    rcases hc : e.clientReq with _ | ⟨cid, rid, i⟩
    · rw [hc] at h; cases h
    · rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨rfl, (List.getElem?_eq_some_iff.1 hl).1, e, rfl, hc, rfl⟩

theorem mem_ops {l : List Label} {o : Op} : o ∈ ops l ↔ opAt l o.g = some o := by
  rw [ops_eq, List.mem_filterMap]
  constructor
  · rintro ⟨g, -, hg⟩
    have := (opAt_spec hg).1
    rw [this]; exact hg
  · intro h
    exact ⟨o.g, List.mem_range.2 (opAt_spec h).2.1, h⟩

theorem ops_g_lt {l : List Label} {o : Op} (h : o ∈ ops l) : o.g < l.length :=
  (opAt_spec (mem_ops.1 h)).2.1

theorem ops_g_inj {l : List Label} {o o' : Op} (h : o ∈ ops l) (h' : o' ∈ ops l)
    (hg : o.g = o'.g) : o = o' := by
  have h1 := mem_ops.1 h
  have h2 := mem_ops.1 h'
  rw [hg, h2] at h1
  exact (Option.some.inj h1).symm

theorem ops_pairwise (l : List Label) : (ops l).Pairwise (fun a b => a.g < b.g) := by
  rw [ops_eq, List.pairwise_filterMap]
  refine List.pairwise_lt_range.imp ?_
  intro a b hab x hx y hy
  rw [(opAt_spec hx).1, (opAt_spec hy).1]; exact hab

theorem ops_append (l l' : List Label) :
    ∃ X, ops (l ++ l') = ops l ++ X ∧ ∀ o ∈ X, l.length ≤ o.g := by
  rw [ops_eq, ops_eq, List.length_append, List.range_add, List.filterMap_append]
  refine ⟨List.filterMap (opAt (l ++ l')) (List.map (fun x => l.length + x) (List.range l'.length)),
    ?_, ?_⟩
  · congr 1
    exact filterMap_congr' (fun g hg => opAt_append l l' (List.mem_range.1 hg))
  · intro o ho
    rw [List.mem_filterMap] at ho
    obtain ⟨g, hg, ho⟩ := ho
    rw [List.mem_map] at hg
    obtain ⟨x, -, rfl⟩ := hg
    rw [(opAt_spec ho).1]; omega

theorem ops_mono {l l' : List Label} {o : Op} (h : o ∈ ops l) : o ∈ ops (l ++ l') := by
  obtain ⟨X, hX, -⟩ := ops_append l l'
  rw [hX]; exact List.mem_append_left _ h

theorem ops_of_append {l l' : List Label} {o : Op} (h : o ∈ ops (l ++ l'))
    (hg : o.g < l.length) : o ∈ ops l := by
  obtain ⟨X, hX, hX2⟩ := ops_append l l'
  rw [hX] at h
  rcases List.mem_append.1 h with h | h
  · exact h
  · exact absurd (hX2 o h) (by omega)

/-- The operation a label creates. -/
noncomputable def newOp (l : List Label) (k : Fin 3) (e : Ev) : Option Op :=
  e.clientReq.map fun x =>
    { g := l.length, r := k, j := (projR l k).length, cid := x.1, rid := x.2.1, inp := x.2.2 }

theorem ops_snoc (l : List Label) (k : Fin 3) (e : Ev) :
    ops (l ++ [(k, e)]) = ops l ++ (newOp l k e).toList := by
  rw [ops_eq, ops_eq, List.length_append, List.length_singleton, List.range_succ,
    List.filterMap_append]
  congr 1
  · exact filterMap_congr' (fun g hg => opAt_append l _ (List.mem_range.1 hg))
  · simp only [List.filterMap_cons, List.filterMap_nil]
    have : opAt (l ++ [(k, e)]) l.length = newOp l k e := by
      unfold opAt newOp
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      simp only [List.getElem?_cons_zero]
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    rw [this]
    cases newOp l k e <;> rfl

theorem mem_ops_snoc {l : List Label} {k : Fin 3} {e : Ev} {o : Op} :
    o ∈ ops (l ++ [(k, e)]) ↔ o ∈ ops l ∨ newOp l k e = some o := by
  rw [ops_snoc, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; cases h' : newOp l k e with
      | none => rw [h'] at h; cases h
      | some o' => rw [h'] at h; simp at h; rw [h]
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h]; simp

theorem newOp_spec {l : List Label} {k : Fin 3} {e : Ev} {o : Op} (h : newOp l k e = some o) :
    o.g = l.length ∧ o.r = k ∧ e.clientReq = some (o.cid, o.rid, o.inp) := by
  unfold newOp at h
  rcases hc : e.clientReq with _ | ⟨cid, rid, i⟩
  · rw [hc] at h; cases h
  · rw [hc] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl⟩

theorem newOp_of_clientReq {l : List Label} {k : Fin 3} {e : Ev} {cid rid : w32}
    {i : dsverify_lab.harness.RegInput w64} (h : e.clientReq = some (cid, rid, i)) :
    ∃ o, newOp l k e = some o ∧ o.cid = cid ∧ o.rid = rid ∧ o.inp = i ∧ o.g = l.length ∧ o.r = k := by
  unfold newOp; rw [h]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem newOp_none {l : List Label} {k : Fin 3} {e : Ev} (h : e.clientReq = none) :
    newOp l k e = none := by
  unfold newOp; rw [h]; rfl

/-! ## Replies -/

theorem outsAt_append (l l' : List Label) {n : Nat} (hn : n < l.length) :
    pure.outsAt (l ++ l') n = pure.outsAt l n := by
  unfold pure.outsAt
  rw [List.getElem?_append_left hn, List.take_append_of_le_length (Nat.le_of_lt hn)]

theorem extsAt_append (l l' : List Label) {n : Nat} (hn : n < l.length) :
    extsAt (l ++ l') n = extsAt l n := by
  unfold extsAt; rw [outsAt_append l l' hn]

theorem replyAt_append {l : List Label} (l' : List Label) {n : Nat} {id : proto.OpId}
    (h : replyAt l n id) : replyAt (l ++ l') n id := by
  obtain ⟨hn, x, hx, hk⟩ := h
  refine ⟨by rw [List.length_append]; omega, x, ?_, hk⟩
  rw [extsAt_append l l' hn]; exact hx

theorem repliedIn_prefix {l l' : List Label} {id : proto.OpId} (hp : l <+: l')
    (h : repliedIn l id) : repliedIn l' id := by
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨n, hn⟩ := h
  exact ⟨n, replyAt_append u hn⟩

theorem RepliesTo_append {l : List Label} (l' : List Label) {n : Nat} {o : Op}
    (h : RepliesTo l n o) : RepliesTo (l ++ l') n o := by
  obtain ⟨h1, h2, x, hx, hk⟩ := h
  have hn : n < l.length := by
    rcases hl : l[n]? with _ | y
    · rw [hl] at h2; cases h2
    · exact (List.getElem?_eq_some_iff.1 hl).1
  refine ⟨h1, ?_, x, ?_, hk⟩
  · rw [List.getElem?_append_left hn]; exact h2
  · rw [extsAt_append l l' hn]; exact hx

/-- The outputs of the last label of `l ++ [(k, e)]` are its step's. -/
theorem outsAt_last (l : List Label) (k : Fin 3) (e : Ev) :
    pure.outsAt (l ++ [(k, e)]) l.length =
      match stepR k (stOf k (projR l k)) e with
      | .ok (_, o) => o
      | .error _ => [] := by
  unfold pure.outsAt
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp only [List.getElem?_cons_zero]
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  rfl

/-! ## Operations per replica -/

theorem ops_filter_snoc (l : List Label) (k r : Fin 3) (e : Ev) :
    ((ops (l ++ [(k, e)])).filter (fun o => decide (o.r = r))).length =
      ((ops l).filter (fun o => decide (o.r = r))).length +
        (if r = k ∧ e.clientReq.isSome then 1 else 0) := by
  rw [ops_snoc, List.filter_append, List.length_append]
  congr 1
  rcases hc : e.clientReq with _ | x
  · rw [newOp_none hc]; simp
  · obtain ⟨o, ho, -, -, -, -, hr⟩ := newOp_of_clientReq (l := l) (k := k) hc
    rw [ho]
    simp only [Option.toList_some, Option.isSome_some, and_true]
    by_cases h : r = k
    · subst h; simp [hr]
    · have : ¬ (o.r = r) := by rw [hr]; exact fun e => h e.symm
      simp [this, h]

/-- The number of client requests replica `r` handled in `l` is the number of its operations. -/
theorem ops_filter_length (r : Fin 3) :
    ∀ (n : Nat) (l : List Label), l.length = n →
      ((ops l).filter (fun o => decide (o.r = r))).length =
        ((projR l r).filter (fun e => e.clientReq.isSome)).length
  | 0, l, h => by
    rw [List.length_eq_zero_iff] at h; subst h; rfl
  | n + 1, l, h => by
    have hne : l ≠ [] := by intro e; subst e; cases h
    obtain ⟨l0, x, rfl⟩ : ∃ l0 x, l = l0 ++ [x] := ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨k, e⟩ := x
    rw [ops_filter_snoc, proj_snoc, List.filter_append, List.length_append,
      ops_filter_length r n _ (by simp at h; omega)]
    congr 1
    by_cases hr : r = k
    · subst hr
      simp only [↓reduceIte, true_and]
      cases hc : e.clientReq.isSome <;> simp [List.filter, hc]
    · simp [hr]

end Perennial.gryff.p2
