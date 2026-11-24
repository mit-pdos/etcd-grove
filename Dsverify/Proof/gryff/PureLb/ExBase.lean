/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/ExBase.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b (RMW side): helpers for **the executed accounting** (`PureLb/ExInv.lean`): ghost phases
and their counts, message counts, executed sequences under extension, RMW-reply labels (`RepX`),
and the specs of `stepExec`/`stepExecuteOverwrite`.
-/
module

public import Dsverify.Proof.gryff.PureLb.ExFlow
public import Dsverify.Proof.gryff.PureT.Total

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## Ghost phases -/

/-- A replica's phase in the execution of an instance: not executed (with a command) or not yet
tracked; its `ExecuteOverwrite` pending; its `Executed` in flight to the leader; counted at the
leader. -/
inductive Ph | none | eo | ex | done
  deriving DecidableEq

/-- The ghost: replica `r`'s phase for instance `(rid32 L, i)` is `G r L i`. -/
abbrev GX := Fin 3 → Fin 3 → w32 → Ph

def phCnt (f : Fin 3 → Ph) (p : Ph) : Nat :=
  (if f 0 = p then 1 else 0) + (if f 1 = p then 1 else 0) + (if f 2 = p then 1 else 0)

def upd3 (f : Fin 3 → Ph) (r : Fin 3) (p : Ph) : Fin 3 → Ph := fun r' => if r' = r then p else f r'

def gupd (G : GX) (r L : Fin 3) (i : w32) (p : Ph) : GX := fun r' L' i' =>
  if L' = L ∧ i' = i then upd3 (fun r => G r L i) r p r' else G r' L' i'

theorem fin3_cases_lb (r : Fin 3) : r = 0 ∨ r = 1 ∨ r = 2 := by
  revert r; decide

theorem cnt_le3 (f : Fin 3 → Ph) (p : Ph) : phCnt f p ≤ 3 := by
  unfold phCnt; split <;> split <;> split <;> omega

theorem cnt_le2 {f : Fin 3 → Ph} {p : Ph} {r : Fin 3} (h : f r ≠ p) : phCnt f p ≤ 2 := by
  unfold phCnt
  rcases fin3_cases_lb r with rfl | rfl | rfl <;> simp only [h, if_false] <;> split <;> split <;> omega

theorem cnt_pos {f : Fin 3 → Ph} {p : Ph} (h : 0 < phCnt f p) : ∃ r, f r = p := by
  unfold phCnt at h
  by_cases h0 : f 0 = p
  · exact ⟨0, h0⟩
  by_cases h1 : f 1 = p
  · exact ⟨1, h1⟩
  by_cases h2 : f 2 = p
  · exact ⟨2, h2⟩
  simp [h0, h1, h2] at h

theorem cnt_two {f : Fin 3 → Ph} {p : Ph} (h : 2 ≤ phCnt f p) :
    ∃ r1 r2, r1 ≠ r2 ∧ f r1 = p ∧ f r2 = p := by
  unfold phCnt at h
  by_cases h0 : f 0 = p <;> by_cases h1 : f 1 = p <;> by_cases h2 : f 2 = p <;>
    simp only [h0, h1, h2, if_true, if_false] at h
  all_goals first
    | omega
    | exact ⟨0, 1, by decide, h0, h1⟩
    | exact ⟨0, 2, by decide, h0, h2⟩
    | exact ⟨1, 2, by decide, h1, h2⟩

theorem cnt_upd3 (f : Fin 3 → Ph) (r : Fin 3) (p q : Ph) :
    phCnt (upd3 f r p) q + (if f r = q then 1 else 0) = phCnt f q + (if p = q then 1 else 0) := by
  unfold phCnt upd3
  rcases fin3_cases_lb r with rfl | rfl | rfl <;> simp only [if_true, if_false,
    (by decide : (1 : Fin 3) ≠ 0), (by decide : (2 : Fin 3) ≠ 0), (by decide : (0 : Fin 3) ≠ 1),
    (by decide : (2 : Fin 3) ≠ 1), (by decide : (0 : Fin 3) ≠ 2), (by decide : (1 : Fin 3) ≠ 2)] <;>
    split <;> split <;> split <;> split <;> omega

theorem gupd_same (G : GX) (r L : Fin 3) (i : w32) (p : Ph) :
    (fun r' => gupd G r L i p r' L i) = upd3 (fun r => G r L i) r p := by
  funext r'; simp [gupd]

theorem gupd_other (G : GX) (r L : Fin 3) (i : w32) (p : Ph) {L' : Fin 3} {i' : w32}
    (h : ¬(L' = L ∧ i' = i)) : (fun r' => gupd G r L i p r' L' i') = fun r' => G r' L' i' := by
  funext r'; simp only [gupd, if_neg h]

theorem gupd_at (G : GX) (r L : Fin 3) (i : w32) (p : Ph) : gupd G r L i p r L i = p := by
  simp [gupd, upd3]

theorem gupd_ne (G : GX) (r L : Fin 3) (i : w32) (p : Ph) {r' L' : Fin 3} {i' : w32}
    (h : ¬(r' = r ∧ L' = L ∧ i' = i)) : gupd G r L i p r' L' i' = G r' L' i' := by
  unfold gupd upd3
  split
  · rename_i h1; obtain ⟨rfl, rfl⟩ := h1
    rw [if_neg (fun h2 => h ⟨h2, rfl, rfl⟩)]
  · rfl

/-! ## Messages -/

/-- An `ExecuteOverwrite` of instance `(q, i)`. -/
def isEOx (q i : w32) : Msg → Bool
  | .executeOverwrite m => decide (m.leader = q ∧ m.slot = i)
  | _ => false

/-- The `Executed` notice of instance `(q, i)`. -/
def exM (q i : w32) : Msg := .executed { replica := q, inst := i }

theorem countP_erase_of {f : Msg → Bool} {m : Msg} (hm : f m = false) (L : List Msg) :
    (L.erase m).countP f = L.countP f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases ha : a = m
    · subst ha; rw [List.erase_cons_head]; simp [hm]
    · rw [List.erase_cons_tail (by simpa using ha)]
      simp only [List.countP_cons, ih]

theorem countP_erase_mem {f : Msg → Bool} {m : Msg} (hm : f m = true) {L : List Msg} (hL : m ∈ L) :
    (L.erase m).countP f + 1 = L.countP f := by
  induction L with
  | nil => cases hL
  | cons a L ih =>
    by_cases ha : a = m
    · subst ha; rw [List.erase_cons_head]; simp [hm]
    · rw [List.erase_cons_tail (by simpa using ha)]
      have hL' : m ∈ L := by
        rcases List.mem_cons.1 hL with h | h
        · exact absurd h.symm ha
        · exact h
      simp only [List.countP_cons]
      have := ih hL'; omega

theorem countP_pos_mem {f : Msg → Bool} {m : Msg} (hm : f m = true) {L : List Msg} (hL : m ∈ L) :
    0 < L.countP f := List.countP_pos_iff.2 ⟨m, hL, hm⟩

theorem sentR_nil (j : Fin 3) : sentR j [] = [] := rfl

theorem sentR_noX {o : List Out} (h : NoX o) (j : Fin 3) : ∀ m ∈ sentR j o, isXMsg m = false := by
  intro m hm
  unfold sentR at hm
  obtain ⟨x, hx, hx'⟩ := List.mem_filterMap.1 hm
  have := h x hx
  cases x with
  | send d m' =>
    simp only at hx'
    split at hx'
    · cases hx'; exact this
    · cases hx'
  | ext _ => cases hx'

theorem countP_sentR_noX {o : List Out} (h : NoX o) (j : Fin 3) (q i : w32) :
    (sentR j o).countP (isEOx q i) = 0 := by
  rw [List.countP_eq_zero]
  intro m hm
  have := sentR_noX h j m hm
  cases m <;> simp_all [isXMsg, isEOx]

theorem count_sentR_noX {o : List Out} (h : NoX o) (j : Fin 3) (q i : w32) :
    (sentR j o).count (exM q i) = 0 := by
  rw [List.count_eq_zero]
  intro hm
  have := sentR_noX h j _ hm
  simp [exM, isXMsg] at this

theorem extsOnly_noX {o : List Out} (h : ∀ x ∈ o, ∃ y, x = .ext y) : NoX o := by
  intro x hx; obtain ⟨y, rfl⟩ := h x hx; rfl

/-! ## Executed sequences under extension -/

theorem mem_execSeq' (r : Fin 3) {es : List Ev} {x : w32 × w32} {vt : ValTag} :
    (x, vt) ∈ execSeq r es ↔ ∃ j, es[j]? = some (.exec x.1 x.2) ∧ execRes (outsOf r es j) = some vt := by
  unfold execSeq
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, -, hj⟩
    split at hj
    · rename_i q i he
      obtain ⟨vt', hv, he'⟩ := Option.map_eq_some_iff.1 hj
      cases he'; exact ⟨j, he, hv⟩
    · cases hj
  · rintro ⟨j, hj, hv⟩
    refine ⟨j, List.mem_range.2 (List.getElem?_eq_some_iff.1 hj).1, ?_⟩
    rw [hj]; simp [hv]

theorem outsOf_append (r : Fin 3) (es es2 : List Ev) {j : Nat} (hj : j < es.length) :
    outsOf r (es ++ es2) j = outsOf r es j := by
  unfold outsOf resOf
  rw [List.getElem?_append_left hj, List.take_append_of_le_length (by omega)]

theorem execSeq_append_mem (r : Fin 3) {es : List Ev} (es2 : List Ev) {x : w32 × w32} {vt : ValTag}
    (h : (x, vt) ∈ execSeq r es) : (x, vt) ∈ execSeq r (es ++ es2) := by
  obtain ⟨j, hj, hv⟩ := (mem_execSeq' r).1 h
  have hjl : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
  exact (mem_execSeq' r).2 ⟨j, by rw [List.getElem?_append_left hjl, hj], by
    rw [outsOf_append r es es2 hjl, hv]⟩

theorem outsOf_last (r : Fin 3) (es : List Ev) (e : Ev) {s' : RState} {o : List Out}
    (h : stepR r (stOf r es) e = .ok (s', o)) : outsOf r (es ++ [e]) es.length = o := by
  unfold outsOf resOf
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp only [List.getElem?_cons_zero]
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length, h]

/-- The executed sequence after one more event. -/
theorem execSeq_snoc_lb (r : Fin 3) (es : List Ev) (e : Ev) {s' : RState} {o : List Out}
    (h : stepR r (stOf r es) e = .ok (s', o)) :
    execSeq r (es ++ [e]) = execSeq r es ++ (match e with
      | .exec q i => ((execRes o).map fun vt => ((q, i), vt)).toList
      | _ => []) := by
  unfold execSeq
  rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
  congr 1
  · apply filterMap_congr'
    intro j hj
    have hj' : j < es.length := List.mem_range.1 hj
    rw [List.getElem?_append_left hj', outsOf_append r es [e] hj']
  · rw [List.filterMap_cons, List.filterMap_nil]
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    simp only [List.getElem?_cons_zero]
    rw [outsOf_last r es e h]
    cases e <;> simp
    cases execRes o <;> rfl

/-! ## RMW-reply labels -/

/-- Event `e` is handled by `handleExecuted` on instance `x`. -/
def HX (e : Ev) (x : w32 × w32) : Prop :=
  (∃ m : ExecutedM, e = .msg (.executed m) ∧ (m.replica, m.inst) = x) ∨
  (∃ m : ExecuteOverwriteM, e = .msg (.executeOverwrite m) ∧ (m.leader, m.slot) = x)

/-- Label `n` is a reply of the leader `L` of instance `x` (`x.1 = rid32 L`) handling `x`'s
execution. -/
def RepX (l : List Label) (n : Nat) (x : w32 × w32) : Prop :=
  ∃ L e, l[n]? = some (L, e) ∧ x.1 = rid32 L ∧ HX e x ∧
    ∃ cid rid f, Ext.rmwReply cid rid f ∈ extsAt l n

/-- Instance `x` was replied to. -/
def Rep (l : List Label) (x : w32 × w32) : Prop := ∃ n, RepX l n x

theorem outsAt_appL {l l' : List Label} {n : Nat} (hn : n < l.length) :
    outsAt (l ++ l') n = outsAt l n := by
  unfold outsAt
  rw [List.getElem?_append_left hn, List.take_append_of_le_length (by omega)]

theorem repX_appL {l l' : List Label} {n : Nat} {x : w32 × w32} (hn : n < l.length) :
    RepX (l ++ l') n x ↔ RepX l n x := by
  unfold RepX extsAt
  rw [List.getElem?_append_left hn, outsAt_appL hn]

theorem repX_lt {l : List Label} {n : Nat} {x : w32 × w32} (h : RepX l n x) : n < l.length := by
  obtain ⟨L, e, hn, -⟩ := h
  exact (List.getElem?_eq_some_iff.1 hn).1

theorem rep_snoc {l : List Label} {y : Label} {x : w32 × w32} :
    Rep (l ++ [y]) x ↔ Rep l x ∨ RepX (l ++ [y]) l.length x := by
  constructor
  · rintro ⟨n, hn⟩
    have hlt := repX_lt hn
    rw [List.length_append, List.length_singleton] at hlt
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | rfl
    · exact Or.inl ⟨n, (repX_appL h).1 hn⟩
    · exact Or.inr hn
  · rintro (⟨n, hn⟩ | h)
    · exact ⟨n, (repX_appL (repX_lt hn)).2 hn⟩
    · exact ⟨_, h⟩

theorem repX_last {l : List Label} {a : Fin 3} {e : Ev} {s : RState} {s' : RState} {o : List Out}
    (hs : stOf a (projR l a) = s) (h : stepR a s e = .ok (s', o)) {x : w32 × w32} :
    RepX (l ++ [(a, e)]) l.length x ↔
      x.1 = rid32 a ∧ HX e x ∧ ∃ cid rid f, Out.ext (.rmwReply cid rid f) ∈ o := by
  unfold RepX
  have h1 : (l ++ [(a, e)])[l.length]? = some (a, e) := by simp
  have h2 : outsAt (l ++ [(a, e)]) l.length = o := by
    unfold outsAt
    rw [h1]; simp only
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length, hs, h]
  rw [h1]
  constructor
  · rintro ⟨L, e', he, h3, h4, cid, rid, f, h5⟩
    cases he
    refine ⟨h3, h4, cid, rid, f, ?_⟩
    unfold extsAt at h5; rw [h2] at h5
    obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 h5
    cases y with
    | ext y => cases hy'; exact hy
    | send _ _ => cases hy'
  · rintro ⟨h3, h4, cid, rid, f, h5⟩
    refine ⟨a, e, rfl, h3, h4, cid, rid, f, ?_⟩
    unfold extsAt; rw [h2]
    exact List.mem_filterMap.2 ⟨_, h5, rfl⟩

/-! ## The executor's and the run loop's steps -/

/-- `stepExec` outputs nothing or one `ExecuteOverwrite` to itself, naming its copy's
leader and slot. -/
theorem stepExec_out {s s' : RState} {q i : w32} {o : List Out} (h : stepExec s q i = .ok (s', o)) :
    ∃ c, s.inst q i = some c ∧ s'.inst q i = some { c with status := St.EXECUTED } ∧
      s'.tag = s.tag ∧ (∀ q' i', ¬(q' = q ∧ i' = i) → s'.inst q' i' = s.inst q' i') ∧
      (o = [] ∨ ∃ d v t, dstOf s.id = some d ∧
        o = [.send d (.executeOverwrite { v, t, leader := c.leader, slot := c.slot })]) := by
  unfold stepExec at h
  peel h
  all_goals (cases h)
  · refine ⟨_, ‹_›, by simp [RState.setInst], rfl, fun q' i' hn => by
      simp [RState.setInst, hn], Or.inl rfl⟩
  all_goals (
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 ‹sendTo _ _ = some _›
    exact ⟨_, ‹_›, by simp [RState.setInst], rfl, fun q' i' hn => by
      simp [RState.setInst, hn], Or.inr ⟨d, _, _, hd, rfl⟩⟩)

/-- `stepExecuteOverwrite`: to self, `handleExecuted` after the overwrite; else an `Executed` to
the leader. -/
theorem stepEO_spec {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) :
    (m.leader = s.id ∧ handleExecuted (s.overwrite m.v m.t) { replica := m.leader, inst := m.slot } =
        .ok (s', o)) ∨
      (m.leader ≠ s.id ∧ s' = s.overwrite m.v m.t ∧ ∃ d, dstOf m.leader = some d ∧
        o = [.send d (exM m.leader m.slot)]) := by
  unfold stepExecuteOverwrite at h
  peel h
  · rename_i hl
    left; exact ⟨by rw [hl]; unfold RState.overwrite; split <;> rfl, h⟩
  all_goals (cases h)
  rename_i hne _ _ hsp
  unfold sendPeer at hsp
  rw [if_neg (by simpa using hne)] at hsp
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hsp
  exact Or.inr ⟨by simpa using hne, rfl, d, hd, rfl⟩

/-- `handleExecuted`'s outputs are external. -/
theorem handleExecuted_ext {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : ∀ x ∈ o, ∃ y, x = .ext y := by
  rcases handleExecuted_spec h with ⟨-, rfl⟩ | ⟨c, lb, b, -, -, -, ⟨rfl, -⟩ | ⟨-, -, -, p, -, rfl⟩⟩
  · simp
  · simp
  · intro x hx; rw [List.mem_singleton.1 hx]; exact ⟨_, rfl⟩

end Perennial.gryff.pure
