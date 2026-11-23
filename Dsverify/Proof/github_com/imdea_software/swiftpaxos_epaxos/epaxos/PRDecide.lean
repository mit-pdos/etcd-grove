/-
Pure facts for `handlePrepareReply`'s decision loops: `prepDecide` by indices (the stages the
code's `subCase`/`chosen` go through), find-first loops.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.PRModel

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

theorem find?_findIdx? {α : Type} [Inhabited α] (l : List α) (p : α → Bool) :
    l.find? p = (l.findIdx? p).map (fun j => l.getD j default) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findIdx?_cons, List.find?_cons]
    cases h : p a
    · simp only [Bool.false_eq_true, ite_false, ih, Option.map_map]
      rfl
    · rfl

/-- First index with `p` among the first `k` (or none). -/
theorem findIdx?_take_succ {α : Type} [Inhabited α] (l : List α) (p : α → Bool) (k : Nat)
    (hk : k < l.length) :
    (l.take (k + 1)).findIdx? p =
      ((l.take k).findIdx? p).or (if p (l.getD k default) then some k else none) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.findIdx?_append,
    List.findIdx?_singleton]
  have hl : (l.take k).length = k := by simp; omega
  rw [hl]
  have : l.getD k default = l[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rw [this]
  cases p l[k] <;> simp

theorem findIdx?_first {α : Type} [Inhabited α] (l : List α) (p : α → Bool) (k : Nat)
    (hk : k < l.length) (hp : p (l.getD k default) = true)
    (hn : ∀ j < k, p (l.getD j default) = false) : l.findIdx? p = some k := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hk, ?_, fun j hj => ?_⟩
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using hp
  · have := hn j hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.lt_trans hj hk)] at this
    simp [this]

theorem findIdx?_none {α : Type} [Inhabited α] (l : List α) (p : α → Bool)
    (hn : ∀ j < l.length, p (l.getD j default) = false) : l.findIdx? p = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := hn j hj
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using this

/-- `findIdx?` of a prefix extended by one element. -/
theorem take_foldl_succ {α β : Type} [Inhabited α] (l : List α) (f : β → α → β) (b : β) (k : Nat)
    (hk : k < l.length) :
    (l.take (k + 1)).foldl f b = f ((l.take k).foldl f b) (l.getD k default) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem take_any_succ {α : Type} [Inhabited α] (l : List α) (p : α → Bool) (k : Nat)
    (hk : k < l.length) :
    (l.take (k + 1)).any p = ((l.take k).any p || p (l.getD k default)) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.any_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem take_filter_len_succ {α : Type} [Inhabited α] (l : List α) (p : α → Bool) (k : Nat)
    (hk : k < l.length) :
    ((l.take (k + 1)).filter p).length =
      ((l.take k).filter p).length + (if p (l.getD k default) then 1 else 0) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.filter_append,
    List.length_append]
  have : l.getD k default = l[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rw [this]
  cases h : p l[k] <;> simp [List.filter_cons, h]

/-! ## The decision by stages (indices) -/

def comP (e : PReply) : Bool := stGe e.m.status stCOMMITTED
def accP (mx : w32) (e : PReply) : Bool := e.m.vballot == mx && e.m.status == stACCEPTED
def lrP (e : PReply) : Bool := e.m.acceptorId == e.m.replica
def mxF (mx : w32) (e : PReply) : w32 := if mx.slt e.m.vballot then e.m.vballot else mx

/-- Sub-case 3's count predicate (`subCase3Ok`'s filter). -/
def q3 (mx : w32) (e o : PReply) : Bool :=
  isPreAcceptedAt mx o && o.m.acceptorId != o.m.replica && o.m.seq == e.m.seq &&
    depsEqual o.m.deps e.m.deps

theorem subCase3Ok_eq (reps : List PReply) (mx : w32) (e : PReply) :
    subCase3Ok reps mx e = (isPreAcceptedAt mx e && e.m.acceptorId != e.m.replica &&
      decide (nR / 2 ≤ (reps.filter (q3 mx e)).length)) := rfl

def stg (c : Nat) (o : Option Nat) : Nat × Option Nat :=
  match o with
  | some j => (c, some j)
  | none => (0, none)

def dec1 (reps : List PReply) : Nat × Option Nat := stg 1 (reps.findIdx? comP)
def dec2 (reps : List PReply) (mx : w32) : Nat × Option Nat :=
  if (dec1 reps).1 = 0 then stg 2 (reps.findIdx? (accP mx)) else dec1 reps
def dec3 (reps : List PReply) (mx : w32) (lr : Bool) (replica : w32) : Nat × Option Nat :=
  if (dec2 reps mx).1 = 0 ∧ isInitialBallot mx replica = true ∧ lr = false then
    stg 3 (reps.findIdx? (subCase3Ok reps mx)) else dec2 reps mx
def dec5 (reps : List PReply) (mx : w32) (lr : Bool) (replica : w32) : Nat × Option Nat :=
  if (dec3 reps mx lr replica).1 = 0 then stg 5 (reps.findIdx? (isPreAcceptedAt mx))
  else dec3 reps mx lr replica
def dec6 (reps : List PReply) (mx : w32) (lr : Bool) (replica : w32) : Nat × Option Nat :=
  if (dec5 reps mx lr replica).1 = 0 then (6, none) else dec5 reps mx lr replica

theorem dec6_eq (reps : List PReply) (mx : w32) (lr : Bool) (replica : w32) :
    ((dec6 reps mx lr replica).1, (dec6 reps mx lr replica).2.map (fun j => reps.getD j default))
      = prepDecide reps mx lr replica := by
  unfold dec6 dec5 dec3 dec2 dec1 prepDecide
  simp only [show (fun e : PReply => stGe e.m.status stCOMMITTED) = comP from rfl,
    show (fun e : PReply => e.m.vballot == mx && e.m.status == stACCEPTED) = accP mx from rfl,
    find?_findIdx? reps comP, find?_findIdx? reps (accP mx),
    find?_findIdx? reps (subCase3Ok reps mx), find?_findIdx? reps (isPreAcceptedAt mx)]
  generalize reps.findIdx? comP = A
  generalize reps.findIdx? (accP mx) = B
  generalize reps.findIdx? (subCase3Ok reps mx) = C
  generalize reps.findIdx? (isPreAcceptedAt mx) = D
  rcases A with _ | a <;> rcases B with _ | b <;> rcases C with _ | c <;> rcases D with _ | d <;>
    cases hi : isInitialBallot mx replica <;> cases lr <;> simp [stg, hi]

theorem dec6_ne4 (reps : List PReply) (mx : w32) (lr : Bool) (replica : w32) :
    (dec6 reps mx lr replica).1 ≠ 4 := by
  have h := congrArg Prod.fst (dec6_eq reps mx lr replica)
  simp only at h
  rw [h]
  unfold prepDecide
  repeat' split
  all_goals simp

theorem stg_fst (c : Nat) (o : Option Nat) : (stg c o).1 = 0 ∨ (stg c o).1 = c := by
  unfold stg; split <;> simp

theorem stg_zero (c : Nat) (o : Option Nat) (hc : c ≠ 0) (h : (stg c o).1 = 0) :
    stg c o = (0, none) := by
  unfold stg at *; split <;> simp_all

theorem dec2_zero (reps : List PReply) (mx : w32) (h : (dec2 reps mx).1 = 0) :
    dec2 reps mx = (0, none) := by
  unfold dec2 at h ⊢
  by_cases hc : (dec1 reps).1 = 0
  · rw [if_pos hc] at h ⊢; exact stg_zero 2 _ (by decide) h
  · rw [if_neg hc] at h ⊢; exact absurd h hc

theorem dec3_zero (reps : List PReply) (mx : w32) (lr : Bool) (r : w32)
    (h : (dec3 reps mx lr r).1 = 0) : dec3 reps mx lr r = (0, none) := by
  unfold dec3 at h ⊢
  by_cases hc : (dec2 reps mx).1 = 0 ∧ isInitialBallot mx r = true ∧ lr = false
  · rw [if_pos hc] at h ⊢; exact stg_zero 3 _ (by decide) h
  · rw [if_neg hc] at h ⊢; exact dec2_zero reps mx h

theorem dec5_zero (reps : List PReply) (mx : w32) (lr : Bool) (r : w32)
    (h : (dec5 reps mx lr r).1 = 0) : dec5 reps mx lr r = (0, none) := by
  unfold dec5 at h ⊢
  by_cases hc : (dec3 reps mx lr r).1 = 0
  · rw [if_pos hc] at h ⊢; exact stg_zero 5 _ (by decide) h
  · rw [if_neg hc] at h ⊢; exact absurd h hc

theorem stg_idx (c : Nat) (o : Option Nat) (j : Nat) (h : (stg c o).2 = some j) : o = some j := by
  unfold stg at h; split at h <;> simp_all

theorem findIdx?_lt {α : Type} (l : List α) (p : α → Bool) (j : Nat) (h : l.findIdx? p = some j) :
    j < l.length := (List.findIdx?_eq_some_iff_getElem.mp h).1

theorem dec1_idx (reps : List PReply) (j : Nat) (h : (dec1 reps).2 = some j) :
    j < reps.length := findIdx?_lt _ _ _ (stg_idx _ _ _ h)

theorem dec2_idx (reps : List PReply) (mx : w32) (j : Nat) (h : (dec2 reps mx).2 = some j) :
    j < reps.length := by
  unfold dec2 at h
  by_cases hc : (dec1 reps).1 = 0
  · rw [if_pos hc] at h; exact findIdx?_lt _ _ _ (stg_idx _ _ _ h)
  · rw [if_neg hc] at h; exact dec1_idx _ _ h

theorem dec3_idx (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) (j : Nat)
    (h : (dec3 reps mx lr r).2 = some j) : j < reps.length := by
  unfold dec3 at h
  by_cases hc : (dec2 reps mx).1 = 0 ∧ isInitialBallot mx r = true ∧ lr = false
  · rw [if_pos hc] at h; exact findIdx?_lt _ _ _ (stg_idx _ _ _ h)
  · rw [if_neg hc] at h; exact dec2_idx _ _ _ h

theorem dec5_idx (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) (j : Nat)
    (h : (dec5 reps mx lr r).2 = some j) : j < reps.length := by
  unfold dec5 at h
  by_cases hc : (dec3 reps mx lr r).1 = 0
  · rw [if_pos hc] at h; exact findIdx?_lt _ _ _ (stg_idx _ _ _ h)
  · rw [if_neg hc] at h; exact dec3_idx _ _ _ _ _ h

theorem stg_none (c : Nat) (o : Option Nat) (h : (stg c o).2 = none) : (stg c o).1 = 0 := by
  unfold stg at *; split <;> simp_all

theorem dec5_none (reps : List PReply) (mx : w32) (lr : Bool) (r : w32)
    (h : (dec5 reps mx lr r).2 = none) : (dec5 reps mx lr r).1 = 0 := by
  unfold dec5 at h ⊢
  by_cases hc : (dec3 reps mx lr r).1 = 0
  · rw [if_pos hc] at h ⊢; exact stg_none _ _ h
  · rw [if_neg hc] at h ⊢
    unfold dec3 at h hc ⊢
    by_cases hc3 : (dec2 reps mx).1 = 0 ∧ isInitialBallot mx r = true ∧ lr = false
    · rw [if_pos hc3] at h hc ⊢; exact stg_none _ _ h
    · rw [if_neg hc3] at h hc ⊢
      unfold dec2 at h hc ⊢
      by_cases hc2 : (dec1 reps).1 = 0
      · rw [if_pos hc2] at h hc ⊢; exact stg_none _ _ h
      · rw [if_neg hc2] at h hc ⊢; unfold dec1 at h ⊢; exact stg_none _ _ h

theorem dec6_snd (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) :
    (dec6 reps mx lr r).2 = (dec5 reps mx lr r).2 := by
  unfold dec6
  split
  · rename_i h; rw [dec5_zero _ _ _ _ h]
  · rfl

theorem dec2_lt (reps : List PReply) (mx : w32) : (dec2 reps mx).1 < 3 := by
  unfold dec2 dec1
  split
  · rcases stg_fst 2 ((reps.findIdx? (accP mx))) with h | h <;> omega
  · rcases stg_fst 1 ((reps.findIdx? comP)) with h | h <;> omega

theorem dec3_lt (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) :
    (dec3 reps mx lr r).1 < 4 := by
  unfold dec3
  split
  · rcases stg_fst 3 ((reps.findIdx? (subCase3Ok reps mx))) with h | h <;> omega
  · have := dec2_lt reps mx; omega

theorem dec5_lt (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) :
    (dec5 reps mx lr r).1 < 6 := by
  unfold dec5
  split
  · rcases stg_fst 5 ((reps.findIdx? (isPreAcceptedAt mx))) with h | h <;> omega
  · have := dec3_lt reps mx lr r; omega

theorem dec6_five (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) (j : Nat)
    (h5 : (dec6 reps mx lr r).1 ≠ 1 ∧ (dec6 reps mx lr r).1 ≠ 2 ∧ (dec6 reps mx lr r).1 ≠ 3)
    (hj : (dec6 reps mx lr r).2 = some j) :
    isPreAcceptedAt mx (reps.getD j default) = true := by
  unfold dec6 at h5 hj
  by_cases h0 : (dec5 reps mx lr r).1 = 0
  · rw [if_pos h0] at hj; simp at hj
  rw [if_neg h0] at h5 hj
  unfold dec5 at h5 hj h0
  by_cases h3 : (dec3 reps mx lr r).1 = 0
  · rw [if_pos h3] at h5 hj
    have := stg_idx _ _ _ hj
    have := (List.findIdx?_eq_some_iff_getElem.mp this)
    obtain ⟨hl, hp, -⟩ := this
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] using hp
  · rw [if_neg h3] at h5 h0
    exfalso
    have := dec3_lt reps mx lr r
    omega

/-- The reply `prepDecide` chooses has a status past NONE. -/
theorem prepDecide_status (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) (e : PReply)
    (h : (prepDecide reps mx lr r).2 = some e) : e.m.status ≠ stNONE := by
  intro hs
  unfold prepDecide at h
  split at h
  · rename_i hf; cases h; have := List.find?_some hf; rw [hs] at this; revert this; decide
  split at h
  · rename_i hf; cases h; have := List.find?_some hf; rw [hs] at this
    simp [stNONE, stACCEPTED] at this
  split at h
  · rename_i hf; cases h
    split at hf
    · have := List.find?_some hf
      simp only [subCase3Ok, isPreAcceptedAt, hs, Bool.and_eq_true] at this
      have h2 := this.1.1.2
      simp [stNONE, stPREACCEPTED, stPREACCEPTED_EQ] at h2
    · simp at hf
  split at h
  · rename_i hf; cases h; have := List.find?_some hf
    simp only [isPreAcceptedAt, hs, Bool.and_eq_true] at this
    have h2 := this.2
    simp [stNONE, stPREACCEPTED, stPREACCEPTED_EQ] at h2
  · simp at h

theorem dec6_status (reps : List PReply) (mx : w32) (lr : Bool) (r : w32) (j : Nat)
    (h : (dec6 reps mx lr r).2 = some j) : (reps.getD j default).m.status ≠ stNONE := by
  have e := congrArg Prod.snd (dec6_eq reps mx lr r)
  simp only [h, Option.map_some] at e
  exact prepDecide_status reps mx lr r _ e.symm

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
