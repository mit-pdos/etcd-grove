/-
**Lemmas over the WAL's history and its reader** (WAL W4b, 2026-11-12; `/shared/tmp/wal-spec/w4b/plan.md`
§2 A, approved by etcd-grove-81). Proved; no trusted text. For the tester's proof (W4c), rung 2's crash
clause (C3) and the server's restart (S2/C6).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-! ## A1. The image algebra -/

section img
variable {E : Type}

theorem getElem?_some_lt {α : Type} {l : List α} {j : Nat} {x : α} (h : l[j]? = some x) :
    j < l.length := by
  rcases Nat.lt_or_ge j l.length with hl | hl
  · exact hl
  · rw [List.getElem?_eq_none hl] at h; cases h

/-- The whole history is an image of itself at any mark up to its length. -/
theorem walImg_refl {H : List (WalOpG E)} {n : Nat} (h : n ≤ H.length) : walImg H n H :=
  ⟨H.length, h, Nat.le_refl _, Or.inl (List.take_length).symm⟩

/-- A higher mark allows fewer images. -/
theorem walImg_mono {H I : List (WalOpG E)} {n n' : Nat} (hn : n ≤ n') (hI : walImg H n' I) :
    walImg H n I := by
  obtain ⟨j, h1, h2, h3⟩ := hI
  exact ⟨j, Nat.le_trans hn h1, h2, h3⟩

/-- An image is no longer than the history. -/
theorem walImg_length_le {H I : List (WalOpG E)} {n : Nat} (hI : walImg H n I) :
    I.length ≤ H.length := by
  obtain ⟨j, -, h2, h3 | ⟨h, es, k, hj, -, h3⟩⟩ := hI
  · subst h3; simp; omega
  · have := getElem?_some_lt hj
    subst h3; simp; omega

/-- An image of `H` is an image of `H` with one more operation (the operation not yet written). -/
theorem walImg_snoc {H I : List (WalOpG E)} {n : Nat} (o : WalOpG E) (hI : walImg H n I) :
    walImg (H ++ [o]) n I := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, hk, h3⟩⟩ := hI
  · refine ⟨j, h1, by simp; omega, Or.inl ?_⟩
    rw [h3, List.take_append_of_le_length h2]
  · have hjl := getElem?_some_lt hj
    refine ⟨j, h1, by simp; omega, Or.inr ⟨h, es, k, ?_, hk, ?_⟩⟩
    · rw [List.getElem?_append_left hjl]; exact hj
    · rw [h3, List.take_append_of_le_length h2]

/-- **The graceful instance**: with every operation synced, the only image is the history. -/
theorem walImg_full {H I : List (WalOpG E)} : walImg H H.length I ↔ I = H := by
  constructor
  · rintro ⟨j, h1, h2, h3 | ⟨h, es, k, hj, -, -⟩⟩
    · have : j = H.length := by omega
      subst this; simpa using h3
    · have := getElem?_some_lt hj; omega
  · rintro rfl; exact walImg_refl (Nat.le_refl _)

/-- An image keeps the synced prefix. -/
theorem walImg_prefix {H I : List (WalOpG E)} {n : Nat} (hI : walImg H n I) :
    n ≤ I.length ∧ I.take n = H.take n := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, -, h3⟩⟩ := hI
  · subst h3
    refine ⟨by simp; omega, ?_⟩
    rw [List.take_take, Nat.min_eq_left h1]
  · subst h3
    have hl : (H.take j).length = j := by simp; omega
    refine ⟨by simp; omega, ?_⟩
    rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left h1]

/-- **An image of an image is an image** (a kill, a restart, then a power loss: `walCrash`'s
docstring). -/
theorem walImg_trans {H I I' : List (WalOpG E)} {n : Nat} (hI : walImg H n I) (hI' : walImg I n I') :
    walImg H n I' := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, hk, h3⟩⟩ := hI
  · subst h3
    obtain ⟨j', h1', h2', h3' | ⟨h', es', k', hj', hk', h3'⟩⟩ := hI'
    · have hj'j : j' ≤ j := by simp at h2'; omega
      refine ⟨j', h1', by omega, Or.inl ?_⟩
      rw [h3', List.take_take, Nat.min_eq_left hj'j]
    · have hlt := getElem?_some_lt hj'
      have hj'j : j' < j := by simp at hlt; omega
      refine ⟨j', h1', by omega, Or.inr ⟨h', es', k', ?_, hk', ?_⟩⟩
      · rw [List.getElem?_take_of_lt hj'j] at hj'; exact hj'
      · rw [h3', List.take_take, Nat.min_eq_left (Nat.le_of_lt hj'j)]
  · subst h3
    have hjl := getElem?_some_lt hj
    have hl : (H.take j).length = j := by simp; omega
    obtain ⟨j', h1', h2', h3' | ⟨h', es', k', hj', hk', h3'⟩⟩ := hI'
    · simp only [List.length_append, List.length_cons, List.length_nil, hl] at h2'
      rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
      · refine ⟨j', h1', by omega, Or.inl ?_⟩
        rw [h3', List.take_append_of_le_length (by omega), List.take_take,
          Nat.min_eq_left (by omega)]
      · have : j' = j + 1 := by omega
        subst this
        refine ⟨j, h1, h2, Or.inr ⟨h, es, k, hj, hk, ?_⟩⟩
        rw [h3', List.take_of_length_le (by simp [hl])]
    · have hlt := getElem?_some_lt hj'
      simp only [List.length_append, List.length_cons, List.length_nil, hl] at hlt
      rcases Nat.lt_or_ge j' j with hj'j | hge
      · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hj'j] at hj'
        refine ⟨j', h1', by omega, Or.inr ⟨h', es', k', hj', hk', ?_⟩⟩
        rw [h3', List.take_append_of_le_length (by omega), List.take_take,
          Nat.min_eq_left (by omega)]
      · have : j' = j := by omega
        subst this
        rw [List.getElem?_append_right (by omega), hl, Nat.sub_self] at hj'
        simp only [List.getElem?_cons_zero, Option.some.injEq, WalOpG.save.injEq] at hj'
        obtain ⟨-, rfl⟩ := hj'
        refine ⟨j', h1, h2, Or.inr ⟨h, es, min k' k, hj, by omega, ?_⟩⟩
        rw [h3', List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
          List.take_take]

/-- **Images commute with a map of the entries** (`toM`, `toRaw`). -/
theorem walImg_map {E' : Type} (f : WalOpG E → WalOpG E') (g : E → E')
    (hsave : ∀ h es, f (.save h es) = .save h (es.map g))
    {H I : List (WalOpG E)} {n : Nat} (hI : walImg H n I) : walImg (H.map f) n (I.map f) := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, hk, h3⟩⟩ := hI
  · subst h3
    exact ⟨j, h1, by simpa using h2, Or.inl (List.map_take ..)⟩
  · subst h3
    refine ⟨j, h1, by simpa using h2, Or.inr ⟨h, es.map g, k, ?_, by simpa using hk, ?_⟩⟩
    · rw [List.getElem?_map, hj]; simp [hsave]
    · simp [List.map_append, List.map_take, hsave]

/-- Each operation of an image is the history's at its position, or a (torn) `Save`. -/
theorem walImg_getElem? {H I : List (WalOpG E)} {n : Nat} (hI : walImg H n I) {i : Nat}
    {o : WalOpG E} (ho : I[i]? = some o) : H[i]? = some o ∨ ∃ h es, o = .save h es := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, hk, h3⟩⟩ := hI
  · subst h3
    have hl := getElem?_some_lt ho
    simp only [List.length_take] at hl
    rw [List.getElem?_take_of_lt (by omega)] at ho
    exact Or.inl ho
  · subst h3
    have hl := getElem?_some_lt ho
    have hjl := getElem?_some_lt hj
    have hl' : (H.take j).length = j := by simp; omega
    simp only [List.length_append, hl', List.length_cons, List.length_nil] at hl
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hij] at ho
      exact Or.inl ho
    · have : i = j := by omega
      subst this
      rw [List.getElem?_append_right (by omega), hl', Nat.sub_self] at ho
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
      exact Or.inr ⟨_, _, ho.symm⟩
/-! ## B3. The images of a history with more operations -/

/-- **The images of `H ++ B`**: an image of `H`, or `H` followed by a
prefix `B.take (i+1)` of the new operations, or `H ++ B.take i` followed by the torn `i`-th (a `Save`
with its first `k` entries, its state record lost). -/
theorem walImg_append_cases {H B I : List (WalOpG E)} {n : Nat}
    (hI : walImg (H ++ B) n I) :
    walImg H n I ∨ ∃ i, i < B.length ∧
      (I = H ++ B.take (i + 1) ∨
       ∃ h es k, B[i]? = some (.save h es) ∧ k ≤ es.length ∧
         I = H ++ B.take i ++ [.save ⟨0, 0, 0⟩ (es.take k)]) := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, hk, h3⟩⟩ := hI
  · simp only [List.length_append] at h2
    rcases Nat.lt_or_ge H.length j with hlt | hge
    · right
      refine ⟨j - H.length - 1, by omega, Or.inl ?_⟩
      rw [h3, List.take_append, List.take_of_length_le (by omega)]
      congr 2; omega
    · left
      refine ⟨j, h1, hge, Or.inl ?_⟩
      rw [h3, List.take_append_of_le_length hge]
  · have hjl := getElem?_some_lt hj
    simp only [List.length_append] at hjl h2
    rcases Nat.lt_or_ge j H.length with hlt | hge
    · left
      refine ⟨j, h1, by omega, Or.inr ⟨h, es, k, ?_, hk, ?_⟩⟩
      · rw [List.getElem?_append_left hlt] at hj; exact hj
      · rw [h3, List.take_append_of_le_length (by omega)]
    · right
      refine ⟨j - H.length, by omega, Or.inr ⟨h, es, k, ?_, hk, ?_⟩⟩
      · rw [List.getElem?_append_right hge] at hj; exact hj
      · rw [h3, List.take_append, List.take_of_length_le (by omega)]

/-- **The images of one more operation** (C3's "entered, not entered, torn"). -/
theorem walImg_snoc_cases {H I : List (WalOpG E)} {n : Nat} {o : WalOpG E}
    (hI : walImg (H ++ [o]) n I) :
    walImg H n I ∨ I = H ++ [o] ∨
      ∃ h es k, o = .save h es ∧ k ≤ es.length ∧ I = H ++ [.save ⟨0, 0, 0⟩ (es.take k)] := by
  rcases walImg_append_cases hI with h | ⟨i, hi, h | ⟨h, es, k, hb, hk, hI'⟩⟩
  · exact Or.inl h
  · have : i = 0 := by simp at hi; omega
    subst this
    exact Or.inr (Or.inl (by simpa using h))
  · have : i = 0 := by simp at hi; omega
    subst this
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
    exact Or.inr (Or.inr ⟨h, es, k, hb, hk, by simpa using hI'⟩)
end img

/-! ## A2. The read's hard state -/

section reader
variable [GooseExts]

/-- The hard-state step of a fold (`walLastHS`'s). -/
def walHsStep (p : HardStateM) : WalOp → HardStateM
  | .save h _ => phsNext p h
  | .snap _ => p

theorem walLastHS_eq (H : WalHist) : walLastHS H = H.foldl walHsStep hsZero := by
  unfold walLastHS
  congr 1

theorem walSaveSnap_hs (σ : StorContents) (m : SnapshotMetadataM) : (walSaveSnap σ m).hs = σ.hs := by
  unfold walSaveSnap; split <;> rfl

/-- A checked fold's hard state is the hard-state fold. -/
theorem walFoldChkFrom_hs {σ σ' : StorContents} {H : WalHist} (h : walFoldChkFrom σ H = some σ') :
    σ'.hs = H.foldl walHsStep σ.hs := by
  induction H generalizing σ with
  | nil => simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; rfl
  | cons o H ih =>
    cases o with
    | snap m =>
      simp only [walFoldChkFrom] at h
      rw [ih h, walSaveSnap_hs]; rfl
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      rw [ih h]; rfl

theorem walHsStep_filter (c : Nat) (p : HardStateM) (H : WalHist) :
    (H.filter (walKeep c)).foldl walHsStep p = H.foldl walHsStep p := by
  induction H generalizing p with
  | nil => rfl
  | cons o H ih =>
    cases o with
    | save h es => simp only [List.filter_cons, walKeep, ite_true, List.foldl_cons, ih]
    | snap m =>
      simp only [List.filter_cons, walKeep, List.foldl_cons]
      by_cases hc : uint.nat m.Index' ≤ c
      · simp only [hc, decide_true, ite_true, List.foldl_cons, walHsStep, ih]
      · simp only [hc, decide_false, Bool.false_eq_true, ite_false, walHsStep, ih]

/-- **A2: a read's hard state is the history's last saved one** (`ReadAll`'s returned state; the
conjunct the Freeze package left to W4b, [FREEZE-4]). -/
theorem walReadCut_hs {I : WalHist} {k : Nat} {σ : StorContents}
    (h : walReadCut I k = some σ) : σ.hs = walLastHS I := by
  unfold walReadCut at h
  split at h
  · unfold walRead at h
    rw [walFoldChkFrom_hs h, walHsStep_filter, walLastHS_eq]; rfl
  · unfold walReadFrom at h
    simp only at h
    split at h
    · cases h
    · rw [walFoldChkFrom_hs h, walHsStep_filter]
      simp only
      rw [walLastHS_eq, walLastHS_eq, ← List.foldl_append, List.take_append_drop]

/-! ## A3. The read's base is the newest valid pair -/

/-- `walNewestPair`'s step. -/
def walNPStep (acc : Option (w64 × w64)) (p : w64 × w64) : Option (w64 × w64) :=
  match acc with
  | none => some p
  | some q => if uint.nat q.1 ≤ uint.nat p.1 then some p else some q

theorem walNewestPair_eq (l : List (w64 × w64)) : walNewestPair l = l.foldl walNPStep none := rfl

/-- The fold from `some a` ends at `a` or a member of the list, at an index at least `a`'s and every
member's. -/
theorem walNPStep_fold (L : List (w64 × w64)) : ∀ (a : w64 × w64), ∃ r,
    L.foldl walNPStep (some a) = some r ∧ (r = a ∨ r ∈ L) ∧ uint.nat a.1 ≤ uint.nat r.1 ∧
    ∀ p ∈ L, uint.nat p.1 ≤ uint.nat r.1 := by
  induction L with
  | nil => intro a; exact ⟨a, rfl, Or.inl rfl, Nat.le_refl _, by simp⟩
  | cons x L ih =>
    intro a
    by_cases hx : uint.nat a.1 ≤ uint.nat x.1
    · obtain ⟨r, h1, h2, h3, h4⟩ := ih x
      refine ⟨r, by simp only [List.foldl_cons, walNPStep, hx, ite_true]; exact h1, ?_, by omega, ?_⟩
      · rcases h2 with rfl | h2
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ h2)
      · intro p hp; rcases List.mem_cons.1 hp with rfl | hp
        · exact h3
        · exact h4 p hp
    · obtain ⟨r, h1, h2, h3, h4⟩ := ih a
      refine ⟨r, by simp only [List.foldl_cons, walNPStep, hx, ite_false]; exact h1, ?_, h3, ?_⟩
      · rcases h2 with rfl | h2
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem _ h2)
      · intro p hp; rcases List.mem_cons.1 hp with rfl | hp
        · omega
        · exact h4 p hp

theorem walNewestPair_cons (x : w64 × w64) (L : List (w64 × w64)) :
    walNewestPair (x :: L) = L.foldl walNPStep (some x) := rfl

/-- The newest pair is a member. -/
theorem walNewestPair_mem {l : List (w64 × w64)} {s : w64 × w64} (h : walNewestPair l = some s) :
    s ∈ l := by
  cases l with
  | nil => cases h
  | cons x L =>
    rw [walNewestPair_cons] at h
    obtain ⟨r, h1, h2, -, -⟩ := walNPStep_fold L x
    rw [h1] at h; cases h
    rcases h2 with rfl | h2
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h2

/-- The newest pair has the highest index. -/
theorem walNewestPair_max {l : List (w64 × w64)} {s : w64 × w64} (h : walNewestPair l = some s) :
    ∀ p ∈ l, uint.nat p.1 ≤ uint.nat s.1 := by
  cases l with
  | nil => cases h
  | cons x L =>
    rw [walNewestPair_cons] at h
    obtain ⟨r, h1, -, h3, h4⟩ := walNPStep_fold L x
    rw [h1] at h; cases h
    intro p hp; rcases List.mem_cons.1 hp with rfl | hp
    · exact h3
    · exact h4 p hp

theorem walNewestPair_none {l : List (w64 × w64)} : walNewestPair l = none ↔ l = [] := by
  cases l with
  | nil => simp [walNewestPair_eq]
  | cons x L =>
    rw [walNewestPair_cons]
    obtain ⟨r, h1, -⟩ := walNPStep_fold L x
    simp [h1]

/-- The last of equal indexes wins: a pair at least every earlier index is the newest. -/
theorem walNewestPair_last {l : List (w64 × w64)} {p : w64 × w64}
    (h : ∀ q ∈ l, uint.nat q.1 ≤ uint.nat p.1) : walNewestPair (l ++ [p]) = some p := by
  rw [walNewestPair_eq, List.foldl_append, ← walNewestPair_eq]
  cases hl : walNewestPair l with
  | none => rfl
  | some r =>
    simp only [List.foldl_cons, List.foldl_nil, walNPStep, h r (walNewestPair_mem hl), ite_true]

/-- The fold depends on its start only up to an index some member reaches. -/
theorem walNPStep_fold_congr (L : List (w64 × w64)) : ∀ (a a' p : w64 × w64), p ∈ L →
    uint.nat a.1 ≤ uint.nat p.1 → uint.nat a'.1 ≤ uint.nat p.1 →
    L.foldl walNPStep (some a) = L.foldl walNPStep (some a') := by
  induction L with
  | nil => intro a a' p hp; cases hp
  | cons x L ih =>
    intro a a' p hp ha ha'
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only [List.foldl_cons, walNPStep, ha, ha', ite_true]
    · simp only [List.foldl_cons, walNPStep]
      by_cases hxp : uint.nat x.1 ≤ uint.nat p.1
      · have e : ∀ b : w64 × w64, (if uint.nat b.1 ≤ uint.nat x.1 then some x else some b) =
            some (if uint.nat b.1 ≤ uint.nat x.1 then x else b) := by intro b; split <;> rfl
        rw [e a, e a']
        apply ih _ _ p hp <;> split <;> omega
      · have h1 : uint.nat a.1 ≤ uint.nat x.1 := by omega
        have h2 : uint.nat a'.1 ≤ uint.nat x.1 := by omega
        simp only [h1, h2, ite_true]

/-- Starting from the newest pair, the fold stays there. -/
theorem walNewestPair_fold_self {L : List (w64 × w64)} {s : w64 × w64}
    (h : walNewestPair L = some s) : L.foldl walNPStep (some s) = some s := by
  cases L with
  | nil => cases h
  | cons x L =>
    have hx : (x :: L).foldl walNPStep (some x) = some s := by
      simp only [List.foldl_cons, walNPStep, Nat.le_refl, ite_true]; exact h
    rw [walNPStep_fold_congr _ s x s (walNewestPair_mem h) (Nat.le_refl _)
      (walNewestPair_max h x (List.mem_cons_self ..))]
    exact hx

/-- The (index, term) pairs of a history's snapshot records, in order. -/
def walSnapPairs (H : WalHist) : List (w64 × w64) :=
  H.filterMap (fun o => match o with | .snap m => some (m.Index', m.Term') | .save _ _ => none)

/-- A base's (index, term). -/
def walBasePair (b : entryID) : w64 × w64 := (b.index', b.term')

/-- A checked fold's base is the newest-pair fold of its snapshot records from the start's base. -/
theorem walFoldChkFrom_base {σ σ' : StorContents} {H : WalHist} (h : walFoldChkFrom σ H = some σ') :
    some (walBasePair σ'.base) = (walSnapPairs H).foldl walNPStep (some (walBasePair σ.base)) := by
  induction H generalizing σ with
  | nil => simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; rfl
  | cons o H ih =>
    cases o with
    | snap m =>
      simp only [walFoldChkFrom] at h
      rw [ih h]
      simp only [walSnapPairs, List.filterMap_cons, List.foldl_cons]
      congr 1
      unfold walSaveSnap walNPStep
      simp only [walBasePair, StorContents.b]
      by_cases hlt : uint.nat m.Index' < uint.nat σ.base.index'
      · simp only [hlt, ite_true, show ¬ uint.nat σ.base.index' ≤ uint.nat m.Index' by omega, ite_false]
      · simp only [hlt, ite_false, show uint.nat σ.base.index' ≤ uint.nat m.Index' by omega, ite_true]
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      rw [ih h]; rfl

/-- `SaveSnap` either changes nothing or starts at the record. -/
theorem walSaveSnap_cases (σ : StorContents) (m : SnapshotMetadataM) :
    walSaveSnap σ m = σ ∨ ((walSaveSnap σ m).snap = some (SnapshotM.mk [] m) ∧
      (walSaveSnap σ m).base = entryID.mk m.Term' m.Index') := by
  unfold walSaveSnap; split
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩

/-- A checked fold keeps a property of the snapshot and base that every snapshot record establishes. -/
theorem walFoldChkFrom_snapInv (P : Option SnapshotM → entryID → Prop)
    (hP : ∀ m : SnapshotMetadataM, P (some (SnapshotM.mk [] m)) (entryID.mk m.Term' m.Index'))
    {σ σ' : StorContents} {H : WalHist} (h0 : P σ.snap σ.base)
    (h : walFoldChkFrom σ H = some σ') : P σ'.snap σ'.base := by
  induction H generalizing σ with
  | nil => simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; exact h0
  | cons o H ih =>
    cases o with
    | snap m =>
      simp only [walFoldChkFrom] at h
      apply ih _ h
      rcases walSaveSnap_cases σ m with he | ⟨h1, h2⟩
      · rw [he]; exact h0
      · rw [h1, h2]; exact hP m
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      exact ih (σ := { σ with hs := phsNext σ.hs hs, ents := ents }) h0 h

theorem walSnapPairs_filter (c : Nat) (I : WalHist) :
    walSnapPairs (I.filter (walKeep c)) = I.filterMap (fun o => match o with
      | .snap m => if uint.nat m.Index' ≤ c then some (m.Index', m.Term') else none
      | .save _ _ => none) := by
  induction I with
  | nil => rfl
  | cons o I ih =>
    cases o with
    | save h es =>
      simp only [List.filter_cons, walKeep, ite_true, walSnapPairs, List.filterMap_cons] at ih ⊢
      exact ih
    | snap m =>
      simp only [List.filter_cons, walKeep, List.filterMap_cons]
      by_cases hc : uint.nat m.Index' ≤ c
      · simp only [hc, decide_true, ite_true, walSnapPairs, List.filterMap_cons] at ih ⊢
        rw [ih]
      · simp only [hc, decide_false, Bool.false_eq_true, ite_false]; exact ih

/-- `walNewest`'s pair is `walNewestPair` of the snapshot pairs. -/
theorem walNewest_pair (H : WalHist) :
    (walNewest H).map (fun m => (m.Index', m.Term')) = walNewestPair (walSnapPairs H) := by
  unfold walNewest
  rw [walNewestPair_eq]
  generalize hb : (none : Option SnapshotMetadataM) = b
  have hb' : (none : Option (w64 × w64)) = b.map (fun m => (m.Index', m.Term')) := by subst hb; rfl
  rw [hb']
  clear hb hb'
  induction H generalizing b with
  | nil => rfl
  | cons o H ih =>
    cases o with
    | save h es =>
      simp only [List.foldl_cons, walSnapPairs, List.filterMap_cons] at ih ⊢
      exact ih b
    | snap m =>
      simp only [List.foldl_cons, walSnapPairs, List.filterMap_cons] at ih ⊢
      rw [ih]
      congr 1
      cases b with
      | none => rfl
      | some x =>
        simp only [Option.map_some, walNPStep]
        split <;> rfl

/-- **The newest snapshot record of the read's filtered rest is the newest valid pair** (`k ≥ 1`). -/
theorem walNewest_eq_newestPair (I : WalHist) {k : Nat} (hk : k ≠ 0) :
    (walNewest ((I.drop k).filter (walKeep (uint.nat (walLastHS I).Commit')))).map
      (fun m => (m.Index', m.Term')) = walNewestPair (walValidSnaps I k) := by
  rw [walNewest_pair, walSnapPairs_filter]
  simp only [walValidSnaps, hk, ite_false, List.nil_append]
  rfl

/-- **A3: a read's base is the newest valid pair** (what `ValidSnapshotEntries` gives bootstrap and the
tester, W4c's `contentsEq`). -/
theorem walReadCut_base {I : WalHist} {k : Nat} {σ : StorContents} {s : w64 × w64}
    (h : walReadCut I k = some σ) (hs : some s = walNewestPair (walValidSnaps I k)) :
    σ.base = entryID.mk s.2 s.1 := by
  suffices hp : walBasePair σ.base = s by
    rw [← hp]; rfl
  unfold walReadCut at h
  split at h
  · next hk =>
    subst hk
    unfold walRead at h
    have hb := walFoldChkFrom_base h
    rw [walSnapPairs_filter] at hb
    simp only [walValidSnaps, ite_true, List.singleton_append, walNewestPair_cons] at hs
    have : some (walBasePair σ.base) = some s := by rw [hb, hs]; rfl
    exact Option.some.inj this
  · next hk =>
    unfold walReadFrom at h
    simp only at h
    split at h
    · cases h
    · next m hm =>
      have hb := walFoldChkFrom_base h
      have hn := walNewest_eq_newestPair I hk
      rw [hm, ← hs] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      have hL : walNewestPair (walSnapPairs ((I.drop k).filter
          (walKeep (uint.nat (walLastHS I).Commit')))) = some s := by
        rw [walSnapPairs_filter, hs]
        simp only [walValidSnaps, hk, ite_false, List.nil_append]
        rfl
      change some (walBasePair σ.base) = List.foldl walNPStep (some (m.Index', m.Term')) _ at hb
      rw [hn, walNewestPair_fold_self hL] at hb
      exact Option.some.inj hb

/-- **A3: a read's snapshot is at its base**: the newest valid record's, or none (with the pair `(0, 0)`)
only when nothing is purged. -/
theorem walReadCut_snap {I : WalHist} {k : Nat} {σ : StorContents} {s : w64 × w64}
    (h : walReadCut I k = some σ) (hs : some s = walNewestPair (walValidSnaps I k)) :
    (∃ m, σ.snap = some (SnapshotM.mk [] m) ∧ (m.Index', m.Term') = s) ∨
    (k = 0 ∧ σ.snap = none ∧ s = (W64 0, W64 0)) := by
  have hb := walReadCut_base h hs
  let P : Option SnapshotM → entryID → Prop := fun sn b =>
    ∃ m, sn = some (SnapshotM.mk [] m) ∧ b = entryID.mk m.Term' m.Index'
  have hP : ∀ m : SnapshotMetadataM, P (some (SnapshotM.mk [] m)) (entryID.mk m.Term' m.Index') :=
    fun m => ⟨m, rfl, rfl⟩
  have fin : ∀ (m : SnapshotMetadataM), σ.snap = some (SnapshotM.mk [] m) →
      σ.base = entryID.mk m.Term' m.Index' → (m.Index', m.Term') = s := by
    intro m _ h2
    rw [hb] at h2
    simp only [entryID.mk.injEq] at h2
    obtain ⟨h1, h2⟩ := h2
    rw [← h1, ← h2]
  unfold walReadCut at h
  split at h
  · next hk =>
    unfold walRead at h
    have := walFoldChkFrom_snapInv (fun sn b => P sn b ∨ (sn = none ∧ b = entryID.mk (W64 0) (W64 0)))
      (fun m => Or.inl (hP m)) (Or.inr ⟨rfl, rfl⟩) h
    rcases this with ⟨m, h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨m, h1, fin m h1 h2⟩
    · refine Or.inr ⟨hk, h1, ?_⟩
      rw [hb] at h2
      simp only [entryID.mk.injEq] at h2
      obtain ⟨h2, h3⟩ := h2
      exact Prod.ext h3 h2
  · unfold walReadFrom at h
    simp only at h
    split at h
    · cases h
    · next m hm =>
      obtain ⟨m', h1, h2⟩ := walFoldChkFrom_snapInv P hP (hP m) h
      exact Or.inl ⟨m', h1, fin m' h1 h2⟩

/-- The entries are consecutive from the base: the `j`-th has index `b + 1 + j`. -/
def walEntsWf (σ : StorContents) : Prop :=
  ∀ (j : Nat) (e : EntryM), σ.ents[j]? = some e → uint.nat e.Index' = σ.b + 1 + j

theorem readEnt_wf {b : Nat} {ents ents' : List EntryM} {e : EntryM}
    (hw : ∀ (j : Nat) (x : EntryM), ents[j]? = some x → uint.nat x.Index' = b + 1 + j)
    (h : readEnt b ents e = some ents') :
    ∀ (j : Nat) (x : EntryM), ents'[j]? = some x → uint.nat x.Index' = b + 1 + j := by
  unfold readEnt at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; intro j x hx; simp at hx
  · split at h
    · next h1 h2 =>
      simp only [Option.some.injEq] at h; subst h
      intro j x hx
      have hl : (ents.take (uint.nat e.Index' - b - 1)).length = uint.nat e.Index' - b - 1 := by
        simp; omega
      rcases Nat.lt_or_ge j (uint.nat e.Index' - b - 1) with hj | hj
      · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hj] at hx
        exact hw j x hx
      · rw [List.getElem?_append_right (by omega), hl] at hx
        have : j - (uint.nat e.Index' - b - 1) = 0 := by
          rcases Nat.lt_or_ge (j - (uint.nat e.Index' - b - 1)) 1 with h0 | h0
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx
        rw [this] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx
        omega
    · cases h

theorem readEnts_wf {b : Nat} {es : List EntryM} : ∀ {ents ents' : List EntryM},
    (∀ (j : Nat) (x : EntryM), ents[j]? = some x → uint.nat x.Index' = b + 1 + j) →
    es.foldlM (fun ents e => readEnt b ents e) ents = some ents' →
    ∀ (j : Nat) (x : EntryM), ents'[j]? = some x → uint.nat x.Index' = b + 1 + j := by
  induction es with
  | nil => intro ents ents' hw h; simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; subst h; exact hw
  | cons e es ih =>
    intro ents ents' hw h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, h⟩ := h
    exact ih (readEnt_wf hw hm) h

theorem walSaveSnap_wf {σ : StorContents} (m : SnapshotMetadataM) (hw : walEntsWf σ) :
    walEntsWf (walSaveSnap σ m) := by
  unfold walSaveSnap
  split
  · exact hw
  · next hlt =>
    intro j e he
    simp only [StorContents.b] at hlt ⊢
    simp only at he
    split at he
    · rw [List.getElem?_drop] at he
      have := hw _ _ he
      simp only [StorContents.b] at this
      omega
    · simp at he

theorem walFoldChkFrom_wf {σ σ' : StorContents} {H : WalHist} (hw : walEntsWf σ)
    (h : walFoldChkFrom σ H = some σ') : walEntsWf σ' := by
  induction H generalizing σ with
  | nil => simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; exact hw
  | cons o H ih =>
    cases o with
    | snap m => simp only [walFoldChkFrom] at h; exact ih (walSaveSnap_wf m hw) h
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, he, h⟩ := h
      exact ih (σ := { σ with hs := phsNext σ.hs hs, ents := ents }) (readEnts_wf hw he) h

/-- **A4: a read's entries are consecutive from its base** (restart S3's `walRead_wf`, its first
half; no premise). -/
theorem walReadCut_wf {I : WalHist} {k : Nat} {σ : StorContents}
    (h : walReadCut I k = some σ) : walEntsWf σ := by
  unfold walReadCut at h
  split at h
  · exact walFoldChkFrom_wf (by intro j e he; simp [walFresh] at he) h
  · unfold walReadFrom at h
    simp only at h
    split at h
    · cases h
    · exact walFoldChkFrom_wf (by intro j e he; simp at he) h

/-! ## A1 over the model's entries -/

theorem walOps_toRaw_toM (H : List (WalOpG WalEnt)) : (H.map WalOpG.toM).map WalOpG.toRaw = H := by
  simp [List.map_map, Function.comp_def, WalOpG.toRaw_toM]

/-- Images over raw entries are images over the model's. -/
theorem walImg_toM_iff {H I : List (WalOpG WalEnt)} {n : Nat} :
    walImg (H.map WalOpG.toM) n (I.map WalOpG.toM) ↔ walImg H n I := by
  constructor
  · intro h
    have := walImg_map WalOpG.toRaw EntryM.toRaw (fun _ _ => rfl) h
    rwa [walOps_toRaw_toM, walOps_toRaw_toM] at this
  · exact walImg_map WalOpG.toM WalEnt.toM (fun _ _ => rfl)

/-- An image of a raw history read over the model's entries is the model's image of a raw one. -/
theorem walImg_toM_ex {H : List (WalOpG WalEnt)} {n : Nat} {I' : WalHist}
    (h : walImg (H.map WalOpG.toM) n I') : ∃ I, I' = I.map WalOpG.toM ∧ walImg H n I := by
  refine ⟨I'.map WalOpG.toRaw, by simp [List.map_map, Function.comp_def, WalOpG.toM_toRaw], ?_⟩
  rw [← walImg_toM_iff]
  simpa [List.map_map, Function.comp_def, WalOpG.toM_toRaw] using h

/-! ## A5. The read's entries come from the history -/

theorem readEnt_sub {b : Nat} {ents ents' : List EntryM} {e : EntryM}
    (h : readEnt b ents e = some ents') : ∀ x ∈ ents', x ∈ ents ∨ x = e := by
  unfold readEnt at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; intro x hx; cases hx
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact Or.inl (List.mem_of_mem_take hx)
      · exact Or.inr (List.mem_singleton.1 hx)
    · cases h

theorem readEnts_sub {b : Nat} {es : List EntryM} : ∀ {ents ents' : List EntryM},
    es.foldlM (fun ents e => readEnt b ents e) ents = some ents' →
    ∀ x ∈ ents', x ∈ ents ∨ x ∈ es := by
  induction es with
  | nil =>
    intro ents ents' h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; subst h
    exact fun x hx => Or.inl hx
  | cons e es ih =>
    intro ents ents' h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, h⟩ := h
    intro x hx
    rcases ih h x hx with hx | hx
    · rcases readEnt_sub hm x hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ hx)

theorem walSaveSnap_ents_sub (σ : StorContents) (m : SnapshotMetadataM) :
    ∀ x ∈ (walSaveSnap σ m).ents, x ∈ σ.ents := by
  unfold walSaveSnap
  split
  · exact fun x hx => hx
  · intro x hx
    simp only at hx
    split at hx
    · exact List.mem_of_mem_drop hx
    · cases hx

/-- A checked fold's entries are the start's or come from a `Save` of the folded history. -/
theorem walFoldChkFrom_ents_sub {σ σ' : StorContents} {H : WalHist}
    (h : walFoldChkFrom σ H = some σ') :
    ∀ x ∈ σ'.ents, x ∈ σ.ents ∨ ∃ hs es, WalOpG.save hs es ∈ H ∧ x ∈ es := by
  induction H generalizing σ with
  | nil =>
    simp only [walFoldChkFrom, Option.some.injEq] at h; subst h
    exact fun x hx => Or.inl hx
  | cons o H ih =>
    cases o with
    | snap m =>
      simp only [walFoldChkFrom] at h
      intro x hx
      rcases ih h x hx with hx | ⟨hs, es, h1, h2⟩
      · exact Or.inl (walSaveSnap_ents_sub σ m x hx)
      · exact Or.inr ⟨hs, es, List.mem_cons_of_mem _ h1, h2⟩
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, he, h⟩ := h
      intro x hx
      rcases ih (σ := { σ with hs := phsNext σ.hs hs, ents := ents }) h x hx with hx | ⟨hs', es', h1, h2⟩
      · rcases readEnts_sub he x hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr ⟨hs, es, List.mem_cons_self .., hx⟩
      · exact Or.inr ⟨hs', es', List.mem_cons_of_mem _ h1, h2⟩

/-- **A5: a read's entries come from the history's `Save`s.** -/
theorem walReadCut_ents_sub {I : WalHist} {k : Nat} {σ : StorContents}
    (h : walReadCut I k = some σ) : ∀ e ∈ σ.ents, ∃ hs es, WalOpG.save hs es ∈ I ∧ e ∈ es := by
  intro e he
  unfold walReadCut at h
  split at h
  · unfold walRead at h
    rcases walFoldChkFrom_ents_sub h e he with he | ⟨hs, es, h1, h2⟩
    · simp [walFresh] at he
    · exact ⟨hs, es, (List.mem_filter.1 h1).1, h2⟩
  · unfold walReadFrom at h
    simp only at h
    split at h
    · cases h
    · rcases walFoldChkFrom_ents_sub h e he with he | ⟨hs, es, h1, h2⟩
      · cases he
      · exact ⟨hs, es, List.mem_of_mem_drop ((List.mem_filter.1 h1).1), h2⟩

/-- A5 over raw histories: a read's entries come from a raw `Save` (whose entries, for a `sized`
history, are of bounded size). -/
theorem walReadCut_ents_sub_raw {I : List (WalOpG WalEnt)} {k : Nat} {σ : StorContents}
    (h : walReadCut (I.map WalOpG.toM) k = some σ) :
    ∀ e ∈ σ.ents, ∃ hs es, WalOpG.save hs es ∈ I ∧ e.toRaw ∈ es := by
  intro e he
  obtain ⟨hs, es, h1, h2⟩ := walReadCut_ents_sub h e he
  obtain ⟨o, ho, hoe⟩ := List.mem_map.1 h1
  cases o with
  | snap m => simp [WalOpG.toM] at hoe
  | save hs' es' =>
    simp only [WalOpG.toM, WalOpG.save.injEq] at hoe
    obtain ⟨-, rfl⟩ := hoe
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    exact ⟨hs', es', ho, by rw [EntryM.toRaw_toM]; exact hr⟩

/-! ## A4 (second half). The read's last index is bounded -/

/-- Every entry and snapshot index of `I` is at most `B`. -/
def walIdxLe (B : Nat) (I : WalHist) : Prop :=
  (∀ hs es e, WalOpG.save hs es ∈ I → e ∈ es → uint.nat e.Index' ≤ B) ∧
  (∀ m, WalOpG.snap m ∈ I → uint.nat m.Index' ≤ B)

theorem walFoldChkFrom_b_le {B : Nat} {σ σ' : StorContents} {H : WalHist}
    (hH : ∀ m, WalOpG.snap m ∈ H → uint.nat m.Index' ≤ B) (h0 : σ.b ≤ B)
    (h : walFoldChkFrom σ H = some σ') : σ'.b ≤ B := by
  induction H generalizing σ with
  | nil => simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; exact h0
  | cons o H ih =>
    cases o with
    | snap m =>
      simp only [walFoldChkFrom] at h
      refine ih (fun m' hm' => hH m' (List.mem_cons_of_mem _ hm')) ?_ h
      rcases walSaveSnap_cases σ m with he | ⟨-, h2⟩
      · rw [he]; exact h0
      · simp only [StorContents.b, h2]; exact hH m (List.mem_cons_self ..)
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      exact ih (σ := { σ with hs := phsNext σ.hs hs, ents := ents })
        (fun m' hm' => hH m' (List.mem_cons_of_mem _ hm')) h0 h

theorem walNewest_mem {H : WalHist} {m : SnapshotMetadataM} (h : walNewest H = some m) :
    ∃ m', WalOpG.snap m' ∈ H ∧ m'.Index' = m.Index' := by
  have hp := walNewest_pair H
  rw [h, Option.map_some] at hp
  have hm := walNewestPair_mem hp.symm
  obtain ⟨o, ho, hoe⟩ := List.mem_filterMap.1 hm
  cases o with
  | save _ _ => cases hoe
  | snap m' =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hoe
    exact ⟨m', ho, hoe.1⟩

/-- **A4: a read's last index is at most a bound of the history's indexes** (restart S3's
`walRead_wf`, its second half, at `B = 2^61`). -/
theorem walReadCut_last_le {B : Nat} {I : WalHist} {k : Nat} {σ : StorContents}
    (hB : walIdxLe B I) (h : walReadCut I k = some σ) : σ.last ≤ B := by
  unfold StorContents.last
  rcases Nat.eq_zero_or_pos σ.ents.length with hl | hl
  · rw [hl, Nat.add_zero]
    unfold walReadCut at h
    split at h
    · unfold walRead at h
      refine walFoldChkFrom_b_le (fun m hm => hB.2 m ((List.mem_filter.1 hm).1)) ?_ h
      simp [walFresh, StorContents.b]
    · unfold walReadFrom at h
      simp only at h
      split at h
      · cases h
      · next m hm =>
        refine walFoldChkFrom_b_le
          (fun m hm' => hB.2 m (List.mem_of_mem_drop ((List.mem_filter.1 hm').1))) ?_ h
        obtain ⟨m', h1, h2⟩ := walNewest_mem hm
        simp only [StorContents.b]
        rw [← h2]
        exact hB.2 m' (List.mem_of_mem_drop ((List.mem_filter.1 h1).1))
  · have hlt : σ.ents.length - 1 < σ.ents.length := by omega
    have hj : σ.ents[σ.ents.length - 1]? = some (σ.ents[σ.ents.length - 1]'hlt) :=
      List.getElem?_eq_getElem hlt
    have hw := walReadCut_wf h _ _ hj
    obtain ⟨hs, es, h1, h2⟩ := walReadCut_ents_sub h _ (List.getElem_mem hlt)
    have := hB.1 hs es _ h1 h2
    omega

/-! ## A6. The purge bound's lemmas -/

theorem lastFilt_succ (P : Nat → Bool) (n : Nat) :
    ((List.range (n + 1)).filter P).getLast? =
      if P n then some n else ((List.range n).filter P).getLast? := by
  rw [List.range_succ, List.filter_append]
  by_cases hp : P n
  · simp [hp]
  · simp [hp]

theorem lastFilt_some (P : Nat → Bool) : ∀ (n p : Nat), ((List.range n).filter P).getLast? = some p →
    p < n ∧ P p ∧ ∀ i, p < i → i < n → P i = false := by
  intro n
  induction n with
  | zero => intro p h; simp at h
  | succ n ih =>
    intro p h
    rw [lastFilt_succ] at h
    by_cases hp : P n
    · simp only [hp, ite_true, Option.some.injEq] at h; subst h
      exact ⟨by omega, hp, fun i h1 h2 => by omega⟩
    · simp only [hp, Bool.false_eq_true, ite_false] at h
      obtain ⟨h1, h2, h3⟩ := ih p h
      refine ⟨by omega, h2, fun i hi1 hi2 => ?_⟩
      rcases Nat.lt_or_ge i n with hin | hin
      · exact h3 i hi1 hin
      · have : i = n := by omega
        subst this; simpa using hp

theorem lastFilt_none (P : Nat → Bool) : ∀ (n : Nat), ((List.range n).filter P).getLast? = none →
    ∀ i, i < n → P i = false := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    rw [lastFilt_succ] at h
    by_cases hp : P n
    · simp [hp] at h
    · simp only [hp, Bool.false_eq_true, ite_false] at h
      rcases Nat.lt_or_ge i n with hin | hin
      · exact ih h i hin
      · have : i = n := by omega
        subst this; simpa using hp

theorem lastFilt_eq_some (P : Nat → Bool) : ∀ (n p : Nat), p < n → P p = true →
    (∀ i, p < i → i < n → P i = false) → ((List.range n).filter P).getLast? = some p := by
  intro n
  induction n with
  | zero => intro p hp; omega
  | succ n ih =>
    intro p hpn hp hi
    rw [lastFilt_succ]
    rcases Nat.lt_or_ge p n with hlt | hge
    · have : P n = false := hi n hlt (by omega)
      simp only [this, Bool.false_eq_true, ite_false]
      exact ih p hlt hp (fun i h1 h2 => hi i h1 (by omega))
    · have : p = n := by omega
      subst this; simp [hp]

theorem lastFilt_eq_none (P : Nat → Bool) : ∀ (n : Nat), (∀ i, i < n → P i = false) →
    ((List.range n).filter P).getLast? = none := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hi
    rw [lastFilt_succ, hi n (by omega)]
    simp only [Bool.false_eq_true, ite_false]
    exact ih (fun i h => hi i (by omega))

/-- Whether position `i` of `H` holds a snapshot record of index `a` (`walLastSnapPos`'s filter). -/
def walSnapIdxAt {E : Type} (H : List (WalOpG E)) (a : w64) (i : Nat) : Bool :=
  match H[i]? with
  | some (WalOpG.snap m) => decide (m.Index' = a)
  | _ => false

theorem walLastSnapPos_eq {E : Type} (H : List (WalOpG E)) (a : w64) :
    walLastSnapPos H a = (((List.range H.length).filter (walSnapIdxAt H a)).getLast?).getD 0 := rfl

theorem walSnapIdxAt_ge {E : Type} {H : List (WalOpG E)} {a : w64} {i : Nat} (h : H.length ≤ i) :
    walSnapIdxAt H a i = false := by
  simp [walSnapIdxAt, List.getElem?_eq_none h]

/-- The last snapshot position is at most the length (below it when a record exists). -/
theorem walLastSnapPos_le {E : Type} (H : List (WalOpG E)) (a : w64) :
    walLastSnapPos H a ≤ H.length := by
  rw [walLastSnapPos_eq]
  cases h : ((List.range H.length).filter (walSnapIdxAt H a)).getLast? with
  | none => simp
  | some p => simp only [Option.getD_some]; exact Nat.le_of_lt (lastFilt_some _ _ _ h).1

/-- **One more operation**: a snapshot record of index `a` is the new last; anything else keeps it. -/
theorem walLastSnapPos_snoc {E : Type} (H : List (WalOpG E)) (o : WalOpG E) (a : w64) :
    walLastSnapPos (H ++ [o]) a =
      (match o with | .snap m => if m.Index' = a then H.length else walLastSnapPos H a
                    | .save _ _ => walLastSnapPos H a) := by
  have hc : ∀ i, i < H.length → walSnapIdxAt (H ++ [o]) a i = walSnapIdxAt H a i := by
    intro i hi; simp only [walSnapIdxAt, List.getElem?_append_left hi]
  have hfl : (List.range H.length).filter (walSnapIdxAt (H ++ [o]) a) =
      (List.range H.length).filter (walSnapIdxAt H a) :=
    List.filter_congr (fun i hi => hc i (List.mem_range.1 hi))
  have hn : walSnapIdxAt (H ++ [o]) a H.length =
      (match o with | .snap m => decide (m.Index' = a) | .save _ _ => false) := by
    simp only [walSnapIdxAt, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]
    cases o <;> rfl
  rw [walLastSnapPos_eq, List.length_append, List.length_singleton, lastFilt_succ, hfl, hn]
  cases o with
  | save h es => rfl
  | snap m =>
    by_cases hm : m.Index' = a
    · simp [hm]
    · simp [hm, walLastSnapPos_eq]

/-- **A crash keeps the last snapshot position when it is synced.** -/
theorem walLastSnapPos_img {E : Type} {H I : List (WalOpG E)} {n : Nat} {a : w64}
    (hI : walImg H n I) (hp : walLastSnapPos H a < n) : walLastSnapPos I a = walLastSnapPos H a := by
  obtain ⟨hnI, htake⟩ := walImg_prefix hI
  have hpre : ∀ i, i < n → I[i]? = H[i]? := by
    intro i hi
    rw [← List.getElem?_take_of_lt hi, htake, List.getElem?_take_of_lt hi]
  -- past the last position, `I` holds no snapshot record of index `a`
  have hlate : ∀ i, (∀ j, i ≤ j → walSnapIdxAt H a j = false) → ∀ j, i ≤ j → walSnapIdxAt I a j = false := by
    intro i hH j hj
    unfold walSnapIdxAt
    cases ho : I[j]? with
    | none => rfl
    | some o =>
      rcases walImg_getElem? hI ho with hh | ⟨h, es, rfl⟩
      · have := hH j hj
        unfold walSnapIdxAt at this
        rw [hh] at this
        exact this
      · rfl
  rw [walLastSnapPos_eq] at hp ⊢
  rw [walLastSnapPos_eq]
  cases hH : ((List.range H.length).filter (walSnapIdxAt H a)).getLast? with
  | none =>
    have hn := lastFilt_none _ _ hH
    rw [lastFilt_eq_none _ _ (fun i _ => hlate 0 (fun j _ => by
      rcases Nat.lt_or_ge j H.length with hj | hj
      · exact hn j hj
      · exact walSnapIdxAt_ge hj) i (Nat.zero_le _))]
  | some p =>
    rw [hH, Option.getD_some] at hp
    obtain ⟨h1, h2, h3⟩ := lastFilt_some _ _ _ hH
    rw [lastFilt_eq_some _ _ p (by omega) ?_ ?_]
    · unfold walSnapIdxAt at h2 ⊢; rw [hpre p hp]; exact h2
    · intro i hi1 _
      exact hlate (p + 1) (fun j hj => by
        rcases Nat.lt_or_ge j H.length with hjl | hjl
        · exact h3 j (by omega) hjl
        · exact walSnapIdxAt_ge hjl) i (by omega)

theorem lastFilt_getD_le (P : Nat → Bool) (n : Nat) :
    ((List.range (n + 1)).filter P).getLast?.getD 0 ≤ n := by
  cases h : ((List.range (n + 1)).filter P).getLast? with
  | none => simp
  | some p => simp only [Option.getD_some]; have := (lastFilt_some _ _ _ h).1; omega

/-- The guard's position is within the history. -/
theorem walGuardPos_le_length (H : WalHist) (a : w64) : walGuardPos H a ≤ H.length := by
  unfold walGuardPos
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.zero_le _
    · split
      · exact walLastSnapPos_le H a
      · exact Nat.le_refl _

/-- The name bound is within the history. -/
theorem walNameBound_le_length (H : WalHist) (a : Nat) (strict : Bool) :
    walNameBound H a strict ≤ H.length := by
  unfold walNameBound
  split
  · exact Nat.le_refl _
  · exact lastFilt_getD_le _ _

/-- The last element of a filter of `range n` grows with the predicate. -/
theorem lastFilt_mono (P Q : Nat → Bool) (hPQ : ∀ i, P i = true → Q i = true) (n : Nat) :
    ((List.range n).filter P).getLast?.getD 0 ≤ ((List.range n).filter Q).getLast?.getD 0 := by
  cases h : ((List.range n).filter P).getLast? with
  | none => simp
  | some p =>
    obtain ⟨hp, hPp, -⟩ := lastFilt_some _ _ _ h
    simp only [Option.getD_some]
    cases h' : ((List.range n).filter Q).getLast? with
    | none => have := lastFilt_none _ _ h' p hp; rw [hPQ p hPp] at this; cases this
    | some q =>
      obtain ⟨-, -, hq⟩ := lastFilt_some _ _ _ h'
      simp only [Option.getD_some]
      rcases Nat.lt_or_ge q p with hqp | hqp
      · have := hq p hqp hp; rw [hPQ p hPp] at this; cases this
      · exact hqp

/-- The strict name bound (`ReleaseLockTo`'s) is at most the non-strict one (`Open`'s). -/
theorem walNameBound_strict_le (H : WalHist) (a : Nat) :
    walNameBound H a true ≤ walNameBound H a false := by
  unfold walNameBound
  split
  · exact Nat.le_refl _
  · apply lastFilt_mono
    intro i hi
    simp only [ite_true, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hi ⊢
    exact ⟨hi.1, Nat.le_of_lt hi.2⟩

/-- The release position is within the history. -/
theorem walReleasePos_le_length (H : WalHist) (a : w64) : walReleasePos H a ≤ H.length :=
  Nat.le_trans (Nat.min_le_left _ _) (walGuardPos_le_length H a)

/-- `Open`'s position is within the history. -/
theorem walOpenPos_le_length (H : WalHist) (a : w64) : walOpenPos H a ≤ H.length :=
  Nat.le_trans (Nat.min_le_left _ _) (walGuardPos_le_length H a)

/-- `ReleaseLockTo`'s position is at most `Open`'s (the same guard, the strict name bound). -/
theorem walReleasePos_le_openPos (H : WalHist) (a : w64) : walReleasePos H a ≤ walOpenPos H a := by
  have := walNameBound_strict_le H (uint.nat a)
  simp only [walReleasePos, walOpenPos]
  omega

/-- No index `2^64-1` in `H ++ [o]`. -/
theorem walHasMaxIdx_snoc {H : WalHist} {o : WalOp} (hH : ¬ walHasMaxIdx H) (ho : ¬ walHasMaxIdx [o]) :
    ¬ walHasMaxIdx (H ++ [o]) := by
  intro ⟨o', ho', hm⟩
  rcases List.mem_append.1 ho' with h | h
  · exact hH ⟨o', h, hm⟩
  · exact ho ⟨o', h, hm⟩

/-- **The release guard for one more operation**: the guard of `H`, the new last commit at least `a`
(when the operation is after `p`), a new `Save`'s entries above `a` (when a snapshot record of index
`≥ a` precedes it), a new snapshot record at least `a` (when after `p`), and no index `2^64-1` in the
new operation (clause 4). -/
theorem walRelGuard_snoc {H : WalHist} {a : w64} {p : Nat} (o : WalOp) (hg : walRelGuard H a p)
    (h1 : p < H.length + 1 → uint.nat a ≤ uint.nat (walLastHS (H ++ [o])).Commit')
    (h2 : ∀ hs es, o = .save hs es → (∃ (q : Nat) (m : SnapshotMetadataM), H[q]? = some (WalOpG.snap m) ∧ uint.nat a ≤ uint.nat m.Index') →
      ∀ e ∈ es, uint.nat a < uint.nat e.Index')
    (h3 : ∀ m, o = .snap m → p < H.length → uint.nat a ≤ uint.nat m.Index')
    (h4 : ¬ walHasMaxIdx [o]) :
    walRelGuard (H ++ [o]) a p := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨?_, ?_, ?_, walHasMaxIdx_snoc g4 h4⟩
  · intro j hpj hj
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j (H.length + 1) with hlt | hge
    · rw [List.take_append_of_le_length (by omega)]
      exact g1 j hpj (by omega)
    · have : j = H.length + 1 := by omega
      subst this
      rw [List.take_of_length_le (by simp)]
      exact h1 (by omega)
  · intro q j m hs es e hq ham hqj hj he
    have hjl := getElem?_some_lt hj
    simp only [List.length_append, List.length_singleton] at hjl
    rcases Nat.lt_or_ge j H.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hj
      rw [List.getElem?_append_left (by omega)] at hq
      exact g2 q j m hs es e hq ham hqj hj he
    · have : j = H.length := by omega
      subst this
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at hj
      rw [List.getElem?_append_left hqj] at hq
      exact h2 hs es hj ⟨q, m, hq, ham⟩ e he
  · intro j m hpj hj
    have hjl := getElem?_some_lt hj
    simp only [List.length_append, List.length_singleton] at hjl
    rcases Nat.lt_or_ge j H.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hj
      exact g3 j m hpj hj
    · have : j = H.length := by omega
      subst this
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at hj
      exact h3 m hj hpj


/-! ## C (first half). The purged read against the unpurged read: what needs no release bound

C2 (`walReadFrom_compacts`) waits for W4a.2's release bound; these are the relation and its laws, the
read's relaxed form, and the read's base below its commit. -/

/-- **C1**: the read from position 0 is the unpurged read. -/
theorem walReadCut_zero (I : WalHist) : walReadCut I 0 = walRead I := by
  simp only [walReadCut, ite_true]

theorem walReadCut_pos {I : WalHist} {k : Nat} (hk : k ≠ 0) : walReadCut I k = walReadFrom I k := by
  simp only [walReadCut, hk, ite_false]

/-- **C1: the relaxed read is monotone in the purge bound.** -/
theorem walReadR_mono {I : WalHist} {p p' : Nat} {σ : StorContents} (hp : p ≤ p')
    (h : walReadR I p σ) : walReadR I p' σ := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, Nat.le_trans hk hp, h⟩

/-- Nothing purged: the relaxed read is the unpurged read. -/
theorem walReadR_zero {I : WalHist} {σ : StorContents} : walReadR I 0 σ ↔ walRead I = some σ := by
  constructor
  · intro ⟨k, hk, h⟩
    rw [Nat.le_zero.1 hk, walReadCut_zero] at h
    exact h
  · intro h
    exact ⟨0, Nat.le_refl _, by rw [walReadCut_zero]; exact h⟩

theorem walReadR_of_read {I : WalHist} {p : Nat} {σ : StorContents} (h : walRead I = some σ) :
    walReadR I p σ :=
  walReadR_mono (Nat.zero_le p) (walReadR_zero.2 h)

/-- **A read's base is at or below its commit** (every kept snapshot record is, and the commit is the
history's last, `walReadCut_hs`). -/
theorem walReadCut_b_le_commit {I : WalHist} {k : Nat} {σ : StorContents}
    (h : walReadCut I k = some σ) : σ.b ≤ σ.commit := by
  have hc : σ.commit = uint.nat (walLastHS I).Commit' := by
    simp only [StorContents.commit, walReadCut_hs h]
  rw [hc]
  have hkept : ∀ (H : WalHist) m, WalOpG.snap m ∈ H.filter (walKeep (uint.nat (walLastHS I).Commit')) →
      uint.nat m.Index' ≤ uint.nat (walLastHS I).Commit' := by
    intro H m hm
    have := (List.mem_filter.1 hm).2
    simpa [walKeep] using this
  unfold walReadCut at h
  split at h
  · unfold walRead at h
    exact walFoldChkFrom_b_le (hkept I) (by simp [walFresh, StorContents.b]) h
  · unfold walReadFrom at h
    simp only at h
    split at h
    · cases h
    · next m hm =>
      refine walFoldChkFrom_b_le (hkept _) ?_ h
      obtain ⟨m', h1, h2⟩ := walNewest_mem hm
      simp only [StorContents.b]
      rw [← h2]
      exact hkept _ m' h1

/-- **`σ`'s snapshot is a record at its base** (what a purged read starts from). -/
def walSnapAtBase (σ : StorContents) : Prop :=
  ∃ m, σ.snap = some (SnapshotM.mk [] m) ∧ σ.base = entryID.mk m.Term' m.Index'

/-- **A purged read's snapshot is at its base.** -/
theorem walReadCut_snapAtBase {I : WalHist} {k : Nat} {σ : StorContents} (hk : k ≠ 0)
    (h : walReadCut I k = some σ) : walSnapAtBase σ := by
  rw [walReadCut_pos hk] at h
  unfold walReadFrom at h
  simp only at h
  split at h
  · cases h
  · next m _ =>
    exact walFoldChkFrom_snapInv (fun sn b => ∃ m, sn = some (SnapshotM.mk [] m) ∧
      b = entryID.mk m.Term' m.Index') (fun m => ⟨m, rfl, rfl⟩) ⟨m, rfl, rfl⟩ h

/-- **`σ'` is a compaction of `σ`** (the plan's `StorCompacts`, C2's conclusion): its base at or above
`σ`'s and at most `σ`'s commit, the same hard state, `σ`'s entries above its base, and its snapshot
`σ`'s at the same base or a record at its own base. -/
def StorCompacts (σ σ' : StorContents) : Prop :=
  σ.b ≤ σ'.b ∧ σ'.b ≤ σ.commit ∧ σ'.hs = σ.hs ∧ σ'.ents = σ.ents.drop (σ'.b - σ.b) ∧
  ((σ'.base = σ.base ∧ σ'.snap = σ.snap) ∨ walSnapAtBase σ')

theorem StorCompacts_refl {σ : StorContents} (h : σ.b ≤ σ.commit) : StorCompacts σ σ :=
  ⟨Nat.le_refl _, h, rfl, by rw [Nat.sub_self, List.drop_zero], Or.inl ⟨rfl, rfl⟩⟩

theorem StorCompacts_trans {σ σ' σ'' : StorContents} (h1 : StorCompacts σ σ')
    (h2 : StorCompacts σ' σ'') : StorCompacts σ σ'' := by
  obtain ⟨a1, b1, c1, d1, e1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2⟩ := h2
  have hcm : σ'.commit = σ.commit := by simp only [StorContents.commit, c1]
  refine ⟨Nat.le_trans a1 a2, hcm ▸ b2, c2.trans c1, ?_, ?_⟩
  · rw [d2, d1, List.drop_drop]
    congr 1
    omega
  · rcases e2 with ⟨hb, hs⟩ | hs
    · rcases e1 with ⟨hb', hs'⟩ | ⟨m, hm1, hm2⟩
      · exact Or.inl ⟨hb.trans hb', hs.trans hs'⟩
      · exact Or.inr ⟨m, hs.trans hm1, hb.trans hm2⟩
    · exact Or.inr hs

/-- **C4's identity shape**: a compaction at the same base and snapshot is the read itself. -/
theorem StorCompacts_eq {σ σ' : StorContents} (h : StorCompacts σ σ') (hb : σ'.base = σ.base)
    (hs : σ'.snap = σ.snap) : σ' = σ := by
  obtain ⟨-, -, hh, he, -⟩ := h
  have hbb : σ'.b = σ.b := by simp only [StorContents.b, hb]
  rw [hbb, Nat.sub_self, List.drop_zero] at he
  cases σ; cases σ'
  simp only at hb hs hh he
  rw [hb, hs, hh, he]

/-- A compaction keeps the entries consecutive from the base. -/
theorem StorCompacts_wf {σ σ' : StorContents} (h : StorCompacts σ σ') (hw : walEntsWf σ) :
    walEntsWf σ' := by
  obtain ⟨ha, -, -, he, -⟩ := h
  intro j e hj
  rw [he, List.getElem?_drop] at hj
  have := hw _ _ hj
  omega

/-- **C3's `k = 0` case**: the unpurged read is a compaction of itself. -/
theorem walRead_compacts_self {I : WalHist} {σ : StorContents} (h : walRead I = some σ) :
    StorCompacts σ σ :=
  StorCompacts_refl (walReadCut_b_le_commit (k := 0) (by rw [walReadCut_zero]; exact h))

/-! ## C (second half). The purged read is the unpurged read, under the name bound

C2-C4. With every file named above every snapshot record before it (W4a.2's name bound, `walNameBound`
non-strict: `Open`'s, and so `ReleaseLockTo`'s), a purge from `k ≥ 1` deletes no snapshot record as high
as `a` (a snapshot record the history holds, within its commit), so the purged read starts at the
unpurged read's newest record; the two folds then agree once that record is reached, provided the
commit never exceeds the read's last index (`walCommitLe`: raft's `committed ≤ lastIndex`). Without
that premise the claim is false: entries above `M` saved before `M`'s record, a received snapshot
below `M` (above the running commit) that empties the unpurged read, then a `Save` raising the commit
to `M` with no entry, then `M`'s record (the plan's risk R1; notes/decisions.md, "WAL W4b"). -/

/-- The last entry record's index (`walLastIdx`'s first fold). -/
def walLastEntF (x : Nat) : WalOp → Nat
  | .save _ es => (es.getLast?.map (fun e => uint.nat e.Index')).getD x
  | .snap _ => x

/-- The highest snapshot record's index (`walLastIdx`'s second fold). -/
def walMaxSnapF (x : Nat) : WalOp → Nat
  | .save _ _ => x
  | .snap m => max x (uint.nat m.Index')

theorem walLastIdx_eq (P : WalHist) :
    walLastIdx P = max (P.foldl walLastEntF 0) (P.foldl walMaxSnapF 0) := by
  unfold walLastIdx
  congr 1

theorem walMaxSnap_ge : ∀ (L : WalHist) (x : Nat), x ≤ L.foldl walMaxSnapF x := by
  intro L
  induction L with
  | nil => intro x; exact Nat.le_refl _
  | cons o L ih =>
    intro x
    cases o with
    | save h es => exact ih x
    | snap m => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem walMaxSnap_mem : ∀ (L : WalHist) (x : Nat) (m : SnapshotMetadataM), WalOpG.snap m ∈ L →
    uint.nat m.Index' ≤ L.foldl walMaxSnapF x := by
  intro L
  induction L with
  | nil => intro x m hm; cases hm
  | cons o L ih =>
    intro x m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact Nat.le_trans (Nat.le_max_right _ _) (walMaxSnap_ge L _)
    · exact ih _ m hm

theorem walLastEnt_noNE : ∀ (L : WalHist) (x : Nat), (∀ h es, WalOpG.save h es ∈ L → es = []) →
    L.foldl walLastEntF x = x := by
  intro L
  induction L with
  | nil => intro x _; rfl
  | cons o L ih =>
    intro x hne
    cases o with
    | save h es =>
      have he := hne h es (List.mem_cons_self ..)
      subst he
      exact ih x (fun h' es' hm => hne h' es' (List.mem_cons_of_mem _ hm))
    | snap m => exact ih x (fun h' es' hm => hne h' es' (List.mem_cons_of_mem _ hm))

/-- The filter lowers the highest snapshot record. -/
theorem walLastIdx_filter (c : Nat) : ∀ (L : WalHist) (x y : Nat), x ≤ y →
    (L.filter (walKeep c)).foldl walMaxSnapF x ≤ L.foldl walMaxSnapF y := by
  intro L
  induction L with
  | nil => intro x y hxy; exact hxy
  | cons o L ih =>
    intro x y hxy
    cases o with
    | save h es =>
      simp only [List.filter_cons, walKeep, ite_true, List.foldl_cons, walMaxSnapF]
      exact ih x y hxy
    | snap m =>
      simp only [List.filter_cons, walKeep, List.foldl_cons, walMaxSnapF]
      by_cases hc : uint.nat m.Index' ≤ c
      · simp only [hc, decide_true, ite_true, List.foldl_cons, walMaxSnapF]
        exact ih _ _ (by omega)
      · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
        exact ih _ _ (by omega)

theorem walLastEnt_filter (c : Nat) : ∀ (L : WalHist) (x : Nat),
    (L.filter (walKeep c)).foldl walLastEntF x = L.foldl walLastEntF x := by
  intro L
  induction L with
  | nil => intro x; rfl
  | cons o L ih =>
    intro x
    cases o with
    | save h es => simp only [List.filter_cons, walKeep, ite_true, List.foldl_cons]; exact ih _
    | snap m =>
      simp only [List.filter_cons, walKeep, List.foldl_cons]
      by_cases hc : uint.nat m.Index' ≤ c
      · simp only [hc, decide_true, ite_true, List.foldl_cons, walLastEntF]; exact ih _
      · simp only [hc, decide_false, Bool.false_eq_true, ite_false, walLastEntF]; exact ih _

theorem walLastIdx_filter_le (c : Nat) (L : WalHist) :
    walLastIdx (L.filter (walKeep c)) ≤ walLastIdx L := by
  rw [walLastIdx_eq, walLastIdx_eq, walLastEnt_filter]
  have := walLastIdx_filter c L 0 0 (Nat.le_refl _)
  omega

theorem readEnt_last {b : Nat} {ents x : List EntryM} {e : EntryM} (h : readEnt b ents e = some x) :
    b + x.length ≤ max b (uint.nat e.Index') := by
  unfold readEnt at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp only [List.length_nil]; omega
  · split at h
    · simp only [Option.some.injEq] at h; subst h; simp; omega
    · cases h

theorem readEnts_last {b : Nat} : ∀ {es : List EntryM} {ents x : List EntryM},
    es.foldlM (fun ents e => readEnt b ents e) ents = some x →
    (es = [] ∧ x = ents) ∨ ∃ e, es.getLast? = some e ∧ b + x.length ≤ max b (uint.nat e.Index') := by
  intro es
  induction es with
  | nil =>
    intro ents x h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact Or.inl ⟨rfl, h.symm⟩
  | cons e es ih =>
    intro ents x h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    right
    rcases ih h with ⟨rfl, rfl⟩ | ⟨e', he', hb⟩
    · exact ⟨e, by simp, readEnt_last hy⟩
    · exact ⟨e', by rw [List.getLast?_cons, he']; rfl, hb⟩

/-- **A fold's base and last index are bounded by the history's highest snapshot record and last
index** (`walLastIdx`, from accumulators `x`, `y`). -/
theorem walFoldChkFrom_last : ∀ {L : WalHist} {τ τ' : StorContents} {x y : Nat},
    τ.b ≤ y → τ.last ≤ max x y → walFoldChkFrom τ L = some τ' →
    τ'.b ≤ L.foldl walMaxSnapF y ∧ τ'.last ≤ max (L.foldl walLastEntF x) (L.foldl walMaxSnapF y) := by
  intro L
  induction L with
  | nil =>
    intro τ τ' x y hb hl h
    simp only [walFoldChkFrom, Option.some.injEq] at h; subst h
    exact ⟨hb, hl⟩
  | cons o L ih =>
    intro τ τ' x y hb hl h
    cases o with
    | snap m =>
      simp only [walFoldChkFrom] at h
      simp only [List.foldl_cons, walMaxSnapF, walLastEntF]
      refine ih ?_ ?_ h
      · unfold walSaveSnap; split
        · omega
        · simp only [StorContents.b]; omega
      · unfold walSaveSnap; split
        · omega
        · next hlt =>
          simp only [StorContents.last, StorContents.b] at hl hlt ⊢
          split
          · simp only [List.length_drop]; omega
          · simp only [List.length_nil]; omega
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, he, h⟩ := h
      simp only [List.foldl_cons, walMaxSnapF, walLastEntF]
      refine ih (τ := { τ with hs := phsNext τ.hs hs, ents := ents }) (by exact hb) ?_ h
      rcases readEnts_last he with ⟨rfl, rfl⟩ | ⟨e, hle, hbd⟩
      · exact hl
      · rw [hle]
        simp only [StorContents.last, StorContents.b, Option.map_some, Option.getD_some] at hb hbd ⊢
        omega

/-- The checked fold of a concatenation. -/
theorem walFoldChkFrom_append : ∀ (A B : WalHist) (τ : StorContents),
    walFoldChkFrom τ (A ++ B) = (walFoldChkFrom τ A).bind (fun τ1 => walFoldChkFrom τ1 B) := by
  intro A
  induction A with
  | nil => intro B τ; rfl
  | cons o A ih =>
    intro B τ
    cases o with
    | snap m => simp only [List.cons_append, walFoldChkFrom]; exact ih B _
    | save hs es =>
      simp only [List.cons_append, walFoldChkFrom, Option.bind_eq_bind]
      cases es.foldlM (fun ents e => readEnt τ.b ents e) τ.ents with
      | none => rfl
      | some ents => simp only [Option.bind_some]; exact ih B _

/-- **Raft's `committed ≤ lastIndex`, along a fold**: every prefix of `L` folded from `τ` has its
commit at most its last index. -/
def walCommitLeFrom (τ : StorContents) (L : WalHist) : Prop :=
  ∀ (n : Nat) (τ' : StorContents), walFoldChkFrom τ (L.take n) = some τ' → τ'.commit ≤ τ'.last

/-- **C2's premise: the restart's fold never has its commit above its last index** (every prefix of
the kept records, folded from the start; raft's `committed ≤ lastIndex`, which every `Save`'s hard
state keeps). -/
def walCommitLe (I : WalHist) : Prop :=
  walCommitLeFrom walFresh (I.filter (walKeep (uint.nat (walLastHS I).Commit')))

theorem walCommitLeFrom_append {τ τ1 : StorContents} {A B : WalHist} (h : walCommitLeFrom τ (A ++ B))
    (hA : walFoldChkFrom τ A = some τ1) : walCommitLeFrom τ1 B := by
  intro n τ2 h2
  apply h (A.length + n)
  rw [List.take_length_add_append, walFoldChkFrom_append, hA]
  exact h2

/-- The two reads' entries before a `Save`: synced, the purged read's empty, or the full read's below
`M`. -/
def walEntsPre (M b : Nat) (ents ents' : List EntryM) : Prop :=
  ents' = ents.drop (M - b) ∨ ents' = [] ∨ b + ents.length < M

theorem readEnt_pair {M b : Nat} {ents ents' x x' : List EntryM} {e : EntryM} (hb : b ≤ M)
    (hpre : walEntsPre M b ents ents')
    (h : readEnt b ents e = some x) (h' : readEnt M ents' e = some x') :
    x' = x.drop (M - b) := by
  unfold readEnt at h h'
  by_cases heM : uint.nat e.Index' ≤ M
  · simp only [heM, ite_true, Option.some.injEq] at h'
    subst h'
    by_cases heb : uint.nat e.Index' ≤ b
    · simp only [heb, ite_true, Option.some.injEq] at h; subst h; simp
    · simp only [heb, ite_false] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        symm; apply List.drop_eq_nil_of_le
        simp; omega
      · cases h
  · have heb : ¬ uint.nat e.Index' ≤ b := by omega
    simp only [heM, heb, ite_false] at h h'
    split at h
    · next hoff =>
      split at h'
      · next hoff' =>
        simp only [Option.some.injEq] at h h'; subst h h'
        rw [List.drop_append_of_le_length (by simp; omega), List.drop_take]
        have hsub : uint.nat e.Index' - b - 1 - (M - b) = uint.nat e.Index' - M - 1 := by omega
        rw [hsub]
        rcases hpre with rfl | rfl | hlt
        · rfl
        · simp at hoff'
          have : uint.nat e.Index' - M - 1 = 0 := by omega
          rw [this]; simp
        · omega
      · cases h'
    · cases h

theorem readEnts_sync {M b : Nat} (hb : b ≤ M) : ∀ {es : List EntryM} {ents ents' x x' : List EntryM},
    ents' = ents.drop (M - b) →
    es.foldlM (fun ents e => readEnt b ents e) ents = some x →
    es.foldlM (fun ents e => readEnt M ents e) ents' = some x' → x' = x.drop (M - b) := by
  intro es
  induction es with
  | nil =>
    intro ents ents' x x' hs h h'
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h h'
    subst h h'; exact hs
  | cons e es ih =>
    intro ents ents' x x' hs h h'
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h h'
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨y', hy', h'⟩ := h'
    exact ih (readEnt_pair hb (Or.inl hs) hy hy') h h'

/-- No record of index `M` before a `Save` with entries. -/
def walNEBefore (M : Nat) (L : WalHist) : Prop :=
  ∃ (L1 : WalHist) (h : HardStateM) (es : List EntryM) (L2 : WalHist),
    L = L1 ++ WalOpG.save h es :: L2 ∧ es ≠ [] ∧ ∀ m, WalOpG.snap m ∈ L1 → uint.nat m.Index' ≠ M

theorem walNEBefore_snap {M : Nat} {m : SnapshotMetadataM} {L : WalHist}
    (h : walNEBefore M (WalOpG.snap m :: L)) : uint.nat m.Index' ≠ M ∧ walNEBefore M L := by
  obtain ⟨L1, hs, es, L2, hL, hes, hL1⟩ := h
  cases L1 with
  | nil => simp at hL
  | cons x L1 =>
    simp only [List.cons_append, List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    exact ⟨hL1 m (List.mem_cons_self ..),
      L1, hs, es, L2, rfl, hes, fun m' hm' => hL1 m' (List.mem_cons_of_mem _ hm')⟩

theorem walNEBefore_save_nil {M : Nat} {hs : HardStateM} {L : WalHist}
    (h : walNEBefore M (WalOpG.save hs [] :: L)) : walNEBefore M L := by
  obtain ⟨L1, hs', es, L2, hL, hes, hL1⟩ := h
  cases L1 with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, WalOpG.save.injEq] at hL
    exact absurd hL.1.2.symm hes
  | cons x L1 =>
    simp only [List.cons_append, List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    exact ⟨L1, hs', es, L2, rfl, hes, fun m' hm' => hL1 m' (List.mem_cons_of_mem _ hm')⟩

/-- The state of the two folds before the newest record `M` is reached: synced, the unpurged read's
last index below `M` (after a received snapshot), or the purged read empty with a `Save` with entries
ahead. -/
def walPairSt (M : Nat) (τ τ' : StorContents) (L : WalHist) : Prop :=
  τ'.ents = τ.ents.drop (M - τ.b) ∨ (τ.last < M ∧ τ.commit ≤ τ.last) ∨
    (τ'.ents = [] ∧ walNEBefore M L)

theorem walSaveSnap_pairSt {M : Nat} {τ τ' : StorContents} {m : SnapshotMetadataM} {L : WalHist}
    (hmM : uint.nat m.Index' < M) (hb : τ.b ≤ M) (hst : walPairSt M τ τ' (WalOpG.snap m :: L)) :
    (walSaveSnap τ m).b ≤ M ∧ walPairSt M (walSaveSnap τ m) τ' L := by
  have hD : τ'.ents = [] ∧ walNEBefore M (WalOpG.snap m :: L) → τ'.ents = [] ∧ walNEBefore M L :=
    fun ⟨h1, h2⟩ => ⟨h1, (walNEBefore_snap h2).2⟩
  unfold walSaveSnap
  split
  · refine ⟨hb, ?_⟩
    rcases hst with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hD h))
  · next hlt =>
    simp only [StorContents.b] at hlt hb ⊢
    refine ⟨by omega, ?_⟩
    simp only [walPairSt, StorContents.b, StorContents.last, StorContents.commit] at hst ⊢
    by_cases hc : uint.nat m.Index' ≤ uint.nat τ.hs.Commit'
    · simp only [hc, ite_true]
      rcases hst with h | h | h
      · left; rw [h, List.drop_drop]; congr 1; omega
      · right; left; simp only [List.length_drop]; omega
      · right; right; exact ⟨h.1, (walNEBefore_snap h.2).2⟩
    · simp only [hc, ite_false]
      rcases hst with h | h | h
      · right; left; simp only [List.length_nil]; omega
      · right; left; simp only [List.length_nil]; omega
      · right; right; exact ⟨h.1, (walNEBefore_snap h.2).2⟩

/-- **The two folds agree once the newest record `M` is reached** (the induction of C2). -/
theorem walFoldChk_sim (M : Nat) : ∀ (L : WalHist) (τ τ' σ σ' : StorContents),
    (∀ m, WalOpG.snap m ∈ L → uint.nat m.Index' ≤ M) →
    (∃ m, WalOpG.snap m ∈ L ∧ uint.nat m.Index' = M) →
    τ'.hs = τ.hs → τ'.b = M → τ.b ≤ M → walPairSt M τ τ' L → walCommitLeFrom τ L →
    walFoldChkFrom τ L = some σ → walFoldChkFrom τ' L = some σ' → σ' = σ := by
  intro L
  induction L with
  | nil => intro τ τ' σ σ' _ hex; obtain ⟨m, hm, -⟩ := hex; cases hm
  | cons o L ih =>
    intro τ τ' σ σ' hle hex hhs hb' hb hst hcl h h'
    have hcl' : ∀ τ1, walFoldChkFrom τ [o] = some τ1 → walCommitLeFrom τ1 L :=
      fun τ1 h1 => walCommitLeFrom_append (A := [o]) hcl h1
    cases o with
    | snap m =>
      simp only [walFoldChkFrom] at h h'
      by_cases hmM : uint.nat m.Index' = M
      · have hc : τ'.commit = τ.commit := by simp only [StorContents.commit, hhs]
        have hents : M ≤ τ.commit → τ'.ents = τ.ents.drop (M - τ.b) := by
          intro hMc
          rcases hst with hS | ⟨hl, hcl2⟩ | ⟨-, hne⟩
          · exact hS
          · omega
          · exact absurd hmM (walNEBefore_snap hne).1
        have heq : walSaveSnap τ' m = walSaveSnap τ m := by
          unfold walSaveSnap
          have h1 : ¬ uint.nat m.Index' < τ'.b := by omega
          have h2 : ¬ uint.nat m.Index' < τ.b := by omega
          simp only [h1, h2, ite_false]
          rw [hc, hmM, hb']
          by_cases hMc : M ≤ τ.commit
          · simp only [hMc, ite_true, Nat.sub_self, List.drop_zero, hents hMc]
            cases τ; cases τ'; simp only at hhs ⊢; rw [hhs]
          · simp only [hMc, ite_false]
            cases τ; cases τ'; simp only at hhs ⊢; rw [hhs]
        rw [heq, h] at h'
        exact (Option.some.inj h').symm
      · have hlt : uint.nat m.Index' < M := by
          have := hle m (List.mem_cons_self ..); omega
        have hτ' : walSaveSnap τ' m = τ' := by
          unfold walSaveSnap; simp only [show uint.nat m.Index' < τ'.b by omega, ite_true]
        rw [hτ'] at h'
        obtain ⟨hb2, hst2⟩ := walSaveSnap_pairSt hlt hb hst
        refine ih _ _ σ σ' (fun m' hm' => hle m' (List.mem_cons_of_mem _ hm')) ?_ ?_ hb' hb2 hst2
          (hcl' _ (by simp only [walFoldChkFrom])) h h'
        · obtain ⟨m', hm', hm'M⟩ := hex
          rcases List.mem_cons.1 hm' with he | hm'
          · cases he; exact absurd hm'M hmM
          · exact ⟨m', hm', hm'M⟩
        · rw [walSaveSnap_hs]; exact hhs
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h h'
      obtain ⟨x, hx, h⟩ := h
      obtain ⟨x', hx', h'⟩ := h'
      have hcl1 := hcl' { τ with hs := phsNext τ.hs hs, ents := x }
        (by simp only [walFoldChkFrom, Option.bind_eq_bind, hx, Option.bind_some])
      refine ih { τ with hs := phsNext τ.hs hs, ents := x } { τ' with hs := phsNext τ'.hs hs, ents := x' }
        σ σ' (fun m' hm' => hle m' (List.mem_cons_of_mem _ hm')) ?_ (by simp only [hhs]) hb' hb ?_ hcl1 h h'
      · obtain ⟨m', hm', hm'M⟩ := hex
        rcases List.mem_cons.1 hm' with he | hm'
        · cases he
        · exact ⟨m', hm', hm'M⟩
      · cases es with
        | nil =>
          simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hx hx'
          subst hx hx'
          rcases hst with hS | ⟨hl, -⟩ | ⟨hD, hne⟩
          · exact Or.inl hS
          · right; left
            refine ⟨hl, ?_⟩
            exact hcl 1 _ (by simp only [List.take_succ_cons, List.take_zero, walFoldChkFrom,
              List.foldlM_nil, Option.bind_eq_bind, Option.pure_def, Option.bind_some])
          · exact Or.inr (Or.inr ⟨hD, walNEBefore_save_nil hne⟩)
        | cons e es =>
          left
          simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx hx'
          obtain ⟨y, hy, hx⟩ := hx
          obtain ⟨y', hy', hx'⟩ := hx'
          have hpre : walEntsPre M τ.b τ.ents τ'.ents := by
            rcases hst with hS | ⟨hl, -⟩ | ⟨hD, -⟩
            · exact Or.inl hS
            · exact Or.inr (Or.inr hl)
            · exact Or.inr (Or.inl hD)
          rw [hb'] at hy' hx'
          exact readEnts_sync hb (readEnt_pair hb hpre hy hy') hx hx'

/-- The newest record has the highest index. -/
theorem walNewest_max {H : WalHist} {m : SnapshotMetadataM} (h : walNewest H = some m) :
    ∀ m', WalOpG.snap m' ∈ H → uint.nat m'.Index' ≤ uint.nat m.Index' := by
  intro m' hm'
  have hp := walNewest_pair H
  rw [h, Option.map_some] at hp
  have := walNewestPair_max hp.symm (m'.Index', m'.Term')
    (List.mem_filterMap.2 ⟨WalOpG.snap m', hm', rfl⟩)
  exact this

theorem lastFilt_getD_mem (P : Nat → Bool) (n : Nat)
    (h : 0 < ((List.range n).filter P).getLast?.getD 0) :
    ((List.range n).filter P).getLast?.getD 0 < n ∧ P (((List.range n).filter P).getLast?.getD 0) = true := by
  cases hl : ((List.range n).filter P).getLast? with
  | none => rw [hl] at h; simp at h
  | some p =>
    obtain ⟨hp, hPp, -⟩ := lastFilt_some _ _ _ hl
    exact ⟨hp, hPp⟩

/-- A position at or above `k` that the non-strict name bound's filter holds. -/
theorem walNameBound_witness {I : WalHist} {k a : Nat} (hk0 : 0 < k) (hk : k ≤ walNameBound I a false)
    (hmax : ¬ walHasMaxIdx I) :
    ∃ b0, k ≤ b0 ∧ b0 ≤ I.length ∧ walLastIdx (I.take b0) + 1 ≤ a := by
  unfold walNameBound at hk
  simp only [hmax, ite_false] at hk
  obtain ⟨hp, hPp⟩ := lastFilt_getD_mem _ _ (Nat.lt_of_lt_of_le hk0 hk)
  simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq] at hPp
  exact ⟨_, hk, by omega, hPp.2⟩

/-- **C2 (exact form): the read purged from `k ≥ 1`, at or below `Open`'s name bound at a snapshot
record `a` of the history within its commit, is the unpurged read** (given `walCommitLe`). -/
theorem walReadFrom_eq {I : WalHist} {k : Nat} {a : w64} {σ σ' : StorContents}
    (hk0 : 0 < k) (hk : k ≤ walNameBound I (uint.nat a) false) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadFrom I k = some σ') : σ' = σ := by
  obtain ⟨b0, hkb0, hb0, hidx⟩ := walNameBound_witness hk0 hk hmax
  -- the records before `b0`: every snapshot record below `a`
  have hsnap0 : ∀ m, WalOpG.snap m ∈ I.take b0 → uint.nat m.Index' + 1 ≤ uint.nat a := by
    intro m hm
    have := walMaxSnap_mem _ 0 m hm
    rw [walLastIdx_eq] at hidx
    omega
  have htake : I.take b0 = I.take k ++ (I.drop k).take (b0 - k) := by
    rw [← List.take_add]; congr 1; omega
  have hsnapk : ∀ m, WalOpG.snap m ∈ I.take k → uint.nat m.Index' + 1 ≤ uint.nat a :=
    fun m hm => hsnap0 m (by rw [htake]; exact List.mem_append_left _ hm)
  unfold walReadFrom at h'
  simp only at h'
  split at h'
  · cases h'
  · next mN hN =>
    -- the full read: the purged prefix's fold, then the rest's
    unfold walRead at h
    have hsplit : I.filter (walKeep (uint.nat (walLastHS I).Commit')) =
        (I.take k).filter (walKeep (uint.nat (walLastHS I).Commit')) ++
          (I.drop k).filter (walKeep (uint.nat (walLastHS I).Commit')) := by
      rw [← List.filter_append, List.take_append_drop]
    have hcl0 := hcl
    unfold walCommitLe at hcl0
    rw [hsplit] at h hcl0
    rw [walFoldChkFrom_append, Option.bind_eq_some_iff] at h
    obtain ⟨σ₀, h0, h⟩ := h
    have hsnapR := walNewest_max hN
    obtain ⟨mR, hmR, hmRi⟩ := walNewest_mem hN
    -- `a ≤ M`: the record of index `a` is past `b0`
    have haM : uint.nat a ≤ uint.nat mN.Index' := by
      obtain ⟨i, ma, hi, hma⟩ := ha
      have hib : b0 ≤ i := by
        rcases Nat.lt_or_ge i b0 with hlt | hge
        · have := hsnap0 ma (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi))
          rw [hma] at this; omega
        · exact hge
      rw [← hma]
      apply hsnapR ma
      apply List.mem_filter.2
      refine ⟨List.mem_of_getElem? (i := i - k) ?_, ?_⟩
      · rw [List.getElem?_drop]; rw [show k + (i - k) = i by omega]; exact hi
      · simp only [walKeep, decide_eq_true_eq, hma]; exact hac
    -- the unpurged prefix's base is below `a`
    have hb0 : σ₀.b + 1 ≤ uint.nat a := by
      have := walFoldChkFrom_b_le (B := uint.nat a - 1)
        (fun m hm => by have := hsnapk m (List.mem_filter.1 hm).1; omega)
        (by simp [walFresh, StorContents.b]) h0
      have : 1 ≤ uint.nat a := by omega
      omega
    -- the hard states agree
    have hhs : walLastHS (I.take k) = σ₀.hs := by
      rw [walFoldChkFrom_hs h0, walHsStep_filter, walLastHS_eq]; rfl
    refine walFoldChk_sim (uint.nat mN.Index') _ σ₀ _ σ σ' hsnapR ⟨mR, hmR, by rw [hmRi]⟩
      hhs rfl (by omega) ?_ (walCommitLeFrom_append hcl0 h0) h h'
    -- the starting state: synced, or a `Save` with entries ahead
    by_cases hne : ∃ hs es, WalOpG.save hs es ∈ (I.drop k).take (b0 - k) ∧ es ≠ []
    · right; right
      refine ⟨rfl, ?_⟩
      obtain ⟨hs, es, hmem, hes⟩ := hne
      have hdrop : I.drop k = (I.drop k).take (b0 - k) ++ I.drop b0 := by
        conv => lhs; rw [← List.take_append_drop (b0 - k) (I.drop k)]
        rw [List.drop_drop]; congr 2; omega
      have hmemF : WalOpG.save hs es ∈ ((I.drop k).take (b0 - k)).filter
          (walKeep (uint.nat (walLastHS I).Commit')) := List.mem_filter.2 ⟨hmem, rfl⟩
      obtain ⟨A, B, hAB⟩ := List.append_of_mem hmemF
      refine ⟨A, hs, es, B ++ (I.drop b0).filter (walKeep (uint.nat (walLastHS I).Commit')), ?_, hes, ?_⟩
      · rw [hdrop, List.filter_append, hAB]; simp
      · intro m hm
        have hmX : WalOpG.snap m ∈ (I.drop k).take (b0 - k) := by
          have : WalOpG.snap m ∈ ((I.drop k).take (b0 - k)).filter
              (walKeep (uint.nat (walLastHS I).Commit')) := by rw [hAB]; exact List.mem_append_left _ hm
          exact (List.mem_filter.1 this).1
        have := hsnap0 m (by rw [htake]; exact List.mem_append_right _ hmX)
        omega
    · left
      have hnoNE : ∀ hs es, WalOpG.save hs es ∈ (I.drop k).take (b0 - k) → es = [] := by
        intro hs es hm
        exact Classical.byContradiction fun hes => hne ⟨hs, es, hm, hes⟩
      have hidxk : walLastIdx (I.take k) + 1 ≤ uint.nat a := by
        rw [htake, walLastIdx_eq, List.foldl_append, List.foldl_append,
          walLastEnt_noNE _ _ hnoNE] at hidx
        rw [walLastIdx_eq]
        have := walMaxSnap_ge ((I.drop k).take (b0 - k)) ((I.take k).foldl walMaxSnapF 0)
        omega
      have hlast := (walFoldChkFrom_last (x := 0) (y := 0)
        (by simp [walFresh, StorContents.b]) (by simp [walFresh, StorContents.last, StorContents.b]) h0).2
      have hle := walLastIdx_filter_le (uint.nat (walLastHS I).Commit') (I.take k)
      rw [← walLastIdx_eq] at hlast
      show [] = σ₀.ents.drop (uint.nat mN.Index' - σ₀.b)
      symm; apply List.drop_eq_nil_of_le
      simp only [StorContents.last] at hlast
      omega

/-- **C2: the purged read is a compaction of the unpurged read** (here, the read itself). -/
theorem walReadFrom_compacts {I : WalHist} {k : Nat} {a : w64} {σ σ' : StorContents}
    (hk0 : 0 < k) (hk : k ≤ walNameBound I (uint.nat a) false) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadFrom I k = some σ') : StorCompacts σ σ' := by
  rw [walReadFrom_eq hk0 hk hmax ha hac hcl h h']
  exact walRead_compacts_self h

/-- **C3/C4: the read from any `k` at or below the name bound is the unpurged read.** -/
theorem walReadCut_eq {I : WalHist} {k : Nat} {a : w64} {σ σ' : StorContents}
    (hk : k ≤ walNameBound I (uint.nat a) false) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadCut I k = some σ') : σ' = σ := by
  by_cases hk0 : k = 0
  · subst hk0; rw [walReadCut_zero, h] at h'; exact (Option.some.inj h').symm
  · rw [walReadCut_pos hk0] at h'
    exact walReadFrom_eq (by omega) hk hmax ha hac hcl h h'

/-- **C3: `walReadCut_compacts`.** -/
theorem walReadCut_compacts {I : WalHist} {k : Nat} {a : w64} {σ σ' : StorContents}
    (hk : k ≤ walNameBound I (uint.nat a) false) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadCut I k = some σ') : StorCompacts σ σ' := by
  rw [walReadCut_eq hk hmax ha hac hcl h h']
  exact walRead_compacts_self h

/-- **C4 (the identity instance): the relaxed read at a purge bound `p` at or below the name bound is
the unpurged read.** No `walNoDormant` premise: the name bound leaves no dormant record in the purged
prefix. -/
theorem walReadR_eq {I : WalHist} {p : Nat} {a : w64} {σ σ' : StorContents}
    (hp : p ≤ walNameBound I (uint.nat a) false) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadR I p σ') : σ' = σ := by
  obtain ⟨k, hk, h'⟩ := h'
  exact walReadCut_eq (Nat.le_trans hk hp) hmax ha hac hcl h h'

/-- **C3: `walReadR_compacts`.** -/
theorem walReadR_compacts {I : WalHist} {p : Nat} {a : w64} {σ σ' : StorContents}
    (hp : p ≤ walNameBound I (uint.nat a) false) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadR I p σ') : StorCompacts σ σ' := by
  rw [walReadR_eq hp hmax ha hac hcl h h']
  exact walRead_compacts_self h

/-- C4 at `Open`'s position (`walOpenPos`, W4a.2). -/
theorem walReadR_eq_openPos {I : WalHist} {p : Nat} {a : w64} {σ σ' : StorContents}
    (hp : p ≤ walOpenPos I a) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadR I p σ') : σ' = σ :=
  walReadR_eq (Nat.le_trans hp (Nat.min_le_right _ _)) hmax ha hac hcl h h'

/-- C4 at `ReleaseLockTo`'s position (`walReleasePos`, W4a.2). -/
theorem walReadR_eq_releasePos {I : WalHist} {p : Nat} {a : w64} {σ σ' : StorContents}
    (hp : p ≤ walReleasePos I a) (hmax : ¬ walHasMaxIdx I)
    (ha : ∃ (i : Nat) (m : SnapshotMetadataM), I[i]? = some (WalOpG.snap m) ∧ m.Index' = a)
    (hac : uint.nat a ≤ uint.nat (walLastHS I).Commit') (hcl : walCommitLe I)
    (h : walRead I = some σ) (h' : walReadR I p σ') : σ' = σ :=
  walReadR_eq_openPos (Nat.le_trans hp (walReleasePos_le_openPos I a)) hmax ha hac hcl h h'

end reader

end EtcdGrove
end Perennial
