/-
**Lemmas over the WAL's history and its reader** (WAL W4b, 2026-11-12; `/shared/tmp/wal-spec/w4b/plan.md`
§2 A, approved by etcd-grove-81). Proved; no trusted text. For the tester's proof (W4c), rung 2's crash
clause (C3) and the server's restart (S2/C6).
DRAFT (unchecked): starting point for Part A.
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

end reader

end EtcdGrove
end Perennial
