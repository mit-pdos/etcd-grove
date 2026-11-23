/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Recover.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The recovery's mechanics: what each rule of `recoverSync` keeps and appends (rule 1's class-0
entries, rule 2's, the closure's completeness and termination within its fuel, rules 3b and 4's
appended dependencies and their dichotomies).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Seq

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

theorem Kept.get_isSome_iff (k : Kept) (y : CmdId) : (k.get y).isSome ↔ y ∈ k.map Prod.fst := by
  unfold Kept.get
  simp only [Option.isSome_map, List.find?_isSome, List.mem_map, beq_iff_eq]

theorem Kept.mem_keys_set (k : Kept) (x y : CmdId) (e : RecEntry) :
    y ∈ (k.set x e).map Prod.fst ↔ y = x ∨ y ∈ k.map Prod.fst := by
  rw [← Kept.get_isSome_iff, ← Kept.get_isSome_iff, Kept.get_set]
  by_cases h : y = x <;> simp [h]

theorem Kept.keys_set_nodup (k : Kept) (x : CmdId) (e : RecEntry) (h : (k.map Prod.fst).Nodup) :
    ((k.set x e).map Prod.fst).Nodup := by
  unfold Kept.set
  split
  · rw [List.map_map]
    have : (Prod.fst ∘ fun p : CmdId × RecEntry => if p.1 == x then (x, e) else p) = Prod.fst := by
      funext p; by_cases hp : p.1 = x <;> simp [hp]
    rw [this]; exact h
  · rename_i hx
    rw [List.map_append, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb; simp at hb; subst hb
    intro hab; subst hab
    apply hx
    rw [List.find?_isSome]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact ⟨p, hp, by simp⟩

theorem Kept.get_some_mem (k : Kept) (y : CmdId) (e : RecEntry) (h : k.get y = some e) :
    y ∈ k.map Prod.fst := by
  rw [← Kept.get_isSome_iff, h]; rfl

/-! ## Rule 1 -/

/-- `y` has an entry rule 1 keeps. -/
def K0ok (oldL : Nat) (U : List (Nat × Report)) (y : CmdId) : Prop :=
  ∃ a ∈ U, ∃ e ∈ a.2.entries, e.id = y ∧ okPhase oldL a e = true

/-- An entry of rule 1's kind. -/
def K0entry (oldL : Nat) (U : List (Nat × Report)) (y : CmdId) (re : RecEntry) : Prop :=
  re.cls = 0 ∧ ∃ a ∈ U, ∃ e ∈ a.2.entries, e.id = y ∧ okPhase oldL a e = true ∧
    re.cmd = e.cmd ∧ re.dep = e.dep

/-- The kept list's facts every rule maintains: unique keys. -/
def KeysOk (k : Kept) : Prop := (k.map Prod.fst).Nodup

theorem rule1_inner (oldL : Nat) (U : List (Nat × Report)) (a : Nat × Report) (ha : a ∈ U) :
    ∀ (es : List RepEntry) (k : Kept), (∀ e ∈ es, e ∈ a.2.entries) → KeysOk k →
      (∀ y re, k.get y = some re → K0entry oldL U y re) →
      let k' := es.foldl (fun k e =>
        if !okPhase oldL a e then k else
        match k.get e.id with
        | some old => if old.phase != 3 && e.phase.toNat == 3 then k.set e.id ⟨3, e.cmd, e.dep, 0⟩
            else k
        | none => k.set e.id ⟨e.phase.toNat, e.cmd, e.dep, 0⟩) k
      KeysOk k' ∧ (∀ y re, k'.get y = some re → K0entry oldL U y re) ∧
      (∀ y, (k'.get y).isSome ↔ ((k.get y).isSome ∨ ∃ e ∈ es, e.id = y ∧ okPhase oldL a e = true)) := by
  intro es
  induction es with
  | nil => intro k _ hk h; exact ⟨hk, h, by simp⟩
  | cons e es ih =>
    intro k hes hk h
    simp only [List.foldl_cons]
    have he : e ∈ a.2.entries := hes e (by simp)
    have hes' : ∀ e ∈ es, e ∈ a.2.entries := fun e' h' => hes e' (by simp [h'])
    -- one step
    have step : ∀ (k1 : Kept), k1 = (if !okPhase oldL a e then k else
        match k.get e.id with
        | some old => if old.phase != 3 && e.phase.toNat == 3 then k.set e.id ⟨3, e.cmd, e.dep, 0⟩
            else k
        | none => k.set e.id ⟨e.phase.toNat, e.cmd, e.dep, 0⟩) →
        KeysOk k1 ∧ (∀ y re, k1.get y = some re → K0entry oldL U y re) ∧
        (∀ y, (k1.get y).isSome ↔ ((k.get y).isSome ∨ (e.id = y ∧ okPhase oldL a e = true))) := by
      intro k1 hk1
      by_cases hok : okPhase oldL a e = true
      · have hset : ∀ re, re.cls = 0 → re.cmd = e.cmd → re.dep = e.dep →
            KeysOk (k.set e.id re) ∧ (∀ y re', (k.set e.id re).get y = some re' → K0entry oldL U y re') ∧
            (∀ y, ((k.set e.id re).get y).isSome ↔ ((k.get y).isSome ∨ (e.id = y ∧ okPhase oldL a e = true))) := by
          intro re h1 h2 h3
          refine ⟨Kept.keys_set_nodup _ _ _ hk, ?_, ?_⟩
          · intro y re' hy
            rw [Kept.get_set] at hy
            by_cases hye : y = e.id
            · rw [if_pos hye] at hy; cases hy
              exact ⟨h1, a, ha, e, he, hye.symm, hok, h2, h3⟩
            · rw [if_neg hye] at hy; exact h y re' hy
          · intro y; rw [Kept.get_set]
            by_cases hye : y = e.id
            · subst hye; simp [hok]
            · simp [hye, Ne.symm hye]
        rw [if_neg (by simp [hok])] at hk1
        cases hg : k.get e.id with
        | none => rw [hg] at hk1; simp only at hk1; subst hk1; exact hset _ rfl rfl rfl
        | some old =>
          rw [hg] at hk1; simp only at hk1
          split at hk1
          · subst hk1; exact hset _ rfl rfl rfl
          · subst hk1
            refine ⟨hk, h, ?_⟩
            intro y
            by_cases hye : e.id = y
            · subst hye; simp [hg]
            · simp [hye]
      · rw [if_pos (by simpa using hok)] at hk1
        subst hk1
        exact ⟨hk, h, by intro y; simp [hok]⟩
    obtain ⟨hk1, h1, h1'⟩ := step _ rfl
    obtain ⟨hk2, h2, h2'⟩ := ih _ hes' hk1 h1
    refine ⟨hk2, h2, ?_⟩
    intro y; rw [h2', h1']
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc, or_and_right, exists_or, exists_eq_left]

theorem rule1_spec (oldL : Nat) (U : List (Nat × Report)) :
    KeysOk (rule1 oldL U) ∧
    (∀ y re, (rule1 oldL U).get y = some re → K0entry oldL U y re) ∧
    (∀ y, ((rule1 oldL U).get y).isSome ↔ K0ok oldL U y) := by
  have outer : ∀ (us : List (Nat × Report)) (k : Kept), (∀ a ∈ us, a ∈ U) → KeysOk k →
      (∀ y re, k.get y = some re → K0entry oldL U y re) →
      let k' := us.foldl (fun k a => a.2.entries.foldl (fun k e =>
        if !okPhase oldL a e then k else
        match k.get e.id with
        | some old => if old.phase != 3 && e.phase.toNat == 3 then k.set e.id ⟨3, e.cmd, e.dep, 0⟩
            else k
        | none => k.set e.id ⟨e.phase.toNat, e.cmd, e.dep, 0⟩) k) k
      KeysOk k' ∧ (∀ y re, k'.get y = some re → K0entry oldL U y re) ∧
      (∀ y, (k'.get y).isSome ↔ ((k.get y).isSome ∨ K0ok oldL us y)) := by
    intro us
    induction us with
    | nil => intro k _ hk h; exact ⟨hk, h, by simp [K0ok]⟩
    | cons a us ih =>
      intro k has hk h
      simp only [List.foldl_cons]
      obtain ⟨hk1, h1, h1'⟩ := rule1_inner oldL U a (has a (by simp)) a.2.entries k (fun _ h => h) hk h
      obtain ⟨hk2, h2, h2'⟩ := ih _ (fun a' h' => has a' (by simp [h'])) hk1 h1
      refine ⟨hk2, h2, ?_⟩
      intro y; rw [h2', h1']
      unfold K0ok
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc, or_and_right, exists_or, exists_eq_left]
  obtain ⟨h1, h2, h3⟩ := outer U [] (fun _ h => h) (by simp [KeysOk]) (by intro y re h; simp [Kept.get] at h)
  refine ⟨h1, h2, ?_⟩
  intro y; exact (h3 y).trans (by simp [Kept.get])

/-! ## Rule 2 and the structure of the kept list after it -/

/-- An entry kept for the fast path or the closure: `R[0]`'s entry, for a command no class-0
entry has. -/
def NonK0entry (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool)
    (R : List (Nat × Report)) (y : CmdId) (re : RecEntry) : Prop :=
  re.cls ≠ 0 ∧ leaderInU = false ∧ ∃ r0 rs, R = r0 :: rs ∧ ∃ e ∈ r0.2.entries, e.id = y ∧
    re.cmd = e.cmd ∧ re.dep = e.dep ∧ ¬ K0ok oldL U y

/-- An entry the closure keeps when the old leader reported (D33): a dependency of a kept
command that no class-0 entry has (a proposal the old leader handled but did not pre-accept,
or a command it did not order), with some reporter's entry (`recPick`); its dependencies are
any of that entry's that are kept. -/
def OthEntry (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool)
    (acks : List (Nat × Report)) (y : CmdId) (re : RecEntry) : Prop :=
  re.cls ≠ 0 ∧ leaderInU = true ∧ ¬ K0ok oldL U y ∧
    ∃ a ∈ acks, ∃ e ∈ a.2.entries, e.id = y ∧ re.cmd = e.cmd

/-- The kept list's structure through rules 2 and 3. -/
def Struct (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool) (R : List (Nat × Report))
    (acks : List (Nat × Report)) (k : Kept) : Prop :=
  KeysOk k ∧ (∀ y re, k.get y = some re → K0entry oldL U y re ∨ NonK0entry oldL U leaderInU R y re ∨
    OthEntry oldL U leaderInU acks y re) ∧
  (∀ y, K0ok oldL U y → (k.get y).isSome)

theorem Struct_rule1 (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool)
    (R acks : List (Nat × Report)) : Struct oldL U leaderInU R acks (rule1 oldL U) := by
  obtain ⟨h1, h2, h3⟩ := rule1_spec oldL U
  exact ⟨h1, fun y re h => Or.inl (h2 y re h), fun y h => (h3 y).mpr h⟩

theorem rule2_spec (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool)
    (R acks : List (Nat × Report)) (k1 : Kept) (h1 : Struct oldL U leaderInU R acks k1) :
    let k2 := rule2 k1 leaderInU R
    Struct oldL U leaderInU R acks k2 ∧ (∀ y re, k1.get y = some re → k2.get y = some re) ∧
    (leaderInU = false → ∀ r0 rs, R = r0 :: rs → ∀ e ∈ r0.2.entries, e.phase.toNat = 1 →
      k1.get e.id = none →
      rs.all (fun a => a.2.entries.any (fun e' =>
        e'.id == e.id && e'.phase.toNat == 1 && depEq e.dep e'.dep)) = true →
      (k2.get e.id).isSome) := by
  intro k2
  unfold k2 rule2
  cases leaderInU
  · cases R with
    | nil => simp; exact h1
    | cons r0 rs =>
      simp only [Bool.false_eq_true, ite_false]
      -- the fold over r0's entries
      have gen : ∀ (es : List RepEntry) (k : Kept), (∀ e ∈ es, e ∈ r0.2.entries) →
          Struct oldL U false (r0 :: rs) acks k → (∀ y re, k1.get y = some re → k.get y = some re) →
          let k' := es.foldl (fun k e =>
            if e.phase.toNat != 1 || (k.get e.id).isSome then k
            else if rs.all (fun a => a.2.entries.any (fun e' =>
                e'.id == e.id && e'.phase.toNat == 1 && depEq e.dep e'.dep))
            then k.set e.id ⟨2, e.cmd, e.dep, 1⟩ else k) k
          Struct oldL U false (r0 :: rs) acks k' ∧ (∀ y re, k1.get y = some re → k'.get y = some re) ∧
          (∀ y, (k.get y).isSome → (k'.get y).isSome) ∧
          (∀ e ∈ es, e.phase.toNat = 1 → rs.all (fun a => a.2.entries.any (fun e' =>
            e'.id == e.id && e'.phase.toNat == 1 && depEq e.dep e'.dep)) = true →
            (k'.get e.id).isSome) := by
        intro es
        induction es with
        | nil => intro k _ hk hk1; exact ⟨hk, hk1, fun _ h => h, by simp⟩
        | cons e es ih =>
          intro k hes hk hk1
          simp only [List.foldl_cons]
          have he : e ∈ r0.2.entries := hes e (by simp)
          -- the step's result
          have hstep : ∃ k', k' = (if e.phase.toNat != 1 || (k.get e.id).isSome then k
              else if rs.all (fun a => a.2.entries.any (fun e' =>
                e'.id == e.id && e'.phase.toNat == 1 && depEq e.dep e'.dep))
              then k.set e.id ⟨2, e.cmd, e.dep, 1⟩ else k) ∧
              Struct oldL U false (r0 :: rs) acks k' ∧ (∀ y re, k1.get y = some re → k'.get y = some re) ∧
              (∀ y, (k.get y).isSome → (k'.get y).isSome) ∧
              (e.phase.toNat = 1 → rs.all (fun a => a.2.entries.any (fun e' =>
                e'.id == e.id && e'.phase.toNat == 1 && depEq e.dep e'.dep)) = true →
                (k'.get e.id).isSome) := by
            refine ⟨_, rfl, ?_⟩
            by_cases hc : (e.phase.toNat != 1 || (k.get e.id).isSome) = true
            · rw [if_pos hc]
              refine ⟨hk, hk1, fun _ h => h, ?_⟩
              intro hp _
              simp [hp] at hc; exact hc
            · rw [if_neg hc]
              have hnk : (k.get e.id).isSome = false := by simp at hc; simpa using hc.2
              split
              · rename_i hall
                have hnK0 : ¬ K0ok oldL U e.id := by
                  intro h; have := hk.2.2 _ h; rw [hnk] at this; simp at this
                refine ⟨⟨Kept.keys_set_nodup _ _ _ hk.1, ?_, ?_⟩, ?_, ?_, ?_⟩
                · intro y re hy
                  rw [Kept.get_set] at hy
                  by_cases hye : y = e.id
                  · rw [if_pos hye] at hy; cases hy
                    exact Or.inr (Or.inl ⟨by simp, rfl, r0, rs, rfl, e, he, hye.symm, rfl, rfl, hye ▸ hnK0⟩)
                  · rw [if_neg hye] at hy; exact hk.2.1 y re hy
                · intro y hy; rw [Kept.get_set]
                  by_cases hye : y = e.id
                  · simp [hye]
                  · simp [hye, hk.2.2 y hy]
                · intro y re hy; rw [Kept.get_set]
                  have := hk1 y re hy
                  by_cases hye : y = e.id
                  · subst hye; rw [this] at hnk; simp at hnk
                  · simp [hye, this]
                · intro y hy; rw [Kept.get_set]; by_cases hye : y = e.id <;> simp [hye, hy]
                · intro _ _; rw [Kept.get_set]; simp
              · rename_i hall
                refine ⟨hk, hk1, fun _ h => h, ?_⟩
                intro _ h; simp [h] at hall
          obtain ⟨k', hk', hs', hk1', hmono, hkeep⟩ := hstep
          rw [← hk']
          obtain ⟨a1, a2, a3, a4⟩ := ih k' (fun e' h' => hes e' (by simp [h'])) hs' hk1'
          refine ⟨a1, a2, fun y h => a3 y (hmono y h), ?_⟩
          intro e' he' hp hall
          simp at he'
          rcases he' with rfl | he'
          · exact a3 _ (hkeep hp hall)
          · exact a4 e' he' hp hall
      obtain ⟨a1, a2, -, a4⟩ := gen r0.2.entries k1 (fun _ h => h) h1
        (fun _ _ h => h)
      refine ⟨a1, a2, ?_⟩
      intro _ r0' rs' hR' e he hp _ hall
      simp at hR'; obtain ⟨rfl, rfl⟩ := hR'
      exact a4 e he hp hall
  · simp only [ite_true]
    refine ⟨h1, fun _ _ h => h, ?_⟩
    intro h; simp at h

/-! ## Rule 3: the closure -/

theorem exists_nodup_cover {α : Type} [DecidableEq α] (l : List α) :
    ∃ A : List α, A.Nodup ∧ (∀ x, x ∈ A ↔ x ∈ l) ∧ A.length ≤ l.length := by
  induction l with
  | nil => exact ⟨[], List.nodup_nil, by simp, Nat.le_refl _⟩
  | cons a l ih =>
    obtain ⟨A, h1, h2, h3⟩ := ih
    by_cases ha : a ∈ A
    · refine ⟨A, h1, ?_, by simp; omega⟩
      intro x; rw [h2 x, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact (h2 _).mp ha
        · exact h
    · refine ⟨a :: A, List.nodup_cons.mpr ⟨ha, h1⟩, ?_, by simp; omega⟩
      intro x; rw [List.mem_cons, List.mem_cons, h2]

/-- Rule 3's test of a dependency `d` of `c` in `k`: not `c`, and kept or with a `best` entry
(the dependencies the closure keeps in `c`'s list). -/
def keepP (best : CmdId → Option RecEntry) (c : CmdId) (k : Kept) (d : CmdId) : Bool :=
  d != c && ((k.get d).isSome || (best d).isSome)

/-- The inner fold of `closeStep` over dependencies `ds`: it keeps the new ones (`news`, those
with a `best` entry), in order, and its list is `ds` without `c` and without the dependencies
neither kept nor reported. -/
theorem closeInner (best : CmdId → Option RecEntry) (c : CmdId) :
    ∀ (ds : List CmdId) (k : Kept) (w l : List CmdId),
      let r := ds.foldl (closeDep best c) (k, w, l)
      r.2.2 = l ++ ds.filter (keepP best c k) ∧ ∃ news, r.2.1 = w ++ news ∧ news.Nodup ∧
        (∀ y ∈ news, k.get y = none ∧ y ∈ ds ∧ (best y).isSome) ∧
        (∀ y, r.1.get y = if y ∈ news then best y else k.get y) ∧
        (∀ d ∈ ds, keepP best c k d = true → (r.1.get d).isSome) ∧ (KeysOk k → KeysOk r.1) := by
  intro ds
  induction ds with
  | nil => intro k w l; exact ⟨by simp, [], by simp, List.nodup_nil, by simp, by simp, by simp, id⟩
  | cons d ds ih =>
    intro k w l
    simp only [List.foldl_cons]
    by_cases hdc : d = c
    · have hstep : closeDep best c (k, w, l) d = (k, w, l) := by unfold closeDep; simp [hdc]
      rw [hstep]
      obtain ⟨h1, news, h2, h3, h4, h5, h6, h7⟩ := ih k w l
      have hp : keepP best c k d = false := by unfold keepP; simp [hdc]
      refine ⟨by rw [h1, List.filter_cons, hp]; simp, news, h2, h3,
        fun y hy => ⟨(h4 y hy).1, by simp [(h4 y hy).2.1], (h4 y hy).2.2⟩, h5, ?_, h7⟩
      intro d' hd' hp'; simp at hd'; rcases hd' with rfl | hd'
      · rw [hp] at hp'; simp at hp'
      · exact h6 d' hd' hp'
    · by_cases hk : (k.get d).isSome = true
      · have hstep : closeDep best c (k, w, l) d = (k, w, l ++ [d]) := by
          unfold closeDep; simp [hdc, hk]
        rw [hstep]
        obtain ⟨h1, news, h2, h3, h4, h5, h6, h7⟩ := ih k w (l ++ [d])
        have hp : keepP best c k d = true := by unfold keepP; simp [hdc, hk]
        refine ⟨by rw [h1, List.filter_cons, hp]; simp, news, h2, h3,
          fun y hy => ⟨(h4 y hy).1, by simp [(h4 y hy).2.1], (h4 y hy).2.2⟩, h5, ?_, h7⟩
        intro d' hd' hp'; simp at hd'; rcases hd' with rfl | hd'
        · rw [h5]
          have : d' ∉ news := fun h => by have := (h4 d' h).1; rw [this] at hk; simp at hk
          simp [this, hk]
        · exact h6 d' hd' hp'
      · have hkn : k.get d = none := by simpa using hk
        cases hb : best d with
        | none =>
          have hstep : closeDep best c (k, w, l) d = (k, w, l) := by
            unfold closeDep; simp [hdc, hkn, hb]
          rw [hstep]
          obtain ⟨h1, news, h2, h3, h4, h5, h6, h7⟩ := ih k w l
          have hp : keepP best c k d = false := by unfold keepP; simp [hkn, hb]
          refine ⟨by rw [h1, List.filter_cons, hp]; simp, news, h2, h3,
            fun y hy => ⟨(h4 y hy).1, by simp [(h4 y hy).2.1], (h4 y hy).2.2⟩, h5, ?_, h7⟩
          intro d' hd' hp'; simp at hd'; rcases hd' with rfl | hd'
          · rw [hp] at hp'; simp at hp'
          · exact h6 d' hd' hp'
        | some bd =>
          have hstep : closeDep best c (k, w, l) d = (k.set d bd, w ++ [d], l ++ [d]) := by
            unfold closeDep; simp [hdc, hkn, hb]
          rw [hstep]
          obtain ⟨h1, news, h2, h3, h4, h5, h6, h7⟩ := ih (k.set d bd) (w ++ [d]) (l ++ [d])
          have hp : keepP best c k d = true := by unfold keepP; simp [hdc, hb]
          have hcongr : ∀ d', keepP best c (k.set d bd) d' = keepP best c k d' := by
            intro d'; unfold keepP; rw [Kept.get_set]
            by_cases e : d' = d
            · subst e; simp [hb]
            · simp [e]
          have hfil : ds.filter (keepP best c (k.set d bd)) = ds.filter (keepP best c k) :=
            List.filter_congr (fun d' _ => hcongr d')
          have hdn : d ∉ news := by
            intro h; have := (h4 d h).1; rw [Kept.get_set] at this; simp at this
          refine ⟨by rw [h1, hfil, List.filter_cons, hp]; simp, d :: news, by rw [h2]; simp,
            List.nodup_cons.mpr ⟨hdn, h3⟩, ?_, ?_, ?_, fun hk0 => h7 (Kept.keys_set_nodup _ _ _ hk0)⟩
          · intro y hy; simp at hy; rcases hy with rfl | hy
            · exact ⟨hkn, by simp, by rw [hb]; rfl⟩
            · obtain ⟨a, b, c'⟩ := h4 y hy
              rw [Kept.get_set] at a
              by_cases e : y = d
              · subst e; simp at a
              · simp [e] at a; exact ⟨a, by simp [b], c'⟩
          · intro y; rw [h5, Kept.get_set]
            by_cases e : y = d
            · subst e; simp [hdn, hb]
            · by_cases hy : y ∈ news <;> simp [e, hy]
          · intro d' hd' hp'; simp at hd'; rcases hd' with rfl | hd'
            · rw [h5]; simp [hdn, Kept.get_set]
            · exact h6 d' hd' (by rw [hcongr]; exact hp')

/-- `closeStep` on a kept command `c`: its dependency list keeps those passing `keepP`, the
new ones get their `best` entries. -/
theorem closeStep_cons (best : CmdId → Option RecEntry) (k : Kept) (c : CmdId) (work : List CmdId)
    (e : RecEntry) (hc : k.get c = some e) :
    ∃ news, (closeStep best (k, c :: work)).2 = work ++ news ∧ news.Nodup ∧
      (∀ y ∈ news, k.get y = none ∧ y ∈ e.dep ∧ (best y).isSome) ∧
      (closeStep best (k, c :: work)).1.get c = some { e with dep := e.dep.filter (keepP best c k) } ∧
      (∀ y, y ≠ c → (closeStep best (k, c :: work)).1.get y = if y ∈ news then best y else k.get y) ∧
      (KeysOk k → KeysOk (closeStep best (k, c :: work)).1) ∧
      (∀ d ∈ e.dep.filter (keepP best c k), ((closeStep best (k, c :: work)).1.get d).isSome) := by
  obtain ⟨h1, news, h2, h3, h4, h5, h6, h7⟩ := closeInner best c e.dep k work []
  refine ⟨news, ?_, h3, h4, ?_, ?_, ?_, ?_⟩
  · unfold closeStep; simp only [hc]; exact h2
  · unfold closeStep; simp only [hc]; rw [Kept.get_set, h1]; simp
  · intro y hy
    unfold closeStep; simp only [hc]
    rw [Kept.get_set, if_neg hy, h5]
  · intro hk0; unfold closeStep; simp only [hc]; exact Kept.keys_set_nodup _ _ _ (h7 hk0)
  · intro d hd
    have hdc : d ≠ c := by
      have := (List.mem_filter.mp hd).2; unfold keepP at this; simp at this; exact this.1
    unfold closeStep; simp only [hc]; rw [Kept.get_set, if_neg hdc]
    exact h6 d (List.mem_filter.mp hd).1 (List.mem_filter.mp hd).2

/-- What the recovery's proof needs of the reports (derived from `PInv` in `Model.lean`):
class-0 entries depend on class-0 commands, or (when the old leader reported, D33) on commands
reported in `U`; `R[0]`'s other entries on commands it reports. -/
structure RecHyp (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool)
    (R : List (Nat × Report)) : Prop where
  k0 : ∀ a ∈ U, ∀ e ∈ a.2.entries, okPhase oldL a e = true →
    ∀ d ∈ e.dep, d ≠ e.id ∧ (K0ok oldL U d ∨
      (leaderInU = true ∧ ∃ a' ∈ U, ∃ e' ∈ a'.2.entries, e'.id = d))
  r0 : leaderInU = false → ∀ r0 rs, R = r0 :: rs → ∀ e ∈ r0.2.entries, ¬ K0ok oldL U e.id →
    ∀ d ∈ e.dep, d ≠ e.id ∧ (K0ok oldL U d ∨ ∃ e' ∈ r0.2.entries, e'.id = d)

/-- `recPick` from an initial value. -/
def recPickFrom (l : List (Nat × Report)) (d : CmdId) (b0 : Option RecEntry) : Option RecEntry :=
  l.foldl (fun (b : Option RecEntry) a =>
    a.2.entries.foldl (fun b e => if e.id != d then b else match b with
      | none => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
      | some b0 => if e.phase.toNat > b0.phase then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
          else some b0) b) b0

theorem recPick_eq (l : List (Nat × Report)) (d : CmdId) : recPick l d = recPickFrom l d none := rfl

theorem recPickFrom_cons (a : Nat × Report) (l : List (Nat × Report)) (d : CmdId) (b0 : Option RecEntry) :
    recPickFrom (a :: l) d b0 = recPickFrom l d (a.2.entries.foldl (fun b e => if e.id != d then b else match b with
      | none => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
      | some b0 => if e.phase.toNat > b0.phase then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
          else some b0) b0) := rfl

/-- `recPick`'s value: the initial one, or a reported entry of `d` (class 2). -/
theorem recPickFrom_some (l : List (Nat × Report)) (d : CmdId) :
    ∀ (b0 : Option RecEntry) (b : RecEntry), recPickFrom l d b0 = some b →
      b0 = some b ∨ ∃ a ∈ l, ∃ e ∈ a.2.entries, e.id = d ∧ b = ⟨e.phase.toNat, e.cmd, e.dep, 2⟩ := by
  induction l with
  | nil => intro b0 b h; exact Or.inl h
  | cons a l ih =>
    intro b0 b h
    rw [recPickFrom_cons] at h
    have inner : ∀ (es : List RepEntry) (b1 : Option RecEntry) (b : RecEntry),
        (es.foldl (fun b e => if e.id != d then b else match b with
          | none => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
          | some b0 => if e.phase.toNat > b0.phase then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
              else some b0) b1) = some b →
        b1 = some b ∨ ∃ e ∈ es, e.id = d ∧ b = ⟨e.phase.toNat, e.cmd, e.dep, 2⟩ := by
      intro es
      induction es with
      | nil => intro b1 b h; exact Or.inl h
      | cons e es ihe =>
        intro b1 b h
        simp only [List.foldl_cons] at h
        rcases ihe _ b h with h' | ⟨e', he', hid, hb⟩
        · by_cases hd : e.id = d
          · simp only [hd, bne_self_eq_false, Bool.false_eq_true, ite_false] at h'
            cases b1 with
            | none => exact Or.inr ⟨e, by simp, hd, (Option.some.inj h').symm⟩
            | some b0' =>
              simp only at h'
              split at h'
              · exact Or.inr ⟨e, by simp, hd, (Option.some.inj h').symm⟩
              · exact Or.inl h'
          · left; simpa [hd] using h'
        · exact Or.inr ⟨e', by simp [he'], hid, hb⟩
    rcases ih _ b h with h' | ⟨a', ha', h''⟩
    · rcases inner _ _ b h' with h'' | ⟨e, he, hid, hb⟩
      · exact Or.inl h''
      · exact Or.inr ⟨a, by simp, e, he, hid, hb⟩
    · exact Or.inr ⟨a', by simp [ha'], h''⟩

/-- `recPick` finds a reported command. -/
theorem recPickFrom_isSome (l : List (Nat × Report)) (d : CmdId) :
    ∀ (b0 : Option RecEntry), (b0.isSome ∨ ∃ a ∈ l, ∃ e ∈ a.2.entries, e.id = d) →
      (recPickFrom l d b0).isSome := by
  have inner : ∀ (es : List RepEntry) (b1 : Option RecEntry),
      (b1.isSome ∨ ∃ e ∈ es, e.id = d) →
      (es.foldl (fun b e => if e.id != d then b else match b with
        | none => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
        | some b0 => if e.phase.toNat > b0.phase then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
            else some b0) b1).isSome := by
    intro es
    induction es with
    | nil => intro b1 h; rcases h with h | ⟨e, he, -⟩; exact h; simp at he
    | cons e es ihe =>
      intro b1 h
      simp only [List.foldl_cons]
      apply ihe
      by_cases hd : e.id = d
      · left
        simp only [hd, bne_self_eq_false, Bool.false_eq_true, ite_false]
        cases b1 with
        | none => rfl
        | some b0' => simp only; split <;> rfl
      · simp only [hd, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
        rcases h with h | ⟨e', he', hid⟩
        · exact Or.inl h
        · simp at he'; rcases he' with rfl | he'
          · exact absurd hid hd
          · exact Or.inr ⟨e', he', hid⟩
  induction l with
  | nil => intro b0 h; rcases h with h | ⟨a, ha, -⟩; exact h; simp at ha
  | cons a l ih =>
    intro b0 h
    rw [recPickFrom_cons]
    by_cases hal : ∃ e ∈ a.2.entries, e.id = d
    · exact ih _ (Or.inl (inner _ _ (Or.inr hal)))
    · apply ih
      rcases h with h | ⟨a', ha', he⟩
      · exact Or.inl (inner _ _ (Or.inl h))
      · simp at ha'; rcases ha' with rfl | ha'
        · exact absurd he hal
        · exact Or.inr ⟨a', ha', he⟩

/-- When the old leader reported, `best` is a reported entry, of class 2. -/
theorem recBest_true {R U acks : List (Nat × Report)} {d : CmdId} {bd : RecEntry}
    (hUa : ∀ a ∈ U, a ∈ acks) (h : recBest true R U acks d = some bd) :
    ∃ a ∈ acks, ∃ e ∈ a.2.entries, e.id = d ∧ bd.cmd = e.cmd ∧ bd.cls = 2 := by
  unfold recBest at h
  have from_l : ∀ l, (∀ a ∈ l, a ∈ acks) → recPick l d = some bd →
      ∃ a ∈ acks, ∃ e ∈ a.2.entries, e.id = d ∧ bd.cmd = e.cmd ∧ bd.cls = 2 := by
    intro l hl hp
    rw [recPick_eq] at hp
    rcases recPickFrom_some l d none bd hp with h' | ⟨a, ha, e, he, hid, rfl⟩
    · simp at h'
    · exact ⟨a, hl a ha, e, he, hid, rfl, rfl⟩
  cases hU : recPick U d with
  | some b => rw [hU] at h; cases h; exact from_l U hUa hU
  | none => rw [hU] at h; exact from_l acks (fun _ h => h) h

theorem recBest_true_isSome {R U acks : List (Nat × Report)} {d : CmdId}
    (h : ∃ a ∈ U, ∃ e ∈ a.2.entries, e.id = d) : (recBest true R U acks d).isSome := by
  unfold recBest
  have := recPickFrom_isSome U d none (Or.inr h)
  rw [← recPick_eq] at this
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp this
  rw [hb]; rfl

theorem recBest_mem {leaderInU R U acks d bd} (hRU : ∀ a ∈ R, a ∈ U) (hUa : ∀ a ∈ U, a ∈ acks)
    (h : recBest leaderInU R U acks d = some bd) :
    ∃ a ∈ acks, ∃ e ∈ a.2.entries, e.id = d := by
  unfold recBest at h
  split at h
  · rename_i e he
    split at he
    · simp at he
    · split at he
      · simp at he
      · rename_i _ r0 rs
        have := List.mem_of_find?_eq_some he
        have hid := List.find?_some he
        simp at hid
        exact ⟨r0, hUa _ (hRU _ (by simp)), e, this, hid⟩
  · split at h
    · rename_i b hb
      rw [recPick_eq] at hb
      rcases recPickFrom_some U d none b hb with h' | ⟨a, ha, e, he, hid, -⟩
      · simp at h'
      · exact ⟨a, hUa a ha, e, he, hid⟩
    · rw [recPick_eq] at h
      rcases recPickFrom_some acks d none bd h with h' | ⟨a, ha, e, he, hid, -⟩
      · simp at h'
      · exact ⟨a, ha, e, he, hid⟩

/-- A class-0 or `R[0]`'s entry keeps all its dependencies in the closure (each kept, or with
a `best` entry). -/
theorem deps_pass {oldL U leaderInU R acks} (H : RecHyp oldL U leaderInU R) (k : Kept)
    (hk : Struct oldL U leaderInU R acks k) (c : CmdId) (re : RecEntry)
    (hkind : K0entry oldL U c re ∨ NonK0entry oldL U leaderInU R c re) :
    ∀ d ∈ re.dep, keepP (recBest leaderInU R U acks) c k d = true := by
  intro d hd
  unfold keepP
  rcases hkind with h | h
  · obtain ⟨-, a, ha, e, he, rfl, hok, -, hdep⟩ := h
    rw [hdep] at hd
    obtain ⟨h1, h2⟩ := H.k0 a ha e he hok d hd
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true]
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | ⟨hl, h2⟩
    · exact Or.inl (hk.2.2 d h2)
    · subst hl; exact Or.inr (recBest_true_isSome h2)
  · obtain ⟨hcls, hL, r0, rs, hR, e, he, rfl, -, hdep, hnK0⟩ := h
    rw [hdep] at hd
    obtain ⟨h1, h2⟩ := H.r0 hL r0 rs hR e he hnK0 d hd
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true]
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | ⟨e', he', hid⟩
    · exact Or.inl (hk.2.2 d h2)
    · right
      have hf : (r0.2.entries.find? (·.id == d)).isSome := by
        rw [List.find?_isSome]; exact ⟨e', he', by simp [hid]⟩
      obtain ⟨e'', he''⟩ := Option.isSome_iff_exists.mp hf
      unfold recBest; rw [hL, hR]; simp [he'']

/-- A dependency the closure newly keeps: `R[0]`'s entry, or (when the old leader reported)
a reported entry. -/
theorem news_ok {oldL U leaderInU R acks} (H : RecHyp oldL U leaderInU R) (hUa : ∀ a ∈ U, a ∈ acks)
    (k : Kept) (hk : Struct oldL U leaderInU R acks k) (c : CmdId) (re : RecEntry)
    (hc : k.get c = some re) (d : CmdId) (hd : d ∈ re.dep) (hnk : k.get d = none) (bd : RecEntry)
    (hbd : recBest leaderInU R U acks d = some bd) :
    NonK0entry oldL U leaderInU R d bd ∨ OthEntry oldL U leaderInU acks d bd := by
  have hnK0d : ¬ K0ok oldL U d := fun h => by have := hk.2.2 d h; rw [hnk] at this; simp at this
  have oth : leaderInU = true → OthEntry oldL U leaderInU acks d bd := by
    intro hl; subst hl
    obtain ⟨a, ha, e, he, hid, hcmd, hcls⟩ := recBest_true hUa hbd
    exact ⟨by rw [hcls]; simp, rfl, hnK0d, a, ha, e, he, hid, hcmd⟩
  rcases hk.2.1 c re hc with h | h | h
  · obtain ⟨-, a, ha, e, he, rfl, hok, -, hdep⟩ := h
    rw [hdep] at hd
    rcases (H.k0 a ha e he hok d hd).2 with h2 | ⟨hl, -⟩
    · exact absurd h2 hnK0d
    · exact Or.inr (oth hl)
  · obtain ⟨hcls, hL, r0, rs, hR, e, he, rfl, -, hdep, hnK0⟩ := h
    rw [hdep] at hd
    obtain ⟨h1, h2⟩ := H.r0 hL r0 rs hR e he hnK0 d hd
    rcases h2 with h2 | ⟨e', he', hid⟩
    · exact absurd h2 hnK0d
    · left
      have hf : (r0.2.entries.find? (·.id == d)).isSome := by
        rw [List.find?_isSome]; exact ⟨e', he', by simp [hid]⟩
      obtain ⟨e'', he''⟩ := Option.isSome_iff_exists.mp hf
      have hmem := List.mem_of_find?_eq_some he''
      have hid'' := List.find?_some he''
      simp at hid''
      have hb : recBest leaderInU R U acks d = some ⟨e''.phase.toNat, e''.cmd, e''.dep, 2⟩ := by
        unfold recBest; rw [hL, hR]; simp [he'']
      rw [hbd] at hb; cases hb
      exact ⟨by simp, hL, r0, rs, hR, e'', hmem, hid'', rfl, rfl, hnK0d⟩
  · exact Or.inr (oth h.2.1)

/-- The closure's invariant. -/
def CInv (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool) (R : List (Nat × Report))
    (acks : List (Nat × Report)) (k2 k : Kept) (work : List CmdId) : Prop :=
  Struct oldL U leaderInU R acks k ∧ work.Nodup ∧ (∀ c ∈ work, (k.get c).isSome) ∧
  (∀ c re, k.get c = some re → c ∉ work → ∀ d ∈ re.dep, (k.get d).isSome) ∧
  (∀ y, (k2.get y).isSome → (k.get y).isSome)

/-- The number of commands of `A` not kept. -/
def unkept (A : List CmdId) (k : Kept) : Nat := (A.filter (fun i => (k.get i).isNone)).length

theorem unkept_step (A : List CmdId) (k k' : Kept) (news : List CmdId) (hA : A.Nodup)
    (hnd : news.Nodup) (hsub : ∀ y ∈ news, y ∈ A) (hnew : ∀ y ∈ news, (k.get y).isNone ∧ (k'.get y).isSome)
    (hsame : ∀ y, y ∉ news → ((k'.get y).isSome ↔ (k.get y).isSome)) :
    unkept A k' + news.length = unkept A k := by
  have key : ∀ A : List CmdId, (A.filter (fun i => (k'.get i).isNone)).length +
      (A.filter (· ∈ news)).length = (A.filter (fun i => (k.get i).isNone)).length := by
    intro A
    induction A with
    | nil => simp
    | cons a A ih =>
      by_cases ha : a ∈ news
      · have := hnew a ha
        simp only [List.filter_cons, ha, decide_true, ite_true]
        have h1 : (k'.get a).isNone = false := by simpa using this.2
        rw [h1, this.1]; simp; omega
      · have := hsame a ha
        simp only [List.filter_cons, ha, decide_false]
        have : (k'.get a).isNone = (k.get a).isNone := by
          cases h1 : (k'.get a) <;> cases h2 : (k.get a) <;> simp_all
        rw [this]; split <;> simp <;> omega
  have hperm : (A.filter (· ∈ news)).length = news.length := by
    apply List.Perm.length_eq
    rw [List.perm_ext_iff_of_nodup (hA.filter _) hnd]
    intro y; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hsub y h, h⟩⟩
  unfold unkept; rw [← key A, hperm]

theorem closeStep_inv {oldL U leaderInU R acks} (H : RecHyp oldL U leaderInU R)
    (hRU : ∀ a ∈ R, a ∈ U) (hUa : ∀ a ∈ U, a ∈ acks)
    (A : List CmdId) (hA : A.Nodup) (hAcov : ∀ a ∈ acks, ∀ e ∈ a.2.entries, e.id ∈ A)
    (k2 k : Kept) (c : CmdId) (w : List CmdId) (h : CInv oldL U leaderInU R acks k2 k (c :: w)) :
    let st' := closeStep (recBest leaderInU R U acks) (k, c :: w)
    CInv oldL U leaderInU R acks k2 st'.1 st'.2 ∧
      st'.2.length + unkept A st'.1 + 1 = (c :: w).length + unkept A k := by
  intro st'
  obtain ⟨hs, hwn, hwk, hdone, hk2⟩ := h
  obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp (hwk c (by simp))
  obtain ⟨news, h2, h3, h4, hgc, h5, h6, h7⟩ := closeStep_cons (recBest leaderInU R U acks) k c w re hre
  have hcn : c ∉ news := fun hc => by have := (h4 c hc).1; rw [hre] at this; simp at this
  have hwn' := List.nodup_cons.mp hwn
  -- c's new entry is of its old kind
  have hkind' : K0entry oldL U c { re with dep := re.dep.filter (keepP (recBest leaderInU R U acks) c k) } ∨
      NonK0entry oldL U leaderInU R c { re with dep := re.dep.filter (keepP (recBest leaderInU R U acks) c k) } ∨
      OthEntry oldL U leaderInU acks c { re with dep := re.dep.filter (keepP (recBest leaderInU R U acks) c k) } := by
    have hsame : (K0entry oldL U c re ∨ NonK0entry oldL U leaderInU R c re) →
        { re with dep := re.dep.filter (keepP (recBest leaderInU R U acks) c k) } = re := by
      intro hk'
      rw [List.filter_eq_self.mpr (deps_pass H k hs c re hk')]
    rcases hs.2.1 c re hre with h | h | h
    · rw [hsame (Or.inl h)]; exact Or.inl h
    · rw [hsame (Or.inr h)]; exact Or.inr (Or.inl h)
    · obtain ⟨a1, a2, a3, a4⟩ := h; exact Or.inr (Or.inr ⟨a1, a2, a3, a4⟩)
  have hnewK : ∀ y ∈ news, ∃ bd, recBest leaderInU R U acks y = some bd ∧
      (NonK0entry oldL U leaderInU R y bd ∨ OthEntry oldL U leaderInU acks y bd) := by
    intro y hy
    obtain ⟨a, b, hb⟩ := h4 y hy
    obtain ⟨bd, hbd⟩ := Option.isSome_iff_exists.mp hb
    exact ⟨bd, hbd, news_ok H hUa k hs c re hre y b a bd hbd⟩
  -- what was kept stays kept
  have hmono : ∀ y, (k.get y).isSome → (st'.1.get y).isSome := by
    intro y hy
    by_cases hyc : y = c
    · subst hyc; show ((closeStep _ _).1.get y).isSome; rw [hgc]; rfl
    · have : y ∉ news := fun hn => by have := (h4 y hn).1; simp_all
      show ((closeStep _ _).1.get y).isSome; rw [h5 y hyc, if_neg this]; exact hy
  refine ⟨⟨⟨h6 hs.1, ?_, ?_⟩, ?_, ?_, ?_, fun y hy => hmono y (hk2 y hy)⟩, ?_⟩
  · intro y r hy
    by_cases hyc : y = c
    · subst hyc
      have : st'.1.get y = _ := hgc
      rw [this] at hy; cases hy; exact hkind'
    · have := h5 y hyc
      change st'.1.get y = _ at this
      rw [this] at hy
      by_cases hyn : y ∈ news
      · rw [if_pos hyn] at hy
        obtain ⟨bd, hbd, hnk⟩ := hnewK y hyn
        rw [hbd] at hy; cases hy; exact Or.inr hnk
      · rw [if_neg hyn] at hy; exact hs.2.1 y r hy
  · intro y hy; exact hmono y (hs.2.2 y hy)
  · rw [h2, List.nodup_append]
    refine ⟨hwn'.2, h3, ?_⟩
    intro a ha b hb hab; subst hab
    have := (h4 a hb).1; have := hwk a (by simp [ha]); simp_all
  · intro y hy; rw [h2] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hmono y (hwk y (by simp [hy]))
    · have hyc : y ≠ c := fun e => hcn (e ▸ hy)
      show ((closeStep _ _).1.get y).isSome
      rw [h5 y hyc, if_pos hy]; exact (h4 y hy).2.2
  · intro y r hy hyw
    rw [h2] at hyw
    by_cases hyc : y = c
    · subst hyc
      have : st'.1.get y = _ := hgc
      rw [this] at hy; cases hy
      exact h7
    · have hyn : y ∉ news := fun hn => hyw (List.mem_append_right _ hn)
      have hyw' : y ∉ c :: w := by simp [hyc]; exact fun hn => hyw (List.mem_append_left _ hn)
      have := h5 y hyc
      change st'.1.get y = _ at this
      rw [this, if_neg hyn] at hy
      intro d hd
      exact hmono d (hdone y r hy hyw' d hd)
  · have hu := unkept_step A k st'.1 news hA h3
      (fun y hy => by
        obtain ⟨bd, hbd, -⟩ := hnewK y hy
        obtain ⟨a, ha, e, he, rfl⟩ := recBest_mem hRU hUa hbd
        exact hAcov a ha e he)
      (fun y hy => by
        have hyc : y ≠ c := fun e => hcn (e ▸ hy)
        refine ⟨by simpa using (h4 y hy).1, ?_⟩
        show ((closeStep _ _).1.get y).isSome; rw [h5 y hyc, if_pos hy]; exact (h4 y hy).2.2)
      (fun y hy => by
        by_cases hyc : y = c
        · subst hyc; show ((closeStep _ _).1.get y).isSome ↔ _; rw [hgc, hre]; rfl
        · show ((closeStep _ _).1.get y).isSome ↔ _; rw [h5 y hyc, if_neg hy])
    show st'.2.length + _ + 1 = _
    rw [h2]; simp; omega

theorem closure_spec {oldL U leaderInU R acks} (H : RecHyp oldL U leaderInU R)
    (hRU : ∀ a ∈ R, a ∈ U) (hUa : ∀ a ∈ U, a ∈ acks)
    (A : List CmdId) (hA : A.Nodup) (hAcov : ∀ a ∈ acks, ∀ e ∈ a.2.entries, e.id ∈ A)
    (k2 : Kept) (hs2 : Struct oldL U leaderInU R acks k2) (fuel : Nat)
    (hfuel : k2.length + A.length < fuel) :
    let k3 := closure (recBest leaderInU R U acks) fuel k2
    Struct oldL U leaderInU R acks k3 ∧ (∀ y, (k2.get y).isSome → (k3.get y).isSome) ∧
    (∀ c re, k3.get c = some re → ∀ d ∈ re.dep, (k3.get d).isSome) := by
  intro k3
  let w0 := sortIds (k2.map Prod.fst)
  have hw0p : w0.Perm (k2.map Prod.fst) := List.mergeSort_perm _ _
  let μ0 := w0.length + unkept A k2
  have hμ0 : μ0 < fuel := by
    have h1 : w0.length = k2.length := by rw [hw0p.length_eq]; simp
    have h2 : unkept A k2 ≤ A.length := List.length_filter_le _ _
    omega
  have hinit : CInv oldL U leaderInU R acks k2 k2 w0 := by
    refine ⟨hs2, hw0p.nodup_iff.mpr hs2.1, ?_, ?_, fun _ h => h⟩
    · intro c hc; rw [Kept.get_isSome_iff]; exact hw0p.mem_iff.mp hc
    · intro c re hc hcw; exfalso; apply hcw
      exact hw0p.mem_iff.mpr (Kept.get_some_mem _ _ _ hc)
  have key : ∀ n, CInv oldL U leaderInU R acks k2 (iter (closeStep (recBest leaderInU R U acks)) n (k2, w0)).1
      (iter (closeStep (recBest leaderInU R U acks)) n (k2, w0)).2 ∧ ((iter (closeStep (recBest leaderInU R U acks)) n (k2, w0)).2 = [] ∨
      (iter (closeStep (recBest leaderInU R U acks)) n (k2, w0)).2.length + unkept A (iter (closeStep (recBest leaderInU R U acks)) n (k2, w0)).1 + n = μ0) := by
    intro n
    induction n with
    | zero => exact ⟨hinit, Or.inr rfl⟩
    | succ n ih =>
      rw [iter_succ']
      obtain ⟨hI, hm⟩ := ih
      generalize hst : iter (closeStep (recBest leaderInU R U acks)) n (k2, w0) = st at hI hm
      obtain ⟨k, work⟩ := st
      cases work with
      | nil => exact ⟨hI, Or.inl rfl⟩
      | cons c w =>
        obtain ⟨h1, h2⟩ := closeStep_inv H hRU hUa A hA hAcov k2 k c w hI
        refine ⟨h1, ?_⟩
        rcases hm with hm | hm
        · simp at hm
        · right; simp only at hm; omega
  obtain ⟨hI, hm⟩ := key fuel
  have hdone : (iter (closeStep (recBest leaderInU R U acks)) fuel (k2, w0)).2 = [] := by
    rcases hm with hm | hm
    · exact hm
    · omega
  obtain ⟨hs, -, -, hfin, hk2⟩ := hI
  refine ⟨hs, hk2, ?_⟩
  intro c re hc
  exact hfin c re hc (by rw [hdone]; simp)

/-! ## Rules 3b and 4: dependencies appended -/

/-- `k'` is `k` with some dependencies appended (same commands, classes, commands). -/
def Mono (k k' : Kept) : Prop :=
  k'.map Prod.fst = k.map Prod.fst ∧ (∀ y, (k'.get y).isSome ↔ (k.get y).isSome) ∧
  ∀ y re, k.get y = some re → ∃ re', k'.get y = some re' ∧ re'.cls = re.cls ∧ re'.cmd = re.cmd ∧
    ∃ ex, re'.dep = re.dep ++ ex

theorem Mono.refl (k : Kept) : Mono k k :=
  ⟨rfl, fun _ => Iff.rfl, fun _ re h => ⟨re, h, rfl, rfl, [], by simp⟩⟩

theorem Mono.trans {k1 k2 k3 : Kept} (h1 : Mono k1 k2) (h2 : Mono k2 k3) : Mono k1 k3 := by
  refine ⟨h2.1.trans h1.1, fun y => (h2.2.1 y).trans (h1.2.1 y), ?_⟩
  intro y re h
  obtain ⟨re2, h2', c2, m2, ex2, d2⟩ := h1.2.2 y re h
  obtain ⟨re3, h3', c3, m3, ex3, d3⟩ := h2.2.2 y re2 h2'
  exact ⟨re3, h3', c3.trans c2, m3.trans m2, ex2 ++ ex3, by rw [d3, d2]; simp⟩

theorem Mono.set_append {k : Kept} {c : CmdId} {ec : RecEntry} (h : k.get c = some ec)
    (ws : List CmdId) : Mono k (k.set c { ec with dep := ec.dep ++ ws }) := by
  refine ⟨?_, fun y => ?_, fun y re hy => ?_⟩
  · have hx : (k.find? (·.1 == c)).isSome := by
      have := (Kept.get_isSome_iff k c).mp (by rw [h]; rfl)
      rw [List.find?_isSome]; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp this; exact ⟨p, hp, by simp⟩
    unfold Kept.set; rw [if_pos hx, List.map_map]
    congr 1; funext p; by_cases hp : p.1 = c <;> simp [hp]
  · rw [Kept.get_set]; by_cases e : y = c
    · subst e; simp [h]
    · simp [e]
  · rw [Kept.get_set]; by_cases e : y = c
    · subst e; rw [h] at hy; cases hy; exact ⟨{ ec with dep := ec.dep ++ ws }, by simp, rfl, rfl, ws, rfl⟩
    · simp only [e, ite_false]; exact ⟨re, hy, rfl, rfl, [], by simp⟩

/-- Reachability through the dependencies of kept commands. -/
def Reach (k : Kept) (a b : CmdId) : Prop := Relation.TransGen (fun y d => d ∈ kdeps k y) a b

theorem Mono.kdeps {k k' : Kept} (h : Mono k k') (y d : CmdId) (hd : d ∈ kdeps k y) :
    d ∈ kdeps k' y := by
  unfold sp.kdeps at *
  cases hy : k.get y with
  | none => rw [hy] at hd; simp at hd
  | some re =>
    rw [hy] at hd; simp at hd
    obtain ⟨re', h', -, -, ex, hdep⟩ := h.2.2 y re hy
    rw [h']; simp [hdep, hd]

theorem Mono.reach {k k' : Kept} (h : Mono k k') {a b : CmdId} (hr : Reach k a b) : Reach k' a b := by
  induction hr with
  | single hd => exact Relation.TransGen.single (h.kdeps _ _ hd)
  | tail _ hd ih => exact Relation.TransGen.tail ih (h.kdeps _ _ hd)

/-- The appended dependencies, described by `P`, from a base list `k0`. -/
def ExtP (P : CmdId → CmdId → Prop) (k0 k : Kept) : Prop :=
  Mono k0 k ∧ ∀ y re', k.get y = some re' → ∃ re, k0.get y = some re ∧
    ∃ ex, re'.dep = re.dep ++ ex ∧ ∀ w ∈ ex, P y w

theorem ExtP.refl (P : CmdId → CmdId → Prop) (k : Kept) : ExtP P k k :=
  ⟨Mono.refl k, fun _ re h => ⟨re, h, [], by simp, by simp⟩⟩

theorem ExtP.set_append {P : CmdId → CmdId → Prop} {k0 k : Kept} (h : ExtP P k0 k) {c : CmdId}
    {ec : RecEntry} (hc : k.get c = some ec) (ws : List CmdId) (hws : ∀ w ∈ ws, P c w) :
    ExtP P k0 (k.set c { ec with dep := ec.dep ++ ws }) := by
  refine ⟨h.1.trans (Mono.set_append hc ws), ?_⟩
  intro y re' hy
  rw [Kept.get_set] at hy
  by_cases e : y = c
  · subst e; simp at hy; subst hy
    obtain ⟨re, h0, ex, hd, hex⟩ := h.2 y ec hc
    refine ⟨re, h0, ex ++ ws, by simp [hd], ?_⟩
    intro w hw; simp at hw; rcases hw with hw | hw
    · exact hex w hw
    · exact hws w hw
  · simp only [e, ite_false] at hy; exact h.2 y re' hy

/-- A fold whose steps append dependencies: `Mono` from any intermediate list to the result,
and `ExtP` from the start. -/
theorem foldl_mono {α : Type} (f : Kept → α → Kept) (P : CmdId → CmdId → Prop) (k0 : Kept) (l : List α)
    (hf : ∀ k x, x ∈ l → ExtP P k0 k → ExtP P k0 (f k x) ∧ Mono k (f k x)) :
    ∀ k, ExtP P k0 k → ExtP P k0 (l.foldl f k) ∧ Mono k (l.foldl f k) := by
  induction l with
  | nil => intro k h; exact ⟨h, Mono.refl k⟩
  | cons x l ih =>
    intro k h
    obtain ⟨h1, h2⟩ := hf k x (by simp) h
    obtain ⟨h3, h4⟩ := ih (fun k' x' hx' => hf k' x' (by simp [hx'])) _ h1
    exact ⟨h3, h2.trans h4⟩

/-- ... and a property `Q x` established by the step on `x` and kept by `Mono` holds of every
element at the end. -/
theorem foldl_post {α : Type} (f : Kept → α → Kept) (P : CmdId → CmdId → Prop) (k0 : Kept) (l : List α)
    (Q : α → Kept → Prop) (hQ : ∀ x k k', Q x k → Mono k k' → Q x k')
    (hf : ∀ k x, x ∈ l → ExtP P k0 k → ExtP P k0 (f k x) ∧ Mono k (f k x) ∧ Q x (f k x)) :
    ∀ k, ExtP P k0 k → ∀ x ∈ l, Q x (l.foldl f k) := by
  induction l with
  | nil => intro k _ x hx; simp at hx
  | cons x l ih =>
    intro k h y hy
    obtain ⟨h1, h2, h3⟩ := hf k x (by simp) h
    have hm := foldl_mono f P k0 l (fun k' x' hx' hk' => let r := hf k' x' (by simp [hx']) hk'; ⟨r.1, r.2.1⟩) _ h1
    simp at hy
    rcases hy with rfl | hy
    · exact hQ _ _ _ h3 hm.2
    · exact ih (fun k' x' hx' => hf k' x' (by simp [hx'])) _ h1 y hy

theorem Mono.back {k k' : Kept} (h : Mono k k') {y : CmdId} {re' : RecEntry} (hy : k'.get y = some re') :
    ∃ re, k.get y = some re ∧ re'.cls = re.cls ∧ re'.cmd = re.cmd ∧ ∃ ex, re'.dep = re.dep ++ ex := by
  have : (k.get y).isSome := (h.2.1 y).mp (by rw [hy]; rfl)
  obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp this
  obtain ⟨re'', h'', c, m, ex, d⟩ := h.2.2 y re hre
  rw [hy] at h''; cases h''
  exact ⟨re, hre, c, m, ex, d⟩

/-- Rule 3b's appended dependency `w` of `c`. -/
def P3b (k3 : Kept) (r0 : Nat × Report) (c w : CmdId) : Prop :=
  (k3.get w).isSome ∧ (∃ re, k3.get c = some re ∧ re.cls ≠ 0) ∧ w ≠ c ∧
  (∃ pw pc, recPos r0 w = some pw ∧ recPos r0 c = some pc ∧ pw ≤ pc) ∧
  (∃ ew ec, k3.get w = some ew ∧ k3.get c = some ec ∧ Cmd.conflict ew.cmd ec.cmd = true)

theorem rule3bPair_step (k3 : Kept) (r0 : Nat × Report) (c : CmdId) (pc : Nat) (re : RecEntry)
    (hc : k3.get c = some re) (hc0 : re.cls ≠ 0) (hpc : recPos r0 c = some pc)
    (k : Kept) (w : CmdId) (h : ExtP (P3b k3 r0) k3 k) :
    let k' := rule3bPair r0 c pc k w
    ExtP (P3b k3 r0) k3 k' ∧ Mono k k' ∧
    (∀ ew ec pw, k3.get w = some ew → k3.get c = some ec → recPos r0 w = some pw → pw ≤ pc → w ≠ c →
      Cmd.conflict ew.cmd ec.cmd = true → Reach k' c w ∨ Reach k' w c) := by
  intro k'
  unfold k' rule3bPair
  cases hw : k.get w with
  | none =>
    simp only
    refine ⟨h, Mono.refl k, ?_⟩
    intro ew ec pw hw3 _ _ _ _ _
    obtain ⟨re', h', -⟩ := h.1.2.2 w ew hw3; rw [hw] at h'; simp at h'
  | some ew =>
    obtain ⟨ec', hc', hcc, hcm, -⟩ := h.1.2.2 c re hc
    rw [hc']
    obtain ⟨ew3, hw3, hwc, hwm, -⟩ := h.1.back hw
    cases hpw : recPos r0 w with
    | none =>
      simp only
      refine ⟨h, Mono.refl k, ?_⟩
      intro _ _ pw _ _ hpw' _ _ _; simp at hpw'
    | some pw =>
      simp only
      split
      · rename_i hcond
        refine ⟨h, Mono.refl k, ?_⟩
        intro ew' ec pw' hw' hc'' hpw' hle hne hconf
        rw [hw3] at hw'; cases hw'; rw [hc] at hc''; cases hc''; cases hpw'
        exfalso
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hcond
        rcases hcond with (hcond | hcond) | hcond
        · exact hne hcond
        · omega
        · rw [hwm, hcm] at hcond; rw [hcond] at hconf; simp at hconf
      · rename_i hcond
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', not_or] at hcond
        split
        · rename_i hc2
          refine ⟨h, Mono.refl k, ?_⟩
          intro _ _ _ _ _ _ _ _ _
          simp only [Bool.or_eq_true] at hc2
          rcases hc2 with hc2 | hc2
          · left; apply Relation.TransGen.single
            unfold kdeps; rw [hc']; simpa using hc2
          · right; exact recReaches_sound k w c hc2
        · have hP : P3b k3 r0 c w := by
            refine ⟨by rw [hw3]; rfl, ⟨re, hc, hc0⟩, hcond.1.1, ⟨pw, pc, hpw, hpc, by omega⟩, ⟨ew3, re, hw3, hc, ?_⟩⟩
            have := hcond.2; rw [hwm, hcm] at this; simpa using this
          refine ⟨h.set_append hc' [w] (by simpa using hP), Mono.set_append hc' [w], ?_⟩
          intro _ _ _ _ _ _ _ _ _
          left; apply Relation.TransGen.single
          unfold kdeps; simp [Kept.get_set]

/-- Rule 3b's dichotomy for a pair. -/
def D3b (k3 : Kept) (r0 : Nat × Report) (k : Kept) (c w : CmdId) : Prop :=
  ∀ ew ec pc pw, k3.get w = some ew → k3.get c = some ec → ec.cls ≠ 0 → recPos r0 c = some pc →
    recPos r0 w = some pw → pw ≤ pc → w ≠ c → Cmd.conflict ew.cmd ec.cmd = true →
    Reach k c w ∨ Reach k w c

theorem D3b.mono {k3 r0 k k' c w} (h : D3b k3 r0 k c w) (hm : Mono k k') : D3b k3 r0 k' c w := by
  intro ew ec pc pw a b c' d e f g i
  rcases h ew ec pc pw a b c' d e f g i with h | h
  · exact Or.inl (hm.reach h)
  · exact Or.inr (hm.reach h)

theorem rule3bCmd_step (k3 : Kept) (r0 : Nat × Report) (ids : List CmdId) (c : CmdId)
    (k : Kept) (h : ExtP (P3b k3 r0) k3 k) :
    let k' := rule3bCmd r0 ids k c
    ExtP (P3b k3 r0) k3 k' ∧ Mono k k' ∧ ∀ w ∈ ids, D3b k3 r0 k' c w := by
  intro k'
  unfold k' rule3bCmd
  cases hk : k.get c with
  | none =>
    refine ⟨h, Mono.refl k, ?_⟩
    intro w _ ew ec _ _ _ hc _ _ _ _ _ _
    obtain ⟨_, h', -⟩ := h.1.2.2 c ec hc; rw [hk] at h'; simp at h'
  | some ec =>
    cases hp : recPos r0 c with
    | none =>
      simp only
      refine ⟨h, Mono.refl k, ?_⟩
      intro w _ _ _ pc _ _ _ _ hpc; rw [hp] at hpc; simp at hpc
    | some pc =>
      simp only
      obtain ⟨re, hre, hcl, -⟩ := h.1.back hk
      split
      · rename_i h0
        refine ⟨h, Mono.refl k, ?_⟩
        intro w _ _ ec' _ _ _ hc3 hc0
        rw [hre] at hc3; cases hc3
        simp at h0; rw [hcl] at h0; exact absurd h0 hc0
      · rename_i h0
        have hc0 : re.cls ≠ 0 := by simp at h0; rw [← hcl]; exact h0
        have hstep := fun k w (_ : w ∈ ids) (hk : ExtP (P3b k3 r0) k3 k) =>
          rule3bPair_step k3 r0 c pc re hre hc0 hp k w hk
        have hm := foldl_mono (rule3bPair r0 c pc) (P3b k3 r0) k3 ids
          (fun k w hw hk => ⟨(hstep k w hw hk).1, (hstep k w hw hk).2.1⟩) k h
        refine ⟨hm.1, hm.2, ?_⟩
        have := foldl_post (rule3bPair r0 c pc) (P3b k3 r0) k3 ids
          (fun w k => D3b k3 r0 k c w) (fun w k k' hq hm => hq.mono hm)
          (fun k w hw hk => ⟨(hstep k w hw hk).1, (hstep k w hw hk).2.1, ?_⟩) k h
        · exact this
        · intro ew ec' pc' pw hw3 hc3 _ hpc' hpw hle hne hconf
          rw [hp] at hpc'; cases hpc'
          exact (hstep k w hw hk).2.2 ew ec' pw hw3 hc3 hpw hle hne hconf

theorem rule3b_spec (leaderInU : Bool) (R : List (Nat × Report)) (k3 : Kept) :
    (leaderInU = true ∨ R = [] → rule3b leaderInU R k3 = k3) ∧
    (leaderInU = false → ∀ r0 rs, R = r0 :: rs →
      ExtP (P3b k3 r0) k3 (rule3b leaderInU R k3) ∧ Mono k3 (rule3b leaderInU R k3) ∧
      ∀ c w, (k3.get c).isSome → D3b k3 r0 (rule3b leaderInU R k3) c w) := by
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · simp [rule3b, h]
    · subst h; cases leaderInU <;> simp [rule3b]
  · intro hL r0 rs hR
    subst hL; subst hR
    simp only [rule3b, Bool.false_eq_true, ite_false]
    let ids := sortIds (k3.map Prod.fst)
    have hst := fun k c (_ : c ∈ ids) (hk : ExtP (P3b k3 r0) k3 k) => rule3bCmd_step k3 r0 ids c k hk
    have hm := foldl_mono (rule3bCmd r0 ids) (P3b k3 r0) k3 ids
      (fun k c hc hk => ⟨(hst k c hc hk).1, (hst k c hc hk).2.1⟩) k3 (ExtP.refl _ _)
    refine ⟨hm.1, hm.2, ?_⟩
    have hpost := foldl_post (rule3bCmd r0 ids) (P3b k3 r0) k3 ids
      (fun c k => ∀ w ∈ ids, D3b k3 r0 k c w) (fun c k k' hq hm w hw => (hq w hw).mono hm)
      (fun k c hc hk => hst k c hc hk) k3 (ExtP.refl _ _)
    intro c w hc
    have hcid : c ∈ ids := (List.mergeSort_perm _ _).mem_iff.mpr ((Kept.get_isSome_iff _ _).mp hc)
    intro ew ec pc pw hw3 hc3 h0 hpc hpw hle hne hconf
    have hwid : w ∈ ids := (List.mergeSort_perm _ _).mem_iff.mpr
      ((Kept.get_isSome_iff _ _).mp (by rw [hw3]; rfl))
    exact hpost c hcid w hwid ew ec pc pw hw3 hc3 h0 hpc hpw hle hne hconf

/-- Rule 4's appended dependency `a` of `c`. -/
def P4 (k0 : Kept) (c a : CmdId) : Prop :=
  (∃ re, k0.get c = some re ∧ re.cls ≠ 0) ∧ (∃ ea, k0.get a = some ea ∧ ea.cls = 0) ∧
  (∃ ea ec, k0.get a = some ea ∧ k0.get c = some ec ∧ Cmd.conflict ea.cmd ec.cmd = true)

/-- Rule 4's dichotomy for a pair. -/
def D4 (k0 : Kept) (k : Kept) (c a : CmdId) : Prop :=
  ∀ ea ec, k0.get a = some ea → k0.get c = some ec → ec.cls ≠ 0 → ea.cls = 0 →
    Cmd.conflict ea.cmd ec.cmd = true → Reach k c a ∨ Reach k a c

theorem D4.mono {k0 k k' c a} (h : D4 k0 k c a) (hm : Mono k k') : D4 k0 k' c a := by
  intro ea ec h1 h2 h3 h4 h5
  rcases h ea ec h1 h2 h3 h4 h5 with h | h
  · exact Or.inl (hm.reach h)
  · exact Or.inr (hm.reach h)

theorem rule4Pair_step (k0 : Kept) (c : CmdId) (re : RecEntry) (hc : k0.get c = some re)
    (hc0 : re.cls ≠ 0) (k : Kept) (a : CmdId) (h : ExtP (P4 k0) k0 k) :
    let k' := rule4Pair c k a
    ExtP (P4 k0) k0 k' ∧ Mono k k' ∧ D4 k0 k' c a := by
  intro k'
  unfold k' rule4Pair
  obtain ⟨ec', hc', hcc, hcm, -⟩ := h.1.2.2 c re hc
  cases ha : k.get a with
  | none =>
    simp only
    refine ⟨h, Mono.refl k, ?_⟩
    intro ea _ ha0 _ _ _ _
    obtain ⟨_, h', -⟩ := h.1.2.2 a ea ha0; rw [ha] at h'; simp at h'
  | some ea =>
    rw [hc']; simp only
    obtain ⟨ea0, ha0, hac, ham, -⟩ := h.1.back ha
    split
    · rename_i hcond
      refine ⟨h, Mono.refl k, ?_⟩
      intro ea' ec ha0' hc0' _ hea0 hconf
      rw [ha0] at ha0'; cases ha0'; rw [hc] at hc0'; cases hc0'
      exfalso
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hcond
      rcases hcond with hcond | hcond
      · rw [hac] at hcond; exact hcond hea0
      · rw [ham, hcm] at hcond; rw [hcond] at hconf; simp at hconf
    · rename_i hcond
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or, Decidable.not_not] at hcond
      split
      · rename_i hr
        have hP : P4 k0 c a := by
          refine ⟨⟨re, hc, hc0⟩, ⟨ea0, ha0, by rw [← hac]; exact hcond.1⟩, ⟨ea0, re, ha0, hc, ?_⟩⟩
          have := hcond.2; rw [ham, hcm] at this; simpa using this
        refine ⟨h.set_append hc' [a] (by simpa using hP), Mono.set_append hc' [a], ?_⟩
        intro _ _ _ _ _ _ _
        left; apply Relation.TransGen.single
        unfold kdeps; simp [Kept.get_set]
      · rename_i hr
        refine ⟨h, Mono.refl k, ?_⟩
        intro _ _ _ _ _ _ _
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hr
        by_cases h1 : recReaches k c a = true
        · exact Or.inl (recReaches_sound k c a h1)
        · right; exact recReaches_sound k a c (hr (by simpa using h1))

theorem rule4Cmd_step (k0 : Kept) (ids : List CmdId) (c : CmdId) (k : Kept)
    (h : ExtP (P4 k0) k0 k) :
    let k' := rule4Cmd ids k c
    ExtP (P4 k0) k0 k' ∧ Mono k k' ∧ ∀ a ∈ ids, D4 k0 k' c a := by
  intro k'
  unfold k' rule4Cmd
  cases hk : k.get c with
  | none =>
    refine ⟨h, Mono.refl k, ?_⟩
    intro a _ ea ec _ hc _ _ _
    obtain ⟨_, h', -⟩ := h.1.2.2 c ec hc; rw [hk] at h'; simp at h'
  | some ec =>
    simp only
    obtain ⟨re, hre, hcl, -⟩ := h.1.back hk
    split
    · rename_i h0
      refine ⟨h, Mono.refl k, ?_⟩
      intro a _ _ ec' _ hc3 hc0
      rw [hre] at hc3; cases hc3
      simp at h0; rw [hcl] at h0; exact absurd h0 hc0
    · rename_i h0
      have hc0 : re.cls ≠ 0 := by simp at h0; rw [← hcl]; exact h0
      have hstep := fun k a (_ : a ∈ ids) (hk : ExtP (P4 k0) k0 k) =>
        rule4Pair_step k0 c re hre hc0 k a hk
      have hm := foldl_mono (rule4Pair c) (P4 k0) k0 ids
        (fun k a ha hk => ⟨(hstep k a ha hk).1, (hstep k a ha hk).2.1⟩) k h
      refine ⟨hm.1, hm.2, ?_⟩
      exact foldl_post (rule4Pair c) (P4 k0) k0 ids
        (fun a k => D4 k0 k c a) (fun a k k' hq hm => hq.mono hm)
        (fun k a ha hk => hstep k a ha hk) k h

theorem rule4_spec (ids : List CmdId) (k0 : Kept)
    (hids : ∀ c, (k0.get c).isSome → c ∈ ids) :
    ExtP (P4 k0) k0 (rule4 ids k0) ∧ Mono k0 (rule4 ids k0) ∧
      ∀ c a, (k0.get c).isSome → (k0.get a).isSome → D4 k0 (rule4 ids k0) c a := by
  have hst := fun k c (_ : c ∈ ids) (hk : ExtP (P4 k0) k0 k) => rule4Cmd_step k0 ids c k hk
  have hm := foldl_mono (rule4Cmd ids) (P4 k0) k0 ids
    (fun k c hc hk => ⟨(hst k c hc hk).1, (hst k c hc hk).2.1⟩) k0 (ExtP.refl _ _)
  refine ⟨hm.1, hm.2, ?_⟩
  have hpost := foldl_post (rule4Cmd ids) (P4 k0) k0 ids
    (fun c k => ∀ a ∈ ids, D4 k0 k c a) (fun c k k' hq hm a ha => (hq a ha).mono hm)
    (fun k c hc hk => hst k c hc hk) k0 (ExtP.refl _ _)
  intro c a hc ha
  exact hpost c (hids c hc) a (hids a ha)

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
