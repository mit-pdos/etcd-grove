/-
The lessor's history (the lease-keys plan, Part B, 2026-10-31): when appending a snapshot keeps
the readers' invariant's facts (`setsOk`, `histOk`). Pure. Lean-first (no Rocq counterpart).

`setsOk_snoc` is the one step every writer (`Grant`, `Attach`, `Detach`, `Revoke`) takes under
`le.mu`'s write lock, with the conditions each discharges of its own snapshot: every lease of the
new snapshot is in the last one under the same id or in no snapshot yet, a lease of it has the
items the new item map attaches to its id, and a lease not in it keeps its set (or is new, with
the empty set).

The reader-side laws a client's `Main` uses (the lease-expiry plan's E3, 2026-11-05), from the
reader invariant's `histOnce`, `ttlTie` and (S2–S4) `reqOk`: `lessorAt_absent_stays`,
`leaseTTLAt_ge_req` (until S2–S4 `leaseTTLAt_ttl_agree`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open go_etcd_io.etcd.server.v3.lease

section hist
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

theorem getElem?_snoc_cases {α : Type} (hs : List α) (x y : α) (i : Nat)
    (h : (hs ++ [x])[i]? = some y) :
    (i < hs.length ∧ hs[i]? = some y) ∨ (i = hs.length ∧ y = x) := by
  rcases Nat.lt_or_ge i hs.length with hi | hi
  · left; exact ⟨hi, by rwa [List.getElem?_append_left hi] at h⟩
  · right
    rw [List.getElem?_append_right hi] at h
    rcases Nat.eq_or_lt_of_le hi with he | hlt
    · subst he; simp at h; exact ⟨rfl, h.symm⟩
    · have : [x][i - hs.length]? = none := List.getElem?_eq_none (by simp; omega)
      rw [this] at h; cases h

theorem getElem?_snoc_lt {α : Type} (hs : List α) (x : α) {i : Nat} (h : i < hs.length) :
    (hs ++ [x])[i]? = hs[i]? := List.getElem?_append_left h

theorem getElem?_snoc_len {α : Type} (hs : List α) (x : α) : (hs ++ [x])[hs.length]? = some x := by
  simp

/-- The last snapshot is the one at the last index. -/
theorem getLast?_getElem? {α : Type} {hs : List α} {σ : α} (h : hs.getLast? = some σ) :
    hs[hs.length - 1]? = some σ ∧ 0 < hs.length := by
  rw [List.getLast?_eq_getElem?] at h
  refine ⟨h, ?_⟩
  rcases hs with _ | ⟨_, _⟩
  · simp at h
  · simp

/-- **Appending a snapshot whose lease map keeps the last one's ids keeps the history monotone**
(the lease-grant plan's D2: `Grant`, `Attach`, `Detach`). -/
theorem histMono_snoc {hs : List LSnap} {τ σ' : LSnap} (hlast : hs.getLast? = some τ)
    (hsub : ∀ id : w64, (τ.1.lookup id).isSome → (σ'.1.lookup id).isSome)
    (h : histMono hs) : histMono (hs ++ [σ']) := by
  have ⟨hτ, hpos⟩ := getLast?_getElem? hlast
  intro i j σ ρ id hij hi hj hl
  rcases getElem?_snoc_cases hs σ' ρ j hj with ⟨hjl, hj'⟩ | ⟨hje, hρ⟩
  · have hil : i < hs.length := by omega
    rw [getElem?_snoc_lt hs σ' hil] at hi
    exact h i j σ ρ id hij hi hj' hl
  · rw [hρ]
    rcases getElem?_snoc_cases hs σ' σ i hi with ⟨hil, hi'⟩ | ⟨hie, hσ⟩
    · exact hsub id (h i (hs.length - 1) σ τ id (by omega) hi' hτ hl)
    · rw [← hσ]; exact hl

/-- A lease of the last snapshot is under one id there. -/
theorem oneId_last {hs : List LSnap} {σ : LSnap} (hone : oneIdPerLease hs)
    (hlast : hs.getLast? = some σ) {id id' : w64} {l : Loc} (h1 : σ.1.lookup id = some l)
    (h2 : σ.1.lookup id' = some l) : id = id' :=
  have hl := (getLast?_getElem? hlast).1
  hone _ _ σ σ id id' l hl hl h1 h2

/-- **Appending a snapshot keeps the readers' invariant's facts.** -/
theorem setsOk_snoc {hs : List LSnap} {Sm Sm' : GMap Loc (GMap LeaseItem Unit)} {σ σ' : LSnap}
    (hlast : hs.getLast? = some σ) (hok : setsOk hs Sm) (hh : histOk hs)
    (hsub : ∀ l, (Sm.lookup l).isSome → (Sm'.lookup l).isSome)
    (hcov : ∀ (id : w64) (l : Loc), σ'.1.lookup id = some l → (Sm'.lookup l).isSome)
    (hold : ∀ (id : w64) (l : Loc), σ'.1.lookup id = some l →
      σ.1.lookup id = some l ∨
        ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some l)
    (hinj : ∀ (id id' : w64) (l : Loc), σ'.1.lookup id = some l → σ'.1.lookup id' = some l →
      id = id')
    (hin : ∀ (id : w64) (l : Loc) (S : GMap LeaseItem Unit), σ'.1.lookup id = some l →
      Sm'.lookup l = some S → itemsFor σ'.2.1 id S)
    (hout : ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm'.lookup l = some S →
      (∀ id : w64, σ'.1.lookup id ≠ some l) →
      Sm.lookup l = some S ∨
        ((∀ (k : Nat) (τ : LSnap) (id : w64), hs[k]? = some τ → τ.1.lookup id ≠ some l) ∧ S = ∅))
    (hshort : itemKeysShort σ'.2.1) :
    setsOk (hs ++ [σ']) Sm' ∧ histOk (hs ++ [σ']) := by
  obtain ⟨hne, hone, hks⟩ := hh
  have ⟨hσ, hpos⟩ := getLast?_getElem? hlast
  -- a lease in no snapshot of `hs` and not in `σ'` is in no snapshot of `hs ++ [σ']`
  have never_snoc : ∀ l : Loc,
      (∀ (k : Nat) (τ : LSnap) (id : w64), hs[k]? = some τ → τ.1.lookup id ≠ some l) →
      (∀ id : w64, σ'.1.lookup id ≠ some l) →
      ∀ (k : Nat) (τ : LSnap) (id : w64), (hs ++ [σ'])[k]? = some τ → τ.1.lookup id ≠ some l := by
    intro l hn hn' k τ id hk
    rcases getElem?_snoc_cases hs σ' τ k hk with ⟨_, hk⟩ | ⟨_, rfl⟩
    · exact hn k τ id hk
    · exact hn' id
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- every lease of the history has a set
    intro k τ id l hk hl
    rcases getElem?_snoc_cases hs σ' τ k hk with ⟨_, hk⟩ | ⟨_, rfl⟩
    · exact hsub l (hok.1 k τ id l hk hl)
    · exact hcov id l hl
  · intro l S hS
    by_cases hin' : ∃ id, σ'.1.lookup id = some l
    · obtain ⟨id, hid⟩ := hin'
      right
      refine ⟨id, hs.length, σ', ⟨⟨σ', getElem?_snoc_len hs σ', hid⟩, ?_⟩,
        getElem?_snoc_len hs σ', hin id l S hid hS⟩
      intro j τ hj hτ
      have : (hs ++ [σ']).length ≤ j := by simp; omega
      rw [List.getElem?_eq_none this] at hτ; cases hτ
    · have hn' : ∀ id : w64, σ'.1.lookup id ≠ some l := fun id h => hin' ⟨id, h⟩
      rcases hout l S hS hn' with hS0 | ⟨hn, rfl⟩
      · rcases hok.2 l S hS0 with ⟨hn, rfl⟩ | ⟨id, i, τ, ⟨⟨τ', hi', hτ'⟩, hlat⟩, hi, hit⟩
        · left; exact ⟨never_snoc l hn hn', rfl⟩
        · right
          have hilt : i < hs.length := (List.getElem?_eq_some_iff.1 hi).1
          refine ⟨id, i, τ, ⟨⟨τ', by rw [getElem?_snoc_lt hs σ' hilt]; exact hi', hτ'⟩, ?_⟩,
            by rw [getElem?_snoc_lt hs σ' hilt]; exact hi, hit⟩
          intro j υ hij hj
          rcases getElem?_snoc_cases hs σ' υ j hj with ⟨_, hj⟩ | ⟨_, rfl⟩
          · exact hlat j υ hij hj
          · exact hn' id
      · left; exact ⟨never_snoc l hn hn', rfl⟩
  · simp
  · -- one id per lease
    intro i j τ υ id id' l hi hj hl hl'
    rcases getElem?_snoc_cases hs σ' τ i hi with ⟨_, hi⟩ | ⟨_, hτ⟩ <;>
      rcases getElem?_snoc_cases hs σ' υ j hj with ⟨_, hj⟩ | ⟨_, hυ⟩
    · exact hone i j τ υ id id' l hi hj hl hl'
    · rw [hυ] at hl'
      rcases hold id' l hl' with h | h
      · exact hone i _ τ σ id id' l hi hσ hl h
      · exact absurd hl (h i τ id hi)
    · rw [hτ] at hl
      rcases hold id l hl with h | h
      · exact hone _ j σ υ id id' l hσ hj h hl'
      · exact absurd hl' (h j υ id' hj)
    · rw [hτ] at hl; rw [hυ] at hl'
      exact hinj id id' l hl hl'
  · intro τ hτ
    rcases List.mem_append.1 hτ with h | h
    · exact hks τ h
    · rw [List.mem_singleton] at h; subst h; exact hshort

/-- **`Grant`'s snapshot**: the lease map gains the lease `l` of `id`, `l` in no snapshot before
(registered with the empty set) and `id` with no item. -/
theorem setsOk_grant {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {M : GMap w64 Loc}
    {I : GMap LeaseItem w64} {T T' : GMap w64 w64} {id : w64} {l : Loc}
    (hlast : hs.getLast? = some (M, I, T)) (hok : setsOk hs Sm) (hh : histOk hs)
    (hM : M.lookup id = none) (hI : ∀ it : LeaseItem, I.lookup it ≠ some id)
    (hnew : ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some l) :
    setsOk (hs ++ [(M.insert id l, I, T')]) (Sm.insert l ∅) ∧ histOk (hs ++ [(M.insert id l, I, T')]) := by
  have ⟨hσ, hpos⟩ := getLast?_getElem? hlast
  have hlM : ∀ x : w64, M.lookup x ≠ some l := fun x h => hnew _ _ x hσ h
  have hins : ∀ (x : w64) (l' : Loc), (M.insert id l).lookup x = some l' →
      (x = id ∧ l' = l) ∨ (x ≠ id ∧ M.lookup x = some l') := by
    intro x l' h
    rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · rename_i hx; cases h; left; exact ⟨hx.symm, rfl⟩
    · rename_i hx; right; exact ⟨Ne.symm hx, h⟩
  have hSm : ∀ l' : Loc, (Sm.insert l ∅).lookup l' = if l = l' then some ∅ else Sm.lookup l' :=
    fun l' => GMap.lookup_insert_eq_iff Sm l l' ∅
  apply setsOk_snoc hlast hok hh
  · intro l' h; rw [hSm]; split
    · rfl
    · exact h
  · intro x l' h
    rw [hSm]; split
    · rfl
    · rcases hins x l' h with ⟨_, rfl⟩ | ⟨_, h⟩
      · contradiction
      · exact hok.1 _ _ x l' hσ h
  · intro x l' h
    rcases hins x l' h with ⟨_, rfl⟩ | ⟨_, h⟩
    · right; exact hnew
    · left; exact h
  · intro x x' l' h h'
    rcases hins x l' h with ⟨hx, hl⟩ | ⟨_, h1⟩ <;>
      rcases hins x' l' h' with ⟨hx', hl'⟩ | ⟨_, h2⟩
    · rw [hx, hx']
    · exact absurd (hl ▸ h2) (hlM x')
    · exact absurd (hl' ▸ h1) (hlM x)
    · exact oneId_last hh.2.1 hlast h1 h2
  · intro x l' S h hS
    rcases hins x l' h with ⟨rfl, rfl⟩ | ⟨hx, h⟩
    · rw [hSm, if_pos rfl] at hS; cases hS
      intro it
      simp only [GMap.lookup_empty, reduceCtorEq, false_iff]
      exact hI it
    · have hll : l ≠ l' := fun e => hlM x (e ▸ h)
      rw [hSm, if_neg hll] at hS
      rcases hok.2 l' S hS with ⟨hn, -⟩ | ⟨id3, i, τ, ⟨⟨τ', hi', hτ'⟩, hlat⟩, hi, hit⟩
      · exact absurd h (hn _ _ x hσ)
      · rw [hi] at hi'; cases hi'
        have h3 : id3 = x := hh.2.1 i _ τ (M, I, T) id3 x l' hi hσ hτ' h
        subst h3
        have hilt : i < hs.length := (List.getElem?_eq_some_iff.1 hi).1
        have : i = hs.length - 1 := by
          refine Nat.le_antisymm (by omega) (Nat.le_of_not_lt fun hlt => ?_)
          exact hlat _ (M, I, T) hlt hσ h
        subst this
        rw [hσ] at hi; cases hi
        exact hit
  · intro l' S hS hn
    have hll : l ≠ l' := fun e => hn id (by subst e; simp [GMap.lookup_insert_eq_iff])
    rw [hSm, if_neg hll] at hS
    left; exact hS
  · exact hh.2.2 (M, I, T) (List.mem_of_getElem? hσ)

/-- A lease of the last snapshot has, in the item sets' map, the items the last item map attaches
to its id. -/
theorem itemsFor_of_last {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {σ : LSnap}
    {id : w64} {l : Loc} {S : GMap LeaseItem Unit}
    (hlast : hs.getLast? = some σ) (hok : setsOk hs Sm) (hh : histOk hs)
    (hl : σ.1.lookup id = some l) (hS : Sm.lookup l = some S) : itemsFor σ.2.1 id S := by
  have ⟨hσ, hpos⟩ := getLast?_getElem? hlast
  rcases hok.2 l S hS with ⟨hn, -⟩ | ⟨id3, i, τ, ⟨⟨τ', hi', hτ'⟩, hlat⟩, hi, hit⟩
  · exact absurd hl (hn _ _ id hσ)
  · rw [hi] at hi'; cases hi'
    have h3 : id3 = id := hh.2.1 i _ τ σ id3 id l hi hσ hτ' hl
    subst h3
    have hilt : i < hs.length := (List.getElem?_eq_some_iff.1 hi).1
    have : i = hs.length - 1 := by
      refine Nat.le_antisymm (by omega) (Nat.le_of_not_lt fun hlt => ?_)
      exact hlat _ σ hlt hσ hl
    subst this
    rw [hσ] at hi; cases hi
    exact hit

/-- **`Attach`'s and `Detach`'s snapshot**: the item map changed to `I'` on the lease `l` of `id`
only, and `l`'s set with it (`S` to `S'`). -/
theorem setsOk_items {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {M : GMap w64 Loc}
    {I I' : GMap LeaseItem w64} {T : GMap w64 w64} {id : w64} {l : Loc}
    {S S' : GMap LeaseItem Unit}
    (hlast : hs.getLast? = some (M, I, T)) (hok : setsOk hs Sm) (hh : histOk hs)
    (hM : M.lookup id = some l) (hS : Sm.lookup l = some S)
    (hself : itemsFor I id S → itemsFor I' id S')
    (hother : ∀ id' : w64, id' ≠ id → ∀ it : LeaseItem, I'.lookup it = some id' ↔ I.lookup it = some id')
    (hshort : itemKeysShort I → itemKeysShort I') :
    setsOk (hs ++ [(M, I', T)]) (Sm.insert l S') ∧ histOk (hs ++ [(M, I', T)]) := by
  have ⟨hσ, hpos⟩ := getLast?_getElem? hlast
  have hSm : ∀ l' : Loc, (Sm.insert l S').lookup l' = if l = l' then some S' else Sm.lookup l' :=
    fun l' => GMap.lookup_insert_eq_iff Sm l l' S'
  apply setsOk_snoc hlast hok hh
  · intro l' h; rw [hSm]; split
    · rfl
    · exact h
  · intro x l' h
    rw [hSm]; split
    · rfl
    · exact hok.1 _ _ x l' hσ h
  · intro x l' h; left; exact h
  · intro x x' l' h h'; exact oneId_last hh.2.1 hlast h h'
  · intro x l' S0 h hS0
    by_cases hll : l = l'
    · subst hll
      have hx : x = id := oneId_last hh.2.1 hlast h hM
      subst hx
      rw [hSm, if_pos rfl] at hS0; cases hS0
      exact hself (itemsFor_of_last hlast hok hh hM hS)
    · rw [hSm, if_neg hll] at hS0
      have hx : x ≠ id := fun e => hll (by subst e; rw [hM] at h; cases h; rfl)
      have hit := itemsFor_of_last hlast hok hh h hS0
      intro it
      rw [hit it, hother x hx it]
  · intro l' S0 hS0 hn
    have hll : l ≠ l' := fun e => hn id (by subst e; exact hM)
    rw [hSm, if_neg hll] at hS0
    left; exact hS0
  · exact hshort (hh.2.2 (M, I, T) (List.mem_of_getElem? hσ))

/-- **`Revoke`'s snapshot**: the lease of `id` leaves the lease map; the item sets unchanged. -/
theorem setsOk_delete {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {M : GMap w64 Loc}
    {I : GMap LeaseItem w64} {T T' : GMap w64 w64} {id : w64}
    (hlast : hs.getLast? = some (M, I, T)) (hok : setsOk hs Sm) (hh : histOk hs) :
    setsOk (hs ++ [(M.delete id, I, T')]) Sm ∧ histOk (hs ++ [(M.delete id, I, T')]) := by
  have ⟨hσ, hpos⟩ := getLast?_getElem? hlast
  have hdel : ∀ (x : w64) (l' : Loc), (M.delete id).lookup x = some l' → x ≠ id ∧ M.lookup x = some l' := by
    intro x l' h
    by_cases hx : id = x
    · subst hx; rw [GMap.lookup_delete] at h; cases h
    · rw [GMap.lookup_delete_ne M hx] at h; exact ⟨Ne.symm hx, h⟩
  apply setsOk_snoc hlast hok hh
  · intro l' h; exact h
  · intro x l' h; exact hok.1 _ _ x l' hσ (hdel x l' h).2
  · intro x l' h; left; exact (hdel x l' h).2
  · intro x x' l' h h'; exact oneId_last hh.2.1 hlast (hdel x l' h).2 (hdel x' l' h').2
  · intro x l' S0 h hS0; exact itemsFor_of_last (σ := (M, I, T)) hlast hok hh (hdel x l' h).2 hS0
  · intro l' S0 hS0 _; left; exact hS0
  · exact hh.2.2 (M, I, T) (List.mem_of_getElem? hσ)

/-! ### Each id live over an interval (the lease-expiry plan's E3 (c), 2026-11-05; ids only since
S2–S4, Q-S4 (A))

`histOnce` is kept by every writer's snapshot (`histOnce_snoc`): each id of the new snapshot is
live in the last one (`Revoke`, `Attach`, `Detach`, `Grant`'s other leases, `Recover`'s ids the
history had) or is an id the history never had (`Grant`'s new lease, `Recover`'s other ids). Its law:
an id absent after being live stays absent (`histOnce_absent`). -/

/-- An id of a history appended to: of the history, or of the new snapshot. -/
theorem everIn_snoc {hs : List LSnap} {σ' : LSnap} {id : w64} :
    everIn (hs ++ [σ']) id ↔ everIn hs id ∨ (σ'.1.lookup id).isSome := by
  constructor
  · rintro ⟨i, σ, hi, h⟩
    rcases getElem?_snoc_cases hs σ' σ i hi with ⟨_, hi⟩ | ⟨_, hσ⟩
    · exact Or.inl ⟨i, σ, hi, h⟩
    · rw [hσ] at h; exact Or.inr h
  · rintro (⟨i, σ, hi, h⟩ | h)
    · exact ⟨i, σ, by rw [getElem?_snoc_lt hs σ' (List.getElem?_eq_some_iff.1 hi).1]; exact hi, h⟩
    · exact ⟨hs.length, σ', getElem?_snoc_len hs σ', h⟩

/-- A one-snapshot history. -/
theorem histOnce_single (σ : LSnap) : histOnce [σ] := by
  intro i j k a b c id hij hjk hi hj hk hl _
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · simp at hk
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  rw [hi0] at hi; rw [hj0] at hj
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hi hj
  rw [← hj, hi]; exact hl

/-- **Appending a snapshot keeps each id live over an interval** when every id of the new
snapshot is live in the last snapshot or is an id the history never had. -/
theorem histOnce_snoc {hs : List LSnap} {τ σ' : LSnap} (hlast : hs.getLast? = some τ)
    (hnew : ∀ id : w64, (σ'.1.lookup id).isSome → (τ.1.lookup id).isSome ∨ ¬ everIn hs id)
    (h : histOnce hs) : histOnce (hs ++ [σ']) := by
  have ⟨hτ, hpos⟩ := getLast?_getElem? hlast
  intro i j k σ υ ρ id hij hjk hi hj hk hl hl'
  rcases getElem?_snoc_cases hs σ' ρ k hk with ⟨hkl, hk'⟩ | ⟨hke, hρ⟩
  · -- all three in `hs`
    have hjl : j < hs.length := by omega
    have hil : i < hs.length := by omega
    rw [getElem?_snoc_lt hs σ' hil] at hi
    rw [getElem?_snoc_lt hs σ' hjl] at hj
    exact h i j k σ υ ρ id hij hjk hi hj hk' hl hl'
  · rw [hρ] at hl'
    rcases getElem?_snoc_cases hs σ' σ i hi with ⟨hil, hi'⟩ | ⟨hie, hσ⟩
    · -- `id` was live in `hs`: the last snapshot has it
      have hev : everIn hs id := ⟨i, σ, hi', hl⟩
      have hτl : (τ.1.lookup id).isSome := by
        rcases hnew id hl' with h' | h'
        · exact h'
        · exact absurd hev h'
      rcases getElem?_snoc_cases hs σ' υ j hj with ⟨hjl, hj'⟩ | ⟨hje, hυ⟩
      · exact h i j (hs.length - 1) σ υ τ id hij (by omega) hi' hj' hτ hl hτl
      · rw [hυ]; exact hl'
    · -- `i` the new index, so is `j`
      rw [hσ] at hl
      rw [show j = hs.length by omega, getElem?_snoc_len] at hj
      rw [← Option.some.inj hj]; exact hl

/-- **In a monotone history an id not live at the end was never live** (the monotone mode's
`Grant`: an id not live is new). -/
theorem not_everIn_of_mono {hs : List LSnap} {τ : LSnap} {id : w64}
    (hlast : hs.getLast? = some τ) (hm : histMono hs) (hn : τ.1.lookup id = none) :
    ¬ everIn hs id := by
  have ⟨hτ, _⟩ := getLast?_getElem? hlast
  rintro ⟨i, σ, hi, h⟩
  have hil : i < hs.length := (List.getElem?_eq_some_iff.1 hi).1
  have := hm i (hs.length - 1) σ τ id (by omega) hi hτ h
  rw [hn] at this; simp at this

/-- **`Grant`'s snapshot**: a new lease of an id the history never had. -/
theorem histOnce_grant {hs : List LSnap} {M : GMap w64 Loc} {I I' : GMap LeaseItem w64}
    {T T' : GMap w64 w64} {id : w64} {l : Loc}
    (hlast : hs.getLast? = some (M, I, T)) (hfresh : ¬ everIn hs id) (h : histOnce hs) :
    histOnce (hs ++ [(M.insert id l, I', T')]) := by
  apply histOnce_snoc hlast _ h
  intro x hx
  dsimp only at hx ⊢
  by_cases hxi : id = x
  · rw [← hxi]; right; exact hfresh
  · left; rw [GMap.lookup_insert_ne _ _ hxi] at hx; exact hx

/-- **`Revoke`'s snapshot**: a lease removed. -/
theorem histOnce_delete {hs : List LSnap} {M : GMap w64 Loc} {I I' : GMap LeaseItem w64}
    {T T' : GMap w64 w64} {id : w64}
    (hlast : hs.getLast? = some (M, I, T)) (h : histOnce hs) :
    histOnce (hs ++ [(M.delete id, I', T')]) := by
  apply histOnce_snoc hlast _ h
  intro x hx
  left
  dsimp only at hx ⊢
  by_cases hxi : id = x
  · rw [← hxi, GMap.lookup_delete] at hx; cases hx
  · rw [GMap.lookup_delete_ne M hxi] at hx; exact hx

/-- **`Attach`'s and `Detach`'s snapshot**: the lease map kept. -/
theorem histOnce_items {hs : List LSnap} {M : GMap w64 Loc} {I I' : GMap LeaseItem w64}
    {T T' : GMap w64 w64} (hlast : hs.getLast? = some (M, I, T)) (h : histOnce hs) :
    histOnce (hs ++ [(M, I', T')]) :=
  histOnce_snoc hlast (fun _ hx => Or.inl hx) h

/-- **`Recover`'s snapshot** (S2–S4, 2026-11-05): each of its ids an id the history never had, or
one the last snapshot has. -/
theorem histOnce_recover {hs : List LSnap} {τ σ' : LSnap} (hlast : hs.getLast? = some τ)
    (hfresh : ∀ id : w64, (σ'.1.lookup id).isSome → (τ.1.lookup id).isSome ∨ ¬ everIn hs id)
    (h : histOnce hs) : histOnce (hs ++ [σ']) :=
  histOnce_snoc hlast hfresh h

/-- **An id absent after being live stays absent** (E3 (c)'s first law, pure). -/
theorem histOnce_absent {hs : List LSnap} (h : histOnce hs) {i k j : Nat} {σ ρ τ : LSnap}
    {id : w64} {l : Loc} (hik : i ≤ k) (hkj : k ≤ j) (hi : hs[i]? = some σ)
    (hl : σ.1.lookup id = some l) (hk : hs[k]? = some ρ) (hρ : ρ.1.lookup id = none)
    (hj : hs[j]? = some τ) : τ.1.lookup id = none := by
  cases hτ : τ.1.lookup id with
  | none => rfl
  | some l' =>
    have := h i k j σ ρ τ id hik hkj hi hk hj (by rw [hl]; rfl) (by rw [hτ]; rfl)
    rw [hρ] at this; cases this

/-- **`histIn` with a snapshot appended** whose ids are in `U`. -/
theorem histIn_snoc_new {hs : List LSnap} {σ' : LSnap} {U : List w64} (h : histIn hs U)
    (hσ : ∀ id : w64, snapHas σ' id → id ∈ U) : histIn (hs ++ [σ']) U := by
  intro i σ id hi hh
  rcases getElem?_snoc_cases hs σ' σ i hi with ⟨_, hi'⟩ | ⟨_, hσ'⟩
  · exact h i σ id hi' hh
  · rw [hσ'] at hh; exact hσ id hh

/-- **`histIn` with a snapshot appended** whose ids the last snapshot has. -/
theorem histIn_snoc {hs : List LSnap} {τ σ' : LSnap} {U : List w64} (hlast : hs.getLast? = some τ)
    (hhas : ∀ id : w64, snapHas σ' id → snapHas τ id) (h : histIn hs U) :
    histIn (hs ++ [σ']) U :=
  histIn_snoc_new h (fun id hid => h _ τ id (getLast?_getElem? hlast).1 (hhas id hid))

/-- **`histIn` for a larger `U`.** -/
theorem histIn_mono {hs : List LSnap} {U U' : List w64} (h : histIn hs U)
    (hU : ∀ x, x ∈ U → x ∈ U') : histIn hs U' :=
  fun i σ id hi hh => hU id (h i σ id hi hh)

/-- **An id not in `U` the history never had.** -/
theorem not_everIn_of_histIn {hs : List LSnap} {U : List w64} {id : w64} (h : histIn hs U)
    (hid : id ∉ U) : ¬ everIn hs id := by
  rintro ⟨i, σ, hi, hl⟩
  exact hid (h i σ id hi (Or.inl hl))

/-- **The lease map's ids are the snapshot's.** -/
theorem snapHas_lease {σ : LSnap} {id : w64} (h : (σ.1.lookup id).isSome) : snapHas σ id :=
  Or.inl h

/-! ### The requested TTLs (the lease-expiry plan's S2–S4, Q-S6, 2026-11-05) -/

/-- **`reqOk` with a snapshot appended and the requests extended** by ids of the new snapshot the
history never had, whose new TTLs are at least their requests. -/
theorem reqOk_snoc_gen {hs : List LSnap} {σ' : LSnap} {Q Q' : GMap w64 w64} (h : reqOk hs Q)
    (hQ' : ∀ (id r : w64), Q'.lookup id = some r →
      Q.lookup id = some r ∨ ((σ'.1.lookup id).isSome ∧ ¬ everIn hs id))
    (hσ : ∀ (id t r : w64), (σ'.1.lookup id).isSome → σ'.2.2.lookup id = some t →
      Q'.lookup id = some r → sint.Z r ≤ sint.Z t) :
    reqOk (hs ++ [σ']) Q' := by
  constructor
  · intro i σ id t r hi hl ht hr
    rcases getElem?_snoc_cases hs σ' σ i hi with ⟨_, hi'⟩ | ⟨_, hσ'⟩
    · rcases hQ' id r hr with hq | ⟨_, hn⟩
      · exact h.1 i σ id t r hi' hl ht hq
      · exact absurd ⟨i, σ, hi', hl⟩ hn
    · rw [hσ'] at hl ht; exact hσ id t r hl ht hr
  · intro id r hr
    rcases hQ' id r hr with hq | ⟨hl, _⟩
    · exact everIn_snoc.2 (Or.inl (h.2 id r hq))
    · exact everIn_snoc.2 (Or.inr hl)

/-- **`reqOk` with a snapshot appended that keeps the last one's leases at their TTLs**
(`Revoke`, `Attach`, `Detach`: `tieSub`). -/
theorem reqOk_snoc_sub {hs : List LSnap} {τ σ' : LSnap} {Q : GMap w64 w64}
    (hlast : hs.getLast? = some τ) (hsub : tieSub τ σ') (h : reqOk hs Q) :
    reqOk (hs ++ [σ']) Q :=
  reqOk_snoc_gen h (fun _ _ hq => Or.inl hq) (fun id t r hl ht hr => by
    obtain ⟨l, hl'⟩ := Option.isSome_iff_exists.1 hl
    have ⟨hτl, hT⟩ := hsub.1 id l hl'
    rw [hT] at ht
    exact h.1 _ τ id t r (getLast?_getElem? hlast).1 (by rw [hτl]; rfl) ht hr)

/-- **`Grant`'s snapshot with its request**: a new lease of an id the history never had, at a TTL
at least its request. -/
theorem reqOk_grant {hs : List LSnap} {M : GMap w64 Loc} {I I' : GMap LeaseItem w64}
    {T : GMap w64 w64} {Q : GMap w64 w64} {id t r : w64} {l : Loc}
    (hlast : hs.getLast? = some (M, I, T)) (hev : ¬ everIn hs id) (hrt : sint.Z r ≤ sint.Z t)
    (h : reqOk hs Q) : reqOk (hs ++ [(M.insert id l, I', T.insert id t)]) (Q.insert id r) := by
  apply reqOk_snoc_gen h
  · intro x r' hx
    by_cases hxi : id = x
    · subst hxi; right; refine ⟨?_, hev⟩; dsimp only; rw [GMap.lookup_insert]; rfl
    · left; rwa [GMap.lookup_insert_ne _ _ hxi] at hx
  · intro x t' r' hl ht hr
    dsimp only at hl ht
    by_cases hxi : id = x
    · subst hxi
      rw [GMap.lookup_insert] at ht hr
      rw [← Option.some.inj ht, ← Option.some.inj hr]; exact hrt
    · rw [GMap.lookup_insert_ne _ _ hxi] at hl ht hr
      exact h.1 _ (M, I, T) x t' r' (getLast?_getElem? hlast).1 hl ht hr

end hist

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

open Iris Iris.BI Iris.ProofMode

/-- **An id absent after being live stays absent** (the lease-expiry plan's E3, 2026-11-05; for a
client's `Main`): a snapshot at `i` with a lease of `id`, one at `k ≥ i` without, and one at
`j ≥ k`: the last has none (`histOnce_absent`: each id is one lease over an interval of the
history). -/
theorem lessorAt_absent_stays (γl : GName) (i k j : Nat) (σ ρ τ : LSnap) (id : w64) (E : CoPset)
    (hE : ↑lessorRdN ⊆ E) (hσ : (σ.1.lookup id).isSome) (hik : i ≤ k)
    (hρ : ρ.1.lookup id = none) (hkj : k ≤ j) :
    lessorRdInv (GF := GF) γl ∗ lessorAt γl i σ ∗ lessorAt γl k ρ ∗ lessorAt γl j τ ⊢
      |={E}=> ⌜τ.1.lookup id = none⌝ := by
  unfold lessorRdInv lessorAt
  iintro ⟨⟨%γr, #Hp, #Hinv⟩, ⟨%γr1, #Hp1, #Hi⟩, ⟨%γr2, #Hp2, #Hk⟩, ⟨%γr3, #Hp3, #Hj⟩⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  ihave %H2 := lessorPinR_agree γl γr γr2 $$ [$Hp $Hp2]
  ihave %H3 := lessorPinR_agree γl γr γr3 $$ [$Hp $Hp3]
  subst H1; subst H2; subst H3
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs, %Sm, >Ha, >HS, >%Hok, >%Hmono, >HU, #>Htie, Hids⟩
  icases HU with ⟨%U, HU, %HUi⟩
  ihave %Hhi := mono_list_auth_idx_lookup γr.1 _ hs i σ $$ Ha Hi
  ihave %Hhk := mono_list_auth_idx_lookup γr.1 _ hs k ρ $$ Ha Hk
  ihave %Hhj := mono_list_auth_idx_lookup γr.1 _ hs j τ $$ Ha Hj
  imod Hclose $$ [Ha HS HU Hids] with -
  · inext; iunfold lessorRdBody; iexists hs, Sm; iframe Ha HS Htie Hids
    isplitr
    · ipureintro; exact Hok
    isplitr
    · ipureintro; exact Hmono
    iexists U; iframe HU; ipureintro; exact HUi
  imodintro
  ipureintro
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hσ
  exact histOnce_absent HUi.1 hik hkj Hhi hl Hhk hρ Hhj

/-- **Every TTL the history gives a lease is at least its request** (the lease-expiry plan's
S2–S4, Q-S8, 2026-11-05; for a client's `Main`; replaces `leaseTTLAt_ttl_agree`, whose "one
`*Lease` per id" `Recover` breaks): a request `r` of `id` (`leaseReqIs`, `Grant`'s or `Recover`'s)
and a TTL `t` of `id` at any index of the history (`leaseTTLAt`, `TimeToLive`'s): `r ≤ t`
(`reqOk`; the snapshot has `id` live, `ttlTie`). -/
theorem leaseTTLAt_ge_req (γl : GName) (j : Nat) (id r t : w64) (E : CoPset)
    (hE : ↑lessorRdN ⊆ E) :
    lessorRdInv (GF := GF) γl ∗ leaseReqIs γl id r ∗ leaseTTLAt γl j id t ⊢
      |={E}=> ⌜sint.Z r ≤ sint.Z t⌝ := by
  unfold lessorRdInv leaseReqIs leaseTTLAt lessorAt
  iintro ⟨⟨%γr, #Hp, #Hinv⟩, ⟨%γr1, #Hp1, #Hq⟩, ⟨%τ, %Hτ, %γr2, #Hp2, #Hj⟩⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  ihave %H2 := lessorPinR_agree γl γr γr2 $$ [$Hp $Hp2]
  subst H1; subst H2
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs, %Sm, >Ha, >HS, >%Hok, >%Hmono, >HU, #>Htie, Hids, >HQ⟩
  icases HQ with ⟨%Q, HQ, %HQo⟩
  ihave %Hhj := mono_list_auth_idx_lookup γr.1 _ hs j τ $$ Ha Hj
  ihave %Hqr := ghost_map_lookup $$ HQ Hq
  ihave #Hτt := BigSepL.bigSepL_lookup (Φ := fun _ σ => ttlTie (GF := GF) σ) Hhj $$ Htie
  iunfold ttlTie at Hτt
  icases Hτt with ⟨%Hdom, -⟩
  imod Hclose $$ [Ha HS HU Hids HQ] with -
  · inext; iunfold lessorRdBody; iexists hs, Sm; iframe Ha HS HU Htie Hids
    isplitr
    · ipureintro; exact Hok
    isplitr
    · ipureintro; exact Hmono
    iexists Q; iframe HQ; ipureintro; exact HQo
  imodintro
  ipureintro
  exact HQo.1 j τ id t r Hhj ((Hdom id).1 (by rw [Hτ]; rfl)) Hτ Hqr

end laws

end lease
end EtcdGrove
end Perennial
