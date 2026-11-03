/-
The lessor's history (the lease-keys plan, Part B, 2026-10-31): when appending a snapshot keeps
the readers' invariant's facts (`setsOk`, `histOk`). Pure. Lean-first (no Rocq counterpart).

`setsOk_snoc` is the one step every writer (`Grant`, `Attach`, `Detach`, `Revoke`) takes under
`le.mu`'s write lock, with the conditions each discharges of its own snapshot: every lease of the
new snapshot is in the last one under the same id or in no snapshot yet, a lease of it has the
items the new item map attaches to its id, and a lease not in it keeps its set (or is new, with
the empty set).
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
      Sm'.lookup l = some S → itemsFor σ'.2 id S)
    (hout : ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm'.lookup l = some S →
      (∀ id : w64, σ'.1.lookup id ≠ some l) →
      Sm.lookup l = some S ∨
        ((∀ (k : Nat) (τ : LSnap) (id : w64), hs[k]? = some τ → τ.1.lookup id ≠ some l) ∧ S = ∅))
    (hshort : itemKeysShort σ'.2) :
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
    {I : GMap LeaseItem w64} {id : w64} {l : Loc}
    (hlast : hs.getLast? = some (M, I)) (hok : setsOk hs Sm) (hh : histOk hs)
    (hM : M.lookup id = none) (hI : ∀ it : LeaseItem, I.lookup it ≠ some id)
    (hnew : ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some l) :
    setsOk (hs ++ [(M.insert id l, I)]) (Sm.insert l ∅) ∧ histOk (hs ++ [(M.insert id l, I)]) := by
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
        have h3 : id3 = x := hh.2.1 i _ τ (M, I) id3 x l' hi hσ hτ' h
        subst h3
        have hilt : i < hs.length := (List.getElem?_eq_some_iff.1 hi).1
        have : i = hs.length - 1 := by
          refine Nat.le_antisymm (by omega) (Nat.le_of_not_lt fun hlt => ?_)
          exact hlat _ (M, I) hlt hσ h
        subst this
        rw [hσ] at hi; cases hi
        exact hit
  · intro l' S hS hn
    have hll : l ≠ l' := fun e => hn id (by subst e; simp [GMap.lookup_insert_eq_iff])
    rw [hSm, if_neg hll] at hS
    left; exact hS
  · exact hh.2.2 (M, I) (List.mem_of_getElem? hσ)

/-- A lease of the last snapshot has, in the item sets' map, the items the last item map attaches
to its id. -/
theorem itemsFor_of_last {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {σ : LSnap}
    {id : w64} {l : Loc} {S : GMap LeaseItem Unit}
    (hlast : hs.getLast? = some σ) (hok : setsOk hs Sm) (hh : histOk hs)
    (hl : σ.1.lookup id = some l) (hS : Sm.lookup l = some S) : itemsFor σ.2 id S := by
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
    {I I' : GMap LeaseItem w64} {id : w64} {l : Loc} {S S' : GMap LeaseItem Unit}
    (hlast : hs.getLast? = some (M, I)) (hok : setsOk hs Sm) (hh : histOk hs)
    (hM : M.lookup id = some l) (hS : Sm.lookup l = some S)
    (hself : itemsFor I id S → itemsFor I' id S')
    (hother : ∀ id' : w64, id' ≠ id → ∀ it : LeaseItem, I'.lookup it = some id' ↔ I.lookup it = some id')
    (hshort : itemKeysShort I → itemKeysShort I') :
    setsOk (hs ++ [(M, I')]) (Sm.insert l S') ∧ histOk (hs ++ [(M, I')]) := by
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
  · exact hshort (hh.2.2 (M, I) (List.mem_of_getElem? hσ))

/-- **`Revoke`'s snapshot**: the lease of `id` leaves the lease map; the item sets unchanged. -/
theorem setsOk_delete {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {M : GMap w64 Loc}
    {I : GMap LeaseItem w64} {id : w64}
    (hlast : hs.getLast? = some (M, I)) (hok : setsOk hs Sm) (hh : histOk hs) :
    setsOk (hs ++ [(M.delete id, I)]) Sm ∧ histOk (hs ++ [(M.delete id, I)]) := by
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
  · intro x l' S0 h hS0; exact itemsFor_of_last (σ := (M, I)) hlast hok hh (hdel x l' h).2 hS0
  · intro l' S0 hS0 _; left; exact hS0
  · exact hh.2.2 (M, I) (List.mem_of_getElem? hσ)

end hist

end lease
end EtcdGrove
end Perennial
