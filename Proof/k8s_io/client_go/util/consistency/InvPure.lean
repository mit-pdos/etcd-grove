/-
The consistency store's invariant, its pure part (`consWf`, `Defs.lean`): each step of the
methods preserves it. Lean-first.

- `wf_found`: `WroteAt` finds the owner's record for its UID; its write becomes pending.
- `wf_new`: `WroteAt` installs a new record (none, or one for another UID, was there).
- `wf_withdraw`: a pending write lands in its record.
- `wf_ens_deposit`, `wf_ens_ok`, `wf_ens_err`: `EnsureReady` takes its slot, finds the record
  ready (deleting it abstractly), or not.
- `wf_clear`, `wf_clear_ens`: `Clear`, from any caller or from `EnsureReady`.
-/
module

public import Proof.k8s_io.client_go.util.consistency.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris resourceversion

section pure
variable [FfiSyntax]

/-- Deleting a key a map lacks. -/
theorem delete_none {K V : Type} [DecidableEq K] (m : GMap K V) (k : K) (h : m !! k = none) :
    GMap.delete k m = m := by
  apply GMap.ext; intro k'
  rw [GMap.lookup_delete_iff]
  split
  · rename_i e; subst e; exact h.symm
  · rfl

theorem absVsOk_congr {V Va : Vs} {pin pin' : GR → GoString → Prop}
    (h : ∀ gr y, pin gr y ↔ pin' gr y) (hok : absVsOk V pin Va) : absVsOk V pin' Va := by
  have e : pin = pin' := funext fun gr => funext fun y => propext (h gr y)
  subst e; exact hok

theorem pendOf_insert (P : GMap Nat Pend) (n : Nat) (p : Pend) (hn : P !! n = none) (r : Loc)
    (gr : GR) (y : GoString) :
    pendOf (<[n := p]> P) r gr y ↔ pendOf P r gr y ∨ (p.r = r ∧ gr = p.gr ∧ y = p.rv) := by
  unfold pendOf
  constructor
  · rintro ⟨id, p', hp', h1, h2, h3⟩
    rw [GMap.lookup_insert_eq_iff] at hp'
    split at hp'
    · cases hp'; exact Or.inr ⟨h1, h2.symm, h3.symm⟩
    · exact Or.inl ⟨id, p', hp', h1, h2, h3⟩
  · rintro (⟨id, p', hp', h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · refine ⟨id, p', ?_, h1, h2, h3⟩
      rw [GMap.lookup_insert_eq_iff]
      split
      · rename_i e; subst e; rw [hn] at hp'; cases hp'
      · exact hp'
    · exact ⟨n, p, GMap.lookup_insert_eq _ _ _, h1, h2.symm, h3.symm⟩

theorem pendOf_delete (P : GMap Nat Pend) (id : Nat) (r : Loc) (gr : GR) (y : GoString) :
    pendOf (GMap.delete id P) r gr y → pendOf P r gr y := by
  rintro ⟨id', p', hp', h1, h2, h3⟩
  rw [GMap.lookup_delete_iff] at hp'
  split at hp'
  · cases hp'
  · exact ⟨id', p', hp', h1, h2, h3⟩

theorem pendOf_delete_sup (P : GMap Nat Pend) (id : Nat) (p : Pend) (h : P !! id = some p)
    (r : Loc) (gr : GR) (y : GoString) :
    pendOf P r gr y → pendOf (GMap.delete id P) r gr y ∨ (p.r = r ∧ gr = p.gr ∧ y = p.rv) := by
  rintro ⟨id', p', hp', h1, h2, h3⟩
  by_cases e : id = id'
  · subst e; rw [h] at hp'; cases hp'; exact Or.inr ⟨h1, h2.symm, h3.symm⟩
  · left; refine ⟨id', p', ?_, h1, h2, h3⟩
    rw [GMap.lookup_delete_iff]; simp [e, hp']

theorem pendOf_other (P : GMap Nat Pend) (r : Loc) (h : ∀ id p, P !! id = some p → p.r ≠ r)
    (gr : GR) (y : GoString) : ¬ pendOf P r gr y := by
  rintro ⟨id, p, hp, h1, -, -⟩; exact h id p hp h1

/-- The owner of a record is the owner it is current for. -/
theorem owner_of_W {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {r : Loc}
    (h : W !! o = some r) : ∃ s, R !! r = some s ∧ s.owner = o := hwf.2.1 o r h

theorem fresh_n {M W R Vg P n E} (hwf : consWf M W R Vg P n E) : P !! n = none := by
  cases h : P !! n with
  | none => rfl
  | some p => exact absurd (hwf.2.2.1 n p h).2 (Nat.lt_irrefl n)

/-- **`WroteAt` finds its record**: the write becomes pending (as id `n`). -/
theorem wf_found {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {r : Loc} {s : RecS}
    {uid : GoString} (gr : GR) (rv : GoString) (q : Qp)
    (hWo : W !! o = some r) (hR : R !! r = some s) (hown : s.owner = o) (huid : s.uid = uid)
    (hE : E !! o = none) :
    consWf (wroteAtM M o uid gr rv) W R Vg (<[n := ⟨r, gr, rv, q⟩]> P) (n + 1) E := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  have hn : P !! n = none := fresh_n ⟨hA, hW, hP, hV, hRV, hEw⟩
  refine ⟨?_, hW, ?_, hV, hRV, hEw⟩
  · intro o'
    by_cases eo : o' = o
    · subst eo
      have h := hA o'
      rw [hWo] at h ⊢
      have hnc : ¬ clearedAt E o' r := by rintro ⟨e, he, -⟩; rw [hE] at he; cases he
      obtain ⟨s1, V, Va, hR1, hVg, hM, hok⟩ := h.2 hnc
      rw [hR] at hR1; cases hR1
      refine ⟨fun hc => absurd hc hnc, fun _ => ⟨s, V, wroteAtVs Va gr rv, hR, hVg, ?_, ?_⟩⟩
      · simp only [wroteAtM, recFor, hM, huid, ↓reduceIte, GMap.lookup_insert_eq]
      · have := absVsOk_add V Va (pendOf P r) gr rv hok
        refine absVsOk_congr (fun g y => ?_) this
        rw [pendOf_insert P n _ hn r g y]
        simp only [true_and]
    · have hM : (wroteAtM M o uid gr rv) !! o' = M !! o' := by
        simp only [wroteAtM]; rw [GMap.lookup_insert_ne _ _ (Ne.symm eo)]
      have h := hA o'
      rw [hM]
      cases hw : W !! o' with
      | none => rw [hw] at h; exact h
      | some r' =>
        rw [hw] at h
        have hne : r' ≠ r := by
          intro e; subst e
          obtain ⟨s2, hs2, ho2⟩ := hW o' r' hw
          rw [hR] at hs2; cases hs2; exact eo (ho2.symm.trans hown)
        refine ⟨h.1, fun hnc => ?_⟩
        obtain ⟨s1, V, Va, h1, h2, h3, hok⟩ := h.2 hnc
        refine ⟨s1, V, Va, h1, h2, h3, absVsOk_congr (fun g y => ?_) hok⟩
        rw [pendOf_insert P n _ hn r' g y]
        constructor
        · exact Or.inl
        · rintro (h | ⟨h1, -⟩); exact h; exact absurd h1 (Ne.symm hne)
  · intro id p hp
    rw [GMap.lookup_insert_eq_iff] at hp
    split at hp
    · cases hp; rename_i e; subst e; exact ⟨by simp [hR], Nat.lt_succ_self _⟩
    · have := hP id p hp; exact ⟨this.1, Nat.lt_succ_of_lt this.2⟩

/-- **`WroteAt` installs a new record** `r'` (registered as `s'`, empty) for its owner, where
there was none or one for another UID; the write becomes pending (as id `n`). -/
theorem wf_new {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {r' : Loc} {s' : RecS}
    {uid : GoString} (gr : GR) (rv : GoString) (q : Qp)
    (hold : W !! o = none ∨ ∃ r0 s0, W !! o = some r0 ∧ R !! r0 = some s0 ∧ s0.uid ≠ uid)
    (hfresh : R !! r' = none) (hown : s'.owner = o) (huid : s'.uid = uid) (hE : E !! o = none) :
    consWf (wroteAtM M o uid gr rv) (<[o := r']> W) (<[r' := s']> R) (<[r' := ∅]> Vg)
      (<[n := ⟨r', gr, rv, q⟩]> P) (n + 1) E := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  have hn : P !! n = none := fresh_n ⟨hA, hW, hP, hV, hRV, hEw⟩
  -- no pending write is to `r'`, nor any current record or slot `r'`
  have hpr' : ∀ id p, P !! id = some p → p.r ≠ r' := by
    intro id p hp e; have := (hP id p hp).1; rw [e, hfresh] at this; cases this
  have hWr' : ∀ o' r, W !! o' = some r → r ≠ r' := by
    intro o' r hw e; obtain ⟨s2, hs2, -⟩ := hW o' r hw; rw [e, hfresh] at hs2; cases hs2
  -- the old record's abstract value is none or for another UID: `recFor` is a new record
  have hrec : recFor M o uid = ⟨uid, ∅⟩ := by
    have h := hA o
    have hnc : ∀ r, ¬ clearedAt E o r := by rintro r ⟨e, he, -⟩; rw [hE] at he; cases he
    rcases hold with hw | ⟨r0, s0, hw, hs0, hne⟩
    · rw [hw] at h; simp only [recFor, h]
    · rw [hw] at h
      obtain ⟨s1, V, Va, h1, -, hM, -⟩ := h.2 (hnc r0)
      rw [hs0] at h1; cases h1
      simp only [recFor, hM, hne, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o'
    by_cases eo : o' = o
    · subst eo
      simp only [GMap.lookup_insert_eq]
      have hnc : ¬ clearedAt E o' r' := by rintro ⟨e, he, -⟩; rw [hE] at he; cases he
      refine ⟨fun hc => absurd hc hnc, fun _ => ⟨s', ∅, wroteAtVs ∅ gr rv,
        rfl, rfl, ?_, ?_⟩⟩
      · simp only [wroteAtM, hrec, huid, GMap.lookup_insert_eq]
      · have := absVsOk_add ∅ ∅ (fun _ _ => False) gr rv absVsOk_empty
        refine absVsOk_congr (fun g y => ?_) this
        rw [pendOf_insert P n _ hn r' g y]
        simp only [false_or, true_and]
        constructor
        · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · exact absurd h (pendOf_other P r' hpr' g y)
          · exact ⟨h1, h2⟩
    · have hM : (wroteAtM M o uid gr rv) !! o' = M !! o' := by
        simp only [wroteAtM]; rw [GMap.lookup_insert_ne _ _ (Ne.symm eo)]
      rw [GMap.lookup_insert_ne _ _ (Ne.symm eo), hM]
      have h := hA o'
      cases hw : W !! o' with
      | none => rw [hw] at h; exact h
      | some r =>
        rw [hw] at h
        have hne := hWr' o' r hw
        refine ⟨h.1, fun hnc => ?_⟩
        obtain ⟨s1, V, Va, h1, h2, h3, hok⟩ := h.2 hnc
        refine ⟨s1, V, Va, ?_, ?_, h3, absVsOk_congr (fun g y => ?_) hok⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h1
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h2
        · rw [pendOf_insert P n _ hn r g y]
          constructor
          · exact Or.inl
          · rintro (h | ⟨h1, -⟩); exact h; exact absurd h1 (Ne.symm hne)
  · intro o' r hw
    rw [GMap.lookup_insert_eq_iff] at hw
    split at hw
    · cases hw; rename_i e; subst e; exact ⟨s', GMap.lookup_insert_eq _ _ _, hown⟩
    · obtain ⟨s2, h1, h2⟩ := hW o' r hw
      refine ⟨s2, ?_, h2⟩
      rw [GMap.lookup_insert_ne _ _ (Ne.symm (hWr' o' r hw))]; exact h1
  · intro id p hp
    rw [GMap.lookup_insert_eq_iff] at hp
    split at hp
    · cases hp; rename_i e; subst e; exact ⟨by simp, Nat.lt_succ_self _⟩
    · have h := hP id p hp
      refine ⟨?_, Nat.lt_succ_of_lt h.2⟩
      rw [GMap.lookup_insert_ne _ _ (Ne.symm (hpr' id p hp))]; exact h.1
  · intro r V hv
    rw [GMap.lookup_insert_eq_iff] at hv
    split at hv
    · cases hv; intro gr x hx; simp at hx
    · exact hV r V hv
  · intro r hr
    rw [GMap.lookup_insert_eq_iff] at hr ⊢
    split
    · rfl
    · rename_i e; simp only [e, ↓reduceIte] at hr; exact hRV r hr
  · intro o' e he
    obtain ⟨h1, h2, s2, h3, h4⟩ := hEw o' e he
    have hne : e.r ≠ r' := by intro x; rw [x, hfresh] at h3; cases h3
    have heo : o' ≠ o := by intro x; subst x; rw [hE] at he; cases he
    refine ⟨?_, ?_, s2, ?_, h4⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm heo)]; exact h1
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h2
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h3

/-- **A pending write lands**: the record's physical versions take it, it is no longer pending.
(No `EnsureReady` slot is for the record's owner: the write's permission excludes it.) -/
theorem wf_withdraw {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {id : Nat} {p : Pend}
    {s : RecS} {V : Vs} (hp : P !! id = some p) (hR : R !! p.r = some s) (hVg : Vg !! p.r = some V)
    (hE : E !! s.owner = none) :
    consWf M W R (<[p.r := wroteAtVs V p.gr p.rv]> Vg) (GMap.delete id P) n E := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  refine ⟨?_, hW, ?_, ?_, ?_, ?_⟩
  · intro o
    have h := hA o
    cases hw : W !! o with
    | none => rw [hw] at h; exact h
    | some r =>
      rw [hw] at h
      refine ⟨h.1, fun hnc => ?_⟩
      obtain ⟨s1, V1, Va, h1, h2, h3, hok⟩ := h.2 hnc
      by_cases er : r = p.r
      · subst er
        rw [hVg] at h2; cases h2
        refine ⟨s1, wroteAtVs V p.gr p.rv, Va, h1, GMap.lookup_insert_eq _ _ _, h3, ?_⟩
        exact absVsOk_withdraw V Va (pendOf P p.r) (pendOf (GMap.delete id P) p.r) p.gr p.rv
          (hV _ _ hVg) ⟨id, p, hp, rfl, rfl, rfl⟩ (pendOf_delete P id p.r)
          (fun g y hy => by
            rcases pendOf_delete_sup P id p hp p.r g y hy with h | ⟨-, h2, h3⟩
            · exact Or.inl h
            · exact Or.inr ⟨h2, h3⟩) hok
      · refine ⟨s1, V1, Va, h1, ?_, h3, absVsOk_congr (fun g y => ?_) hok⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm er)]; exact h2
        · constructor
          · intro hy
            rcases pendOf_delete_sup P id p hp r g y hy with h | ⟨h1, -⟩
            · exact h
            · exact absurd h1.symm er
          · exact pendOf_delete P id r g y
  · intro id' p' hp'
    rw [GMap.lookup_delete_iff] at hp'
    split at hp'
    · cases hp'
    · exact hP id' p' hp'
  · intro r V' hv
    rw [GMap.lookup_insert_eq_iff] at hv
    split at hv
    · cases hv; exact wroteAtVs_wf V p.gr p.rv (hV _ _ hVg)
    · exact hV r V' hv
  · intro r hr
    rw [GMap.lookup_insert_eq_iff]
    split
    · rfl
    · exact hRV r hr
  · intro o e he
    obtain ⟨h1, h2, s2, h3, h4⟩ := hEw o e he
    have hne : e.r ≠ p.r := by
      intro x; rw [x, hR] at h3; cases h3; rw [h4] at hE; rw [hE] at he; cases he
    refine ⟨h1, ?_, s2, h3, h4⟩
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h2

/-- **`EnsureReady` takes its slot** for the owner's current record `r`. -/
theorem wf_ens_deposit {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {r : Loc}
    {V : Vs} (hWo : W !! o = some r) (hVg : Vg !! r = some V) (hE : E !! o = none) :
    consWf M W R Vg P n (<[o := ⟨r, V, false⟩]> E) := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  refine ⟨?_, hW, hP, hV, hRV, ?_⟩
  · intro o'
    have h := hA o'
    have hc : ∀ r', clearedAt (<[o := ⟨r, V, false⟩]> E) o' r' ↔ clearedAt E o' r' := by
      intro r'
      unfold clearedAt
      by_cases eo : o' = o
      · subst eo
        simp only [GMap.lookup_insert_eq, hE]
        constructor
        · rintro ⟨e, he, -, h2⟩; cases he; cases h2
        · rintro ⟨e, he, -⟩; cases he
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm eo)]
    cases hw : W !! o' with
    | none => rw [hw] at h; exact h
    | some r' => rw [hw] at h; simp only [hc]; exact h
  · intro o' e he
    rw [GMap.lookup_insert_eq_iff] at he
    split at he
    · cases he; rename_i e; subst e
      obtain ⟨s, hs, ho⟩ := hW _ _ hWo
      exact ⟨Or.inl hWo, hVg, s, hs, ho⟩
    · exact hEw o' e he

theorem clearedAt_insert_ne {E : GMap Owner EnsSt} {o o' : Owner} (e : EnsSt) (r : Loc)
    (h : o' ≠ o) : clearedAt (<[o := e]> E) o' r ↔ clearedAt E o' r := by
  unfold clearedAt; rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]

theorem clearedAt_delete_ne {E : GMap Owner EnsSt} {o o' : Owner} (r : Loc)
    (h : o' ≠ o) : clearedAt (GMap.delete o E) o' r ↔ clearedAt E o' r := by
  unfold clearedAt; rw [GMap.lookup_delete_ne _ (Ne.symm h)]

/-- **`EnsureReady` finds its record ready**: it marks its slot cleared and deletes the owner's
record abstractly; the owner's abstract record was none or the slot's versions. -/
theorem wf_ens_ok {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {r : Loc} {V : Vs}
    (he : E !! o = some ⟨r, V, false⟩) (hnop : ∀ id p, P !! id = some p → p.r ≠ r) :
    consWf (GMap.delete o M) W R Vg P n (<[o := ⟨r, V, true⟩]> E) ∧
      (M !! o = none ∨ ∃ s, R !! r = some s ∧ M !! o = some ⟨s.uid, V⟩) := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  obtain ⟨hWo, hVg, -⟩ := hEw o _ he
  have hnc : ∀ r', ¬ clearedAt E o r' := by
    rintro r' ⟨e, he', -, h2⟩; rw [he] at he'; cases he'; cases h2
  refine ⟨⟨?_, hW, hP, hV, hRV, ?_⟩, ?_⟩
  · intro o'
    have h := hA o'
    by_cases eo : o' = o
    · subst eo
      rw [GMap.lookup_delete_eq]
      cases hw : W !! o' with
      | none => rfl
      | some r' => exact ⟨fun _ => rfl, fun hc => absurd ⟨_, GMap.lookup_insert_eq _ _ _, by
          rcases hWo with h1 | h1 <;> rw [hw] at h1 <;> cases h1; rfl, rfl⟩ hc⟩
    · rw [GMap.lookup_delete_ne _ (Ne.symm eo)]
      cases hw : W !! o' with
      | none => rw [hw] at h; exact h
      | some r' =>
        rw [hw] at h
        simp only [clearedAt_insert_ne _ _ eo]
        exact h
  · intro o' e he'
    rw [GMap.lookup_insert_eq_iff] at he'
    split at he'
    · cases he'; rename_i x; subst x
      obtain ⟨h1, h2, h3⟩ := hEw _ _ he
      exact ⟨h1, h2, h3⟩
    · exact hEw o' e he'
  · have h := hA o
    rcases hWo with hw | hw
    · rw [hw] at h
      obtain ⟨s1, V1, Va, h1, h2, h3, hok⟩ := h.2 (hnc r)
      rw [hVg] at h2; cases h2
      have := absVsOk_nil V Va (pendOf P r) (pendOf_other P r hnop) hok
      subst this
      exact Or.inr ⟨s1, h1, h3⟩
    · rw [hw] at h; exact Or.inl h

/-- **`EnsureReady` finds its record not ready**: it gives its slot up; nothing else changes. -/
theorem wf_ens_err {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {e : EnsSt}
    (he : E !! o = some e) (hnc : e.cleared = false) :
    consWf M W R Vg P n (GMap.delete o E) := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  refine ⟨?_, hW, hP, hV, hRV, ?_⟩
  · intro o'
    have h := hA o'
    cases hw : W !! o' with
    | none => rw [hw] at h; exact h
    | some r' =>
      rw [hw] at h
      have hc : clearedAt (GMap.delete o E) o' r' ↔ clearedAt E o' r' := by
        by_cases eo : o' = o
        · subst eo
          unfold clearedAt
          rw [GMap.lookup_delete_eq]
          constructor
          · rintro ⟨_, h, -⟩; cases h
          · rintro ⟨e', h1, -, h2⟩; rw [he] at h1; cases h1; rw [hnc] at h2; cases h2
        · exact clearedAt_delete_ne _ eo
      simp only [hc]; exact h
  · intro o' e' he'
    rw [GMap.lookup_delete_iff] at he'
    split at he'
    · cases he'
    · exact hEw o' e' he'

/-- **`Clear` deletes** the owner's current record `r0` (its UID matches, or `uid` is empty). -/
theorem wf_clear_del {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {r0 : Loc}
    {s0 : RecS} {uid : GoString} (hWo : W !! o = some r0) (hs0 : R !! r0 = some s0)
    (hc : uid = [] ∨ s0.uid = uid) :
    consWf (clearM M o uid) (GMap.delete o W) R Vg P n E := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  have hMo : clearM M o uid !! o = none := by
    have h := hA o
    rw [hWo] at h
    by_cases hcl : clearedAt E o r0
    · have := h.1 hcl; simp only [clearM, this]
    · obtain ⟨s1, V, Va, h1, -, h3, -⟩ := h.2 hcl
      rw [hs0] at h1; cases h1
      simp only [clearM, h3, hc, ↓reduceIte, GMap.lookup_delete_eq]
  have hMo' : ∀ o', o' ≠ o → clearM M o uid !! o' = M !! o' := by
    intro o' eo
    simp only [clearM]
    split
    · split
      · rw [GMap.lookup_delete_ne _ (Ne.symm eo)]
      · rfl
    · rfl
  refine ⟨?_, ?_, hP, hV, hRV, ?_⟩
  · intro o'
    by_cases eo : o' = o
    · subst eo; rw [GMap.lookup_delete_eq]; exact hMo
    · rw [GMap.lookup_delete_ne _ (Ne.symm eo), hMo' o' eo]; exact hA o'
  · intro o' r hw
    rw [GMap.lookup_delete_iff] at hw
    split at hw
    · cases hw
    · exact hW o' r hw
  · intro o' e he
    obtain ⟨h1, h2, h3⟩ := hEw o' e he
    refine ⟨?_, h2, h3⟩
    by_cases eo : o' = o
    · subst eo; right; exact GMap.lookup_delete_eq _ _
    · rw [GMap.lookup_delete_ne _ (Ne.symm eo)]; exact h1

/-- **`Clear` deletes nothing** (no record, or one for another UID and `uid` is not empty): the
abstract state does not change. -/
theorem clearM_keep {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {uid : GoString}
    (h : W !! o = none ∨ ∃ r0 s0, W !! o = some r0 ∧ R !! r0 = some s0 ∧
      ¬ (uid = [] ∨ s0.uid = uid)) :
    clearM M o uid = M := by
  have hA := hwf.1 o
  rcases h with hw | ⟨r0, s0, hw, hs0, hc⟩
  · rw [hw] at hA; simp only [clearM, hA]
  · rw [hw] at hA
    by_cases hcl : clearedAt E o r0
    · simp only [clearM, hA.1 hcl]
    · obtain ⟨s1, V, Va, h1, -, h3, -⟩ := hA.2 hcl
      rw [hs0] at h1; cases h1
      simp only [clearM, h3, hc, ↓reduceIte]

/-- **`EnsureReady`'s own `Clear`**: the owner's record (its slot's, cleared, or none) goes
physically and the slot with it; abstractly nothing changes. -/
theorem wf_clear_ens {M W R Vg P n E} (hwf : consWf M W R Vg P n E) {o : Owner} {r : Loc}
    {V : Vs} (he : E !! o = some ⟨r, V, true⟩) :
    consWf M (GMap.delete o W) R Vg P n (GMap.delete o E) ∧ M !! o = none ∧
      (W !! o = some r ∨ W !! o = none) := by
  obtain ⟨hA, hW, hP, hV, hRV, hEw⟩ := hwf
  obtain ⟨hWo, -, -⟩ := hEw o _ he
  have hMo : M !! o = none := by
    have h := hA o
    rcases hWo with hw | hw
    · rw [hw] at h; exact h.1 ⟨_, he, rfl, rfl⟩
    · rw [hw] at h; exact h
  refine ⟨⟨?_, ?_, hP, hV, hRV, ?_⟩, hMo, hWo⟩
  · intro o'
    by_cases eo : o' = o
    · subst eo; rw [GMap.lookup_delete_eq]; exact hMo
    · rw [GMap.lookup_delete_ne _ (Ne.symm eo)]
      have h := hA o'
      cases hw : W !! o' with
      | none => rw [hw] at h; exact h
      | some r' => rw [hw] at h; simp only [clearedAt_delete_ne _ eo]; exact h
  · intro o' r' hw
    rw [GMap.lookup_delete_iff] at hw
    split at hw
    · cases hw
    · exact hW o' r' hw
  · intro o' e he'
    rw [GMap.lookup_delete_iff] at he'
    split at he'
    · cases he'
    · rename_i eo
      obtain ⟨h1, h2, h3⟩ := hEw o' e he'
      refine ⟨?_, h2, h3⟩
      rw [GMap.lookup_delete_ne _ eo]; exact h1

end pure

end consistency
end EtcdGrove
end Perennial
