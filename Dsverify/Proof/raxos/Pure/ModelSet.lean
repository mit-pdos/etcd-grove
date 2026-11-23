/-
The kit's porcupine model, pure (notes/dsv-quepaxa.md; paxos's `ModelSet.lean` for a map): the
model's state (`model.go`: per key an entry `{Found, V, Old, New}`) stands for a set of
configurations of linkv's pending-writes store `kvB` (`Pure/Smr.lean`), `mSet`, and the model's step
(`stepE` on the input's key) is `pSeq kvB`'s step on those sets, exactly: `step_mSet`.

An entry `e` (known state `e.known`, pending values `e.all = e.old ++ e.new`) stands for the
configurations whose key state and pending values `(σ, R)` are: the known state, every `new` put
still pending and any `old` one taken effect before (then overwritten): `new ⊆ R ⊆ all`; or some
pending `x` taken effect last and any of the others before it: `σ = some x`, `R ⊆ all - x`
(multisets: `Subperm`).
-/
module

public import Dsverify.Proof.raxos.Pure.Smr
public import Batteries.Data.List.Perm

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.raxos.pure

open EtcdGrove.linkv

/-! ## Entries and their sets -/

/-- One key's entry (`model.go`'s `Entry` without its key). -/
structure Ent where
  f : Bool
  v : GoString
  old : List GoString
  new : List GoString
deriving DecidableEq, Inhabited

/-- A key without an entry: nothing known, nothing pending. -/
def Ent.empty : Ent := ⟨false, [], [], []⟩

/-- The known state as the store's. -/
def Ent.known (e : Ent) : Option GoString := if e.f then some e.v else none

/-- All pending values. -/
def Ent.all (e : Ent) : List GoString := e.old ++ e.new

/-- A Go entry's invariant: nothing known means the empty value. -/
def Ent.Ok (e : Ent) : Prop := e.f = false → e.v = []

/-- The key states and pending values an entry stands for. -/
def eSet (e : Ent) (σ : Option GoString) (R : List GoString) : Prop :=
  (σ = e.known ∧ e.new.Subperm R ∧ R.Subperm e.all) ∨
    ∃ x ∈ e.all, σ = some x ∧ R.Subperm (e.all.erase x)

/-- A put of `v` at `k`. -/
def mk (k v : GoString) : KIn := ⟨true, k, v⟩

/-- The values of the pending puts at `k`. -/
def vals (k : GoString) (p : List KIn) : List GoString :=
  (p.filter (fun i => decide (i.k = k))).map KIn.v

/-- The configurations. -/
abbrev Cfg := PCfg Store KIn

/-- Every pending operation is a put. -/
def allPuts (c : Cfg) : Prop := ∀ i ∈ c.pend, i.put = true

/-- **The configurations the model's state `M` (key ↦ entry) stands for.** -/
def mSet (M : GoString → Ent) : PSet Store KIn :=
  fun c => allPuts c ∧ ∀ k, eSet (M k) (c.st k) (vals k c.pend)

/-- A get's answer at a key state. -/
def ans (σ : Option GoString) : KOut :=
  match σ with
  | some v => ⟨true, v⟩
  | none => ⟨false, []⟩

/-- `model.go`'s `stepE` on an entry: its verdict and the next entry. -/
def stepE (e : Ent) (i : KIn) (a : Ans KOut) : Bool × Ent :=
  match a with
  | .err => if i.put then (true, ⟨e.f, e.v, e.old, e.new ++ [i.v]⟩) else (true, e)
  | .ok o =>
    if i.put then
      (if o.found || decide (o.v ≠ []) then (false, e) else (true, ⟨true, i.v, e.all, []⟩))
    else if o.found = e.f ∧ o.v = e.v then (true, e)
    else if o.found ∧ o.v ∈ e.all then (true, ⟨true, o.v, e.all.erase o.v, []⟩)
    else (false, e)

/-- The model's state with key `k`'s entry `e`. -/
def upd (M : GoString → Ent) (k : GoString) (e : Ent) : GoString → Ent :=
  fun k' => if k' = k then e else M k'

/-! ## Lists -/

theorem split_subperm {A R : List GoString} (h : R.Subperm A) :
    R.Perm A ∨ ∃ y ∈ A, R.Subperm (A.erase y) := by
  by_cases hl : R.length < A.length
  · obtain ⟨a, ha⟩ := h.exists_of_length_lt hl
    have hm : a ∈ A := ha.subset (List.mem_cons_self)
    right
    refine ⟨a, hm, ?_⟩
    have := (List.perm_cons_erase hm).subperm_left.1 ha
    exact (List.subperm_cons a).1 this
  · left; exact h.perm_of_length_le (by omega)

theorem cons_subperm {A R : List GoString} {x : GoString} (hx : x ∈ A)
    (h : R.Subperm (A.erase x)) : (x :: R).Subperm A :=
  (List.perm_cons_erase hx).subperm_left.2 ((List.subperm_cons x).2 h)

theorem erase_erase_subperm (A : List GoString) (x y : GoString) :
    ((A.erase y).erase x).Subperm (A.erase x) := by
  rw [List.erase_comm]; exact List.erase_subperm _ _

/-! ## The entry's set -/

theorem eSet_perm {e : Ent} {σ : Option GoString} {R R' : List GoString} (hp : R.Perm R')
    (h : eSet e σ R) : eSet e σ R' := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨x, hx, h1, h2⟩
  · exact .inl ⟨h1, hp.subperm_left.1 h2, hp.subperm_right.1 h3⟩
  · exact .inr ⟨x, hx, h1, hp.subperm_right.1 h2⟩

theorem eSet_apply {e : Ent} {σ : Option GoString} {R : List GoString} {x : GoString}
    (h : eSet e σ R) (hx : x ∈ R) : eSet e (some x) (R.erase x) := by
  right
  rcases h with ⟨-, -, h3⟩ | ⟨y, -, -, h2⟩
  · exact ⟨x, h3.subset hx, rfl, h3.erase x⟩
  · exact ⟨x, (List.erase_subperm y _).subset (h2.subset hx), rfl,
      (h2.erase x).trans (erase_erase_subperm _ _ _)⟩

/-- The configuration `c` with key `k`'s state `σ` and pending values `R`. -/
def put (c : Cfg) (k : GoString) (σ : Option GoString) (R : List GoString) : Cfg :=
  ⟨fun k' => if k' = k then σ else c.st k', R.map (mk k) ++ c.pend.filter (fun i => decide (i.k ≠ k))⟩

/-! ## The pending list split by key -/

theorem vals_cons_same {k : GoString} {i : KIn} (h : i.k = k) (p : List KIn) :
    vals k (i :: p) = i.v :: vals k p := by
  simp [vals, h]

theorem vals_cons_other {k : GoString} {i : KIn} (h : i.k ≠ k) (p : List KIn) :
    vals k (i :: p) = vals k p := by
  simp [vals, h]

theorem vals_append (k : GoString) (p q : List KIn) : vals k (p ++ q) = vals k p ++ vals k q := by
  simp [vals, List.filter_append]

theorem vals_map_mk (k k' : GoString) (R : List GoString) :
    vals k' (R.map (mk k)) = if k = k' then R else [] := by
  induction R with
  | nil => split <;> rfl
  | cons v R ih =>
    simp only [List.map_cons]
    by_cases h : k = k'
    · rw [vals_cons_same (by simp [mk, h]), ih]; simp [h, mk]
    · rw [vals_cons_other (by simp [mk, h]), ih]; simp [h]

theorem vals_filter_ne (k k' : GoString) (p : List KIn) :
    vals k' (p.filter (fun i => decide (i.k ≠ k))) = if k' = k then [] else vals k' p := by
  unfold vals
  rw [List.filter_filter]
  split
  · subst_vars
    rw [List.filter_eq_nil_iff.2]; · rfl
    intro a _; simp
  · congr 1
    apply List.filter_congr
    intro a _
    by_cases ha : a.k = k' <;> simp [ha] <;> intro h <;> simp_all

theorem vals_put (c : Cfg) (k : GoString) (σ : Option GoString) (R : List GoString) (k' : GoString) :
    vals k' (put c k σ R).pend = if k' = k then R else vals k' c.pend := by
  simp only [put, vals_append, vals_map_mk, vals_filter_ne]
  by_cases h : k' = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem st_put (c : Cfg) (k : GoString) (σ : Option GoString) (R : List GoString) (k' : GoString) :
    (put c k σ R).st k' = if k' = k then σ else c.st k' := rfl

theorem allPuts_put {c : Cfg} (hc : allPuts c) (k : GoString) (σ : Option GoString)
    (R : List GoString) : allPuts (put c k σ R) := by
  intro i hi
  simp only [put, List.mem_append, List.mem_map, List.mem_filter] at hi
  rcases hi with ⟨v, -, rfl⟩ | ⟨hi, -⟩
  · rfl
  · exact hc i hi

theorem mk_eta {i : KIn} (h : i.put = true) : mk i.k i.v = i := by
  obtain ⟨p, k, v⟩ := i; simp at h; subst h; rfl

/-- An all-puts pending list is its key-`k` puts and the others. -/
theorem pend_split {c : Cfg} (hc : allPuts c) (k : GoString) :
    c.pend.Perm ((vals k c.pend).map (mk k) ++ c.pend.filter (fun i => decide (i.k ≠ k))) := by
  have : ∀ p : List KIn, (∀ i ∈ p, i.put = true) →
      p.Perm ((vals k p).map (mk k) ++ p.filter (fun i => decide (i.k ≠ k))) := by
    intro p
    induction p with
    | nil => intro; simp [vals]
    | cons i p ih =>
      intro hp
      have hi := hp i List.mem_cons_self
      have ih := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
      by_cases h : i.k = k
      · rw [vals_cons_same h]
        simp only [List.map_cons, List.filter_cons, h, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.cons_append]
        rw [← h, mk_eta hi]; rw [h]
        exact ih.cons i
      · rw [vals_cons_other h]
        simp only [List.filter_cons, ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte]
        exact ih.cons i |>.trans List.perm_middle.symm
  exact this c.pend hc

/-- `c` is `put c k` of its own key-`k` state and values, up to the order of its pending list. -/
theorem reach_put_self {c : Cfg} (hc : allPuts c) (k : GoString) :
    PReach kvB (put c k (c.st k) (vals k c.pend)) c := by
  have hst : (put c k (c.st k) (vals k c.pend)).st = c.st := by
    funext k'; simp only [st_put]; split <;> simp_all
  have h := PSilent.perm (P := kvB) (put c k (c.st k) (vals k c.pend)) c.pend (pend_split hc k)
  rw [hst] at h
  exact .single h

theorem put_put (c : Cfg) (k : GoString) (σ σ' : Option GoString) (R R' : List GoString) :
    put (put c k σ R) k σ' R' = put c k σ' R' := by
  simp only [put, PCfg.mk.injEq]
  constructor
  · funext k'; split <;> simp_all
  · congr 1
    rw [List.filter_append, List.filter_filter]
    have : (R.map (mk k)).filter (fun i => decide (i.k ≠ k)) = [] := by
      rw [List.filter_eq_nil_iff]; intro a ha; simp [List.mem_map] at ha
      obtain ⟨v, -, rfl⟩ := ha; simp [mk]
    rw [this, List.nil_append]
    apply List.filter_congr; intro a _; simp

/-- A pending put at the head of key `k`'s values takes effect. -/
theorem silent_head (c : Cfg) (k : GoString) (σ : Option GoString) (v : GoString)
    (L : List GoString) : PSilent kvB (put c k σ (v :: L)) (put c k (some v) L) := by
  have h := PSilent.apply (P := kvB) (put c k σ (v :: L)) (mk k v) (by simp [put])
  have he : (⟨(kvB.step (mk k v) (put c k σ (v :: L)).st).1,
      (put c k σ (v :: L)).pend.erase (mk k v)⟩ : Cfg) = put c k (some v) L := by
    simp only [put, kvB, mk, List.map_cons, List.cons_append, ↓reduceIte, PCfg.mk.injEq]
    constructor
    · funext k'; split <;> rfl
    · exact List.erase_cons_head _ _
  rw [he] at h; exact h

theorem reach_list (c : Cfg) (k : GoString) (x : GoString) (R : List GoString) :
    ∀ (D : List GoString) (σ : Option GoString),
      PReach kvB (put c k σ (D ++ x :: R)) (put c k (some x) R)
  | [], σ => .single (silent_head c k σ x R)
  | d :: D, σ => by
    refine .step (silent_head c k σ d (D ++ x :: R)) ?_
    exact reach_list c k x R D (some d)

/-- **The workhorse**: from `put c k σ P`, pending `x` takes effect last, leaving any `R ⊆ P - x`
pending. -/
theorem reach_to (c : Cfg) (k : GoString) (σ : Option GoString) {P R : List GoString}
    {x : GoString} (hx : x ∈ P) (hR : R.Subperm (P.erase x)) :
    PReach kvB (put c k σ P) (put c k (some x) R) := by
  obtain ⟨R₀, hp, hs⟩ := hR
  obtain ⟨D, hD⟩ : ∃ D, (P.erase x).Perm (R ++ D) := by
    obtain ⟨D, hD⟩ := hs.exists_perm_append
    exact ⟨D, hD.trans (hp.append_right D)⟩
  have hP : P.Perm (D ++ x :: R) :=
    (List.perm_cons_erase hx).trans ((hD.cons x).trans
      ((List.perm_append_comm.cons x).trans List.perm_middle.symm))
  have h1 : PSilent kvB (put c k σ P) (put c k σ (D ++ x :: R)) := by
    have := PSilent.perm (P := kvB) (put c k σ P) (put c k σ (D ++ x :: R)).pend
      ((hP.map (mk k)).symm.append_right _)
    simpa [put] using this
  exact .step h1 (reach_list c k x R D σ)

/-! ## The set is closed under late effects -/

theorem vals_erase {p : List KIn} (hp : ∀ j ∈ p, j.put = true) {i : KIn} (hi : i.put = true)
    (k : GoString) :
    vals k (p.erase i) = if i.k = k then (vals k p).erase i.v else vals k p := by
  induction p with
  | nil => simp [vals]
  | cons j p ih =>
    have hj := hp j List.mem_cons_self
    have ih := ih (fun j' hj' => hp j' (List.mem_cons_of_mem _ hj'))
    by_cases hji : j = i
    · subst hji
      rw [List.erase_cons_head]
      by_cases h : j.k = k
      · rw [vals_cons_same h]; simp [h]
      · rw [vals_cons_other h]; simp [h]
    · rw [List.erase_cons_tail (by simpa using hji)]
      by_cases h : j.k = k
      · rw [vals_cons_same h, vals_cons_same h, ih]
        by_cases h' : i.k = k
        · simp only [h', ↓reduceIte]
          rw [List.erase_cons_tail]
          intro hv
          apply hji
          obtain ⟨jp, jk, jv⟩ := j
          obtain ⟨ip, ik, iv⟩ := i
          simp_all
        · simp [h']
      · rw [vals_cons_other h, vals_cons_other h, ih]

theorem mSet_silent {M : GoString → Ent} {c c' : Cfg} (hs : PSilent kvB c c') (hc : mSet M c) :
    mSet M c' := by
  obtain ⟨hp, he⟩ := hc
  cases hs with
  | apply i hi =>
    have hip := hp i hi
    refine ⟨fun j hj => hp j (List.mem_of_mem_erase hj), fun k => ?_⟩
    simp only [kvB, hip, ↓reduceIte]
    rw [vals_erase hp hip k]
    by_cases h : i.k = k
    · subst h; simp only [↓reduceIte]
      exact eSet_apply (he i.k) (by
        simp only [vals, List.mem_map, List.mem_filter]; exact ⟨i, ⟨hi, by simp⟩, rfl⟩)
    · simp only [h, ↓reduceIte, Ne.symm h]; exact he k
  | perm p hperm =>
    refine ⟨fun j hj => hp j (hperm.subset hj), fun k => ?_⟩
    exact eSet_perm ((hperm.filter _).map _).symm (he k)

theorem mSet_closed (M : GoString → Ent) : PSet.Closed kvB (mSet M) := by
  intro c c' hc hr
  induction hr with
  | refl => exact hc
  | step hs _ ih => exact ih (mSet_silent hs hc)

/-! ## `pSeq`'s step on a closed set -/

theorem pSeq_some {S T : PSet Store KIn} {i : KIn} {a : Ans KOut} (hS : PSet.Closed kvB S)
    (hT : PSet.Closed kvB T)
    (hsound : ∀ c c₁, S c → PStep kvB c i a c₁ → T c₁)
    (hcomp : ∀ c', T c' → ∃ c c₁, S c ∧ PStep kvB c i a c₁ ∧ PReach kvB c₁ c')
    (hne : ∃ c', T c') : (pSeq kvB).step S (i, a) = some T := by
  have heq : ppost kvB S i a = T := by
    funext c'
    apply propext
    constructor
    · rintro ⟨c₀, c, c₁, h0, hr0, hst, hr1⟩
      exact hT _ _ (hsound c c₁ (hS _ _ h0 hr0) hst) hr1
    · intro h
      obtain ⟨c, c₁, hc, hst, hr⟩ := hcomp c' h
      exact ⟨c, c, c₁, hc, .refl _, hst, hr⟩
  obtain ⟨c', hc'⟩ := hne
  simp only [pSeq]
  rw [if_pos ⟨c', heq ▸ hc'⟩, heq]

theorem pSeq_none {S : PSet Store KIn} {i : KIn} {a : Ans KOut} (hS : PSet.Closed kvB S)
    (h : ∀ c c₁, S c → ¬ PStep kvB c i a c₁) : (pSeq kvB).step S (i, a) = none := by
  simp only [pSeq]
  rw [if_neg]
  rintro ⟨c', c₀, c, c₁, h0, hr0, hst, -⟩
  exact h c c₁ (hS _ _ h0 hr0) hst

/-! ## Key-local steps -/

theorem mSet_put {M : GoString → Ent} {c : Cfg} (hc : allPuts c) {k : GoString}
    (ho : ∀ k', k' ≠ k → eSet (M k') (c.st k') (vals k' c.pend)) {σ : Option GoString}
    {R : List GoString} (h : eSet (M k) σ R) : mSet M (put c k σ R) := by
  refine ⟨allPuts_put hc k σ R, fun k' => ?_⟩
  rw [vals_put, st_put]
  by_cases hk : k' = k
  · subst hk; simpa using h
  · simp only [hk, ↓reduceIte]; exact ho k' hk

theorem upd_same (M : GoString → Ent) (k : GoString) (e : Ent) : upd M k e k = e := by simp [upd]

theorem upd_other (M : GoString → Ent) {k k' : GoString} (e : Ent) (h : k' ≠ k) :
    upd M k e k' = M k' := by simp [upd, h]

/-- A configuration of the next set, from one of `M`'s with key `k` changed. -/
theorem mSet_upd_of {M : GoString → Ent} {c c₁ : Cfg} (hc : mSet M c) {k : GoString} {e : Ent}
    (hp : allPuts c₁) (hst : ∀ k', k' ≠ k → c₁.st k' = c.st k')
    (hv : ∀ k', k' ≠ k → vals k' c₁.pend = vals k' c.pend)
    (h : eSet e (c₁.st k) (vals k c₁.pend)) : mSet (upd M k e) c₁ := by
  refine ⟨hp, fun k' => ?_⟩
  by_cases hk : k' = k
  · subst hk; rw [upd_same]; exact h
  · rw [upd_other _ _ hk, hst k' hk, hv k' hk]; exact hc.2 k'

/-- The other keys of a configuration of the next set are `M`'s. -/
theorem others_of_upd {M : GoString → Ent} {c : Cfg} {k : GoString} {e : Ent}
    (hc : mSet (upd M k e) c) : ∀ k', k' ≠ k → eSet (M k') (c.st k') (vals k' c.pend) := by
  intro k' hk; have := hc.2 k'; rwa [upd_other _ _ hk] at this

theorem put_err_put (c : Cfg) {i : KIn} (hp : i.put = true) (σ : Option GoString)
    (R : List GoString) :
    (⟨(put c i.k σ R).st, i :: (put c i.k σ R).pend⟩ : Cfg) = put c i.k σ (i.v :: R) := by
  simp only [put, List.map_cons, List.cons_append, mk_eta hp]

theorem put_ok_put (c : Cfg) {i : KIn} (hp : i.put = true) (σ : Option GoString)
    (R : List GoString) :
    (⟨(kvB.step i (put c i.k σ R).st).1, (put c i.k σ R).pend⟩ : Cfg) = put c i.k (some i.v) R := by
  simp only [put, kvB, hp, ↓reduceIte, PCfg.mk.injEq, and_true]
  funext k'; split <;> rfl

theorem get_ok (c : Cfg) {i : KIn} (hp : i.put = false) :
    (kvB.step i c.st) = (c.st, ans (c.st i.k)) := by
  simp only [kvB, hp, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, true_and]
  cases c.st i.k <;> rfl

theorem reach_end {c' : Cfg} (hc : allPuts c') {k x : GoString} (hx : c'.st k = some x)
    (σ : Option GoString) {P : List GoString} (hxP : x ∈ P)
    (hR : (vals k c'.pend).Subperm (P.erase x)) : PReach kvB (put c' k σ P) c' :=
  (reach_to c' k σ hxP hR).trans (hx ▸ reach_put_self hc k)

theorem eSet_known_all (e : Ent) : eSet e e.known e.all :=
  .inl ⟨rfl, List.sublist_append_right _ _ |>.subperm, List.Subperm.refl _⟩

theorem snoc_sub_cons {A B : List GoString} (v : GoString) (h : A.Subperm B) :
    (A ++ [v]).Subperm (v :: B) :=
  (List.perm_append_singleton v A).subperm_right.2 ((List.subperm_cons v).2 h)

theorem cons_sub_snoc {A B : List GoString} (v : GoString) (h : A.Subperm B) :
    (v :: A).Subperm (B ++ [v]) :=
  (List.perm_append_singleton v B).subperm_left.2 ((List.subperm_cons v).2 h)

theorem snoc_erase (A : List GoString) (v : GoString) : ((A ++ [v]).erase v).Perm A := by
  have := (List.perm_append_singleton v A).erase v
  rwa [List.erase_cons_head] at this

/-! ## The steps, case by case -/

section steps
variable {M : GoString → Ent}

/-- A put of unknown outcome: pending (`New`). -/
theorem step_errW (hne : ∃ c, mSet M c) {i : KIn} (hp : i.put = true) :
    (pSeq kvB).step (mSet M) (i, .err) =
      some (mSet (upd M i.k ⟨(M i.k).f, (M i.k).v, (M i.k).old, (M i.k).new ++ [i.v]⟩)) := by
  obtain ⟨e, he⟩ : ∃ e, M i.k = e := ⟨_, rfl⟩
  rw [he]
  have hall : Ent.all (⟨e.f, e.v, e.old, e.new ++ [i.v]⟩ : Ent) = e.all ++ [i.v] := by simp [Ent.all]
  have sound : ∀ c c₁, mSet M c → PStep kvB c i .err c₁ → mSet (upd M i.k (⟨e.f, e.v, e.old, e.new ++ [i.v]⟩ : Ent)) c₁ := by
    intro c c₁ hc hs
    cases hs with
    | errW _ _ =>
      refine mSet_upd_of hc ?_ (fun _ _ => rfl) (fun k' hk => vals_cons_other (Ne.symm hk) _) ?_
      · intro j hj; rcases List.mem_cons.1 hj with rfl | hj; exact hp; exact hc.1 j hj
      · rw [vals_cons_same rfl]
        rcases (he ▸ hc.2 i.k) with ⟨h1, h2, h3⟩ | ⟨x, hx, h1, h2⟩
        · refine .inl ⟨by simp [h1, Ent.known], snoc_sub_cons _ h2, ?_⟩
          rw [hall]; exact cons_sub_snoc _ h3
        · refine .inr ⟨x, by rw [hall]; exact List.mem_append_left _ hx, h1, ?_⟩
          rw [hall, List.erase_append_left _ hx]
          exact cons_sub_snoc _ h2
    | errR h _ => simp [kvB, hp] at h
  refine pSeq_some (mSet_closed M) (mSet_closed _) sound ?_ ?_
  · intro c' hc'
    have ho := others_of_upd hc'
    have hk := hc'.2 i.k
    rw [upd_same] at hk
    rcases hk with ⟨h1, h2, h3⟩ | ⟨x, hx, h1, h2⟩
    · -- the new put still pending, the key's state the known one
      have hv : i.v ∈ vals i.k c'.pend :=
        h2.subset (List.mem_append_right _ (List.mem_singleton_self _))
      refine ⟨put c' i.k (c'.st i.k) ((vals i.k c'.pend).erase i.v),
        put c' i.k (c'.st i.k) (i.v :: (vals i.k c'.pend).erase i.v), ?_, ?_, ?_⟩
      · refine mSet_put hc'.1 ho ?_
        rw [he]
        refine .inl ⟨by simpa [Ent.known] using h1, ?_, ?_⟩
        · exact (snoc_erase _ _).subperm_right.1 (h2.erase i.v)
        · have := h3.erase i.v
          rw [hall] at this
          exact (snoc_erase _ _).subperm_left.1 this
      · rw [← put_err_put c' hp]; exact .errW _ _ hp rfl
      · have hst : (put c' i.k (c'.st i.k) (i.v :: (vals i.k c'.pend).erase i.v)).st = c'.st := by
          funext k'; simp only [st_put]; split <;> simp_all
        have := PSilent.perm (P := kvB) (put c' i.k (c'.st i.k) (i.v :: (vals i.k c'.pend).erase i.v))
          c'.pend (by
            refine (pend_split hc'.1 i.k).trans ?_
            exact ((List.perm_cons_erase hv).map _).append_right _)
        rw [hst] at this
        exact .single this
    · -- some pending put took effect last
      refine ⟨put c' i.k e.known e.all, put c' i.k e.known (i.v :: e.all), ?_, ?_, ?_⟩
      · refine mSet_put hc'.1 ho ?_
        rw [he]; exact eSet_known_all e
      · rw [← put_err_put c' hp]; exact .errW _ _ hp rfl
      · refine reach_end hc'.1 h1 _ ?_ ?_
        · rw [hall] at hx; exact (List.perm_append_singleton i.v e.all).subset hx
        · rw [hall] at h2
          exact ((List.perm_append_singleton _ _).erase x).subperm_left.1 h2
  · obtain ⟨c, hc⟩ := hne
    exact ⟨_, sound c _ hc (.errW c i hp rfl)⟩

/-- A get of unknown outcome: nothing changes. -/
theorem step_errR (hne : ∃ c, mSet M c) {i : KIn} (hp : i.put = false) :
    (pSeq kvB).step (mSet M) (i, .err) = some (mSet M) := by
  refine pSeq_some (mSet_closed M) (mSet_closed M) ?_ ?_ hne
  · intro c c₁ hc hs
    cases hs with
    | errW h _ => simp [kvB, hp] at h
    | errR _ _ => exact hc
  · intro c' hc'
    exact ⟨c', c', hc', .errR c' i hp rfl, .refl _⟩

end steps

end Perennial.raxos.pure
