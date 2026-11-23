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

end Perennial.raxos.pure
