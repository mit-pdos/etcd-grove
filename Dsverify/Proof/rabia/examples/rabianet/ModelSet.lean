/-
The key-value map with pending puts, pure (notes/dsv-rabia.md; as paxos's `ModelSet.lean` for its
register): the store `kvB` (linkv's pending-writes store of the key-value map `kv`, on bounded
inputs `KIn` and outputs `KOut`), the set of configurations a model state (`kit.go`'s `State`: per
key its value `Cur`, its old pending puts `Old`, its new ones `Pend`) stands for (`kvSet`), and
**`stepG_pSeq`**: `step` (kit.go) on the state is the pending model's step on the set.

Per key, with `cur` the value, `O` the old and `N` the new pending puts, the configurations are
those reached from `cur` with `N` and some of `O` pending (an old put may have taken effect before
`cur` was set, and been overwritten) by pending puts taking effect (`keyOk`). An answered put sets
the value and makes every pending put old; an observed pending value does the same; an unknown
put is a new pending one.
-/
module

public import Dsverify.Proof.rabia.Core.Ghost
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.PendModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.rabia.examples.rabianet

open EtcdGrove EtcdGrove.linkv Perennial.rabia Perennial.rabia.model

/-! ## The store -/

/-- A put's value's length (`0` for a get). -/
def valLen : KvInput GoString GoString → Nat
  | .put _ v => v.length
  | .get _ => 0

/-- The inputs: the workload's (`inputOk`), with a value below `2^40` bytes. -/
def inB (i : KvInput GoString GoString) : Prop := inputOk i ∧ valLen i < 2 ^ 40

abbrev KIn := {i : KvInput GoString GoString // inB i}

/-- `KIn`'s `BEq` is its decidable equality's (the instance linkv's pending lists erase with). -/
@[reducible] instance (priority := high) KIn.beq : BEq KIn := instBEqOfDecidableEq

/-- A bounded value: not empty (a get's answer cannot tell it from none) and below `2^62`. -/
def valB (v : GoString) : Prop := v ≠ [] ∧ v.length < 2 ^ 62

/-- The outputs: a put's, a get's of no value or of a bounded value. -/
def outB : KvOutput GoString → Prop
  | .done => True
  | .got none => True
  | .got (some v) => valB v

abbrev KOut := {o : KvOutput GoString // outB o}

abbrev KSt := (kv GoString GoString).State

open Classical in
/-- An output as a bounded one (`got none` if it is not). -/
def clampO (o : KvOutput GoString) : KOut := if h : outB o then ⟨o, h⟩ else ⟨.got none, trivial⟩

/-- `σ` with `k` at `a`. -/
def upd (σ : KSt) (k : GoString) (a : Option GoString) : KSt := fun k' => if k' = k then a else σ k'

/-- **The key-value map with failed puts** (linkv's pending-writes store): a put is a write. -/
def kvB : PendSpec KSt KIn KOut where
  init := fun _ => none
  step i σ := match i.1 with
    | .get k => (σ, clampO (.got (σ k)))
    | .put k v => (upd σ k (some v), clampO .done)
  isWrite i := match i.1 with
    | .put _ _ => true
    | .get _ => false

theorem kvB_step_get (i : KIn) (k : GoString) (h : i.1 = .get k) (σ : KSt) :
    kvB.step i σ = (σ, clampO (.got (σ k))) := by
  simp only [kvB, h]

theorem kvB_step_put (i : KIn) (k v : GoString) (h : i.1 = .put k v) (σ : KSt) :
    kvB.step i σ = (upd σ k (some v), clampO .done) := by
  simp only [kvB, h]

theorem clampO_of (o : KvOutput GoString) (h : outB o) : clampO o = ⟨o, h⟩ := by
  unfold clampO; rw [dif_pos h]

/-- The store's step is `kv`'s (for the outputs a reachable state gives). -/
theorem kvB_kv (i : KIn) (σ : KSt) :
    (kv GoString GoString).step σ i.1 (kvB.step i σ).1 (kvB.step i σ).2.1 ∨
    ∃ o, (kv GoString GoString).step σ i.1 (kvB.step i σ).1 o ∧ clampO o = (kvB.step i σ).2 := by
  right
  rcases i with ⟨i, hi⟩
  cases i with
  | get k => exact ⟨.got (σ k), ⟨rfl, rfl⟩, by simp [kvB]⟩
  | put k v => exact ⟨.done, ⟨by funext k'; simp [kvB, upd], rfl⟩, by simp [kvB]⟩

/-! ## The model's state -/

/-- One key's entry (kit.go's `Entry`): its key, value (`[]`: none), old and new pending puts. -/
structure EntV where
  k : GoString
  cur : GoString
  old : List GoString
  new : List GoString

/-- A value string as an optional value (`""`: none). -/
def optS (s : GoString) : Option GoString := if s = [] then none else some s

/-- kit.go's `find`: `k`'s first entry, or an empty one. -/
def findE (es : List EntV) (k : GoString) : EntV :=
  (es.find? (fun e => decide (e.k = k))).getD ⟨k, [], [], []⟩

/-- kit.go's `set`: every entry of `e`'s key replaced by `e`, or `e` added. -/
def setE (es : List EntV) (e : EntV) : List EntV :=
  if es.any (fun x => decide (x.k = e.k)) then es.map (fun x => if x.k = e.k then e else x)
  else es ++ [e]

/-- kit.go's `step` on the pure state: its verdict and next entries. -/
def stepG (es : List EntV) (i : KIn) (a : Ans KOut) : Bool × List EntV :=
  match i.1, a with
  | .put k v, .err => (true, setE es ⟨k, (findE es k).cur, (findE es k).old, (findE es k).new ++ [v]⟩)
  | .get _, .err => (true, es)
  | .put k v, .ok o => (decide (o.1 = .done),
      setE es ⟨k, v, (findE es k).old ++ (findE es k).new, []⟩)
  | .get k, .ok o =>
    match o.1 with
    | .done => (false, es)
    | .got w =>
      if w.getD [] = (findE es k).cur then (true, es)
      else if w.getD [] ≠ [] ∧ w.getD [] ∈ (findE es k).old ++ (findE es k).new then
        (true, setE es ⟨k, w.getD [], ((findE es k).old ++ (findE es k).new).erase (w.getD []), []⟩)
      else (false, es)

/-- One key's configurations (see the file header): its value `a` and its pending puts' values
`p`. -/
def keyOk (cur : Option GoString) (O N : List GoString) (a : Option GoString) (p : List GoString) :
    Prop :=
  (a = cur ∧ ∃ O', O'.Subperm O ∧ p.Perm (O' ++ N)) ∨
    (∃ x ∈ O ++ N, a = some x ∧ p.Subperm ((O ++ N).erase x))

def entOk (e : EntV) (a : Option GoString) (p : List GoString) : Prop :=
  keyOk (optS e.cur) e.old e.new a p

/-- An input's key. -/
def keyOf (i : KIn) : GoString := match i.1 with
  | .put k _ => k
  | .get k => k

def isPut (i : KIn) : Prop := ∃ k v, i.1 = .put k v

/-- A pending put's value at `k`. -/
def valAt (k : GoString) (i : KIn) : Option GoString := match i.1 with
  | .put k' v => if k' = k then some v else none
  | .get _ => none

/-- The values of the pending puts at `k`. -/
def vals (k : GoString) (l : List KIn) : List GoString := l.filterMap (valAt k)

/-- **The configurations the model's state stands for**. -/
def kvSet (es : List EntV) : PSet KSt KIn := fun c =>
  (∀ i ∈ c.pend, isPut i) ∧ ∀ k, entOk (findE es k) (c.st k) (vals k c.pend)

/-- The model's states are well formed: every pending value makes a valid put at its key, every
value is bounded. -/
def WF (es : List EntV) : Prop :=
  ∀ k, (∀ v ∈ (findE es k).old ++ (findE es k).new, inB (.put k v)) ∧
    ((findE es k).cur = [] ∨ valB (findE es k).cur)

/-! ## Lists of values -/

section lists

theorem optS_nil : optS [] = none := by simp [optS]

theorem optS_ne {s : GoString} (h : s ≠ []) : optS s = some s := by simp [optS, h]

theorem optS_inj {s t : GoString} (h : optS s = optS t) : s = t := by
  unfold optS at h
  by_cases hs : s = [] <;> by_cases ht : t = [] <;> simp_all

theorem valAt_some {k v : GoString} {i : KIn} (h : valAt k i = some v) : i.1 = .put k v := by
  rcases i with ⟨i, hi⟩
  cases i with
  | get k' => simp [valAt] at h
  | put k' v' =>
    simp only [valAt] at h
    split at h
    · cases h; subst_vars; rfl
    · cases h

theorem valAt_inj {k v : GoString} {i j : KIn} (hi : valAt k i = some v) (hj : valAt k j = some v) :
    i = j := Subtype.ext ((valAt_some hi).trans (valAt_some hj).symm)

theorem valAt_put (i : KIn) (k v : GoString) (h : i.1 = .put k v) (k' : GoString) :
    valAt k' i = if k = k' then some v else none := by
  simp only [valAt, h]

theorem vals_nil (k : GoString) : vals k [] = [] := rfl

theorem vals_cons (k : GoString) (i : KIn) (l : List KIn) :
    vals k (i :: l) = (match valAt k i with | some v => v :: vals k l | none => vals k l) := by
  simp only [vals, List.filterMap_cons]
  cases valAt k i <;> rfl

theorem vals_append (k : GoString) (l₁ l₂ : List KIn) : vals k (l₁ ++ l₂) = vals k l₁ ++ vals k l₂ := by
  simp [vals, List.filterMap_append]

theorem vals_perm (k : GoString) {l₁ l₂ : List KIn} (h : l₁.Perm l₂) : (vals k l₁).Perm (vals k l₂) :=
  h.filterMap _

theorem mem_vals {k v : GoString} {l : List KIn} (h : v ∈ vals k l) : ∃ i ∈ l, valAt k i = some v := by
  simp only [vals, List.mem_filterMap] at h
  exact h

/-- The values at `k` after erasing a pending put `i`. -/
theorem vals_erase (k : GoString) (l : List KIn) (i : KIn) (k0 v : GoString)
    (hi : i.1 = .put k0 v) :
    vals k (l.erase i) = if k0 = k then (vals k l).erase v else vals k l := by
  induction l with
  | nil => by_cases h : k0 = k <;> simp [vals, h]
  | cons j l ih =>
    by_cases hji : j = i
    · subst hji
      have hv := valAt_put j k0 v hi k
      rw [List.erase_cons_head, vals_cons, hv]
      by_cases h : k0 = k
      · simp [h]
      · simp [h]
    · rw [List.erase_cons_tail (by simpa using hji), vals_cons, vals_cons, ih]
      rcases hj : valAt k j with _ | w
      · rfl
      · dsimp only
        by_cases h : k0 = k
        · simp only [h, ↓reduceIte]
          have hwv : w ≠ v := by
            intro hw; subst hw
            exact hji (valAt_inj hj (by rw [valAt_put i k0 w hi k, if_pos h]))
          rw [List.erase_cons_tail (by simpa using hwv)]
        · simp [h]

theorem allPut_cons {i : KIn} {l : List KIn} (h : ∀ j ∈ i :: l, isPut j) : isPut i ∧ ∀ j ∈ l, isPut j :=
  ⟨h i (by simp), fun j hj => h j (by simp [hj])⟩

/-- A list of pending puts' count of a put `x` is its value's count at its key. -/
theorem count_vals (l : List KIn) (hl : ∀ j ∈ l, isPut j) (x : KIn) (k v : GoString)
    (hx : x.1 = .put k v) : l.count x = (vals k l).count v := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    obtain ⟨⟨kj, vj, hj⟩, hl'⟩ := allPut_cons hl
    rw [List.count_cons, vals_cons, valAt_put j kj vj hj k, ih hl']
    by_cases hjx : j = x
    · subst hjx
      rw [hj] at hx
      cases hx
      simp
    · have hne : ¬ (kj = k ∧ vj = v) := by
        rintro ⟨rfl, rfl⟩; exact hjx (Subtype.ext (hj.trans hx.symm))
      by_cases hk : kj = k
      · have hvne : vj ≠ v := fun h => hne ⟨hk, h⟩
        simp [hk, List.count_cons, hvne, hjx]
      · simp [hk, hjx]

/-- Two lists of pending puts with the same values at every key are permutations. -/
theorem perm_of_vals {l₁ l₂ : List KIn} (h₁ : ∀ j ∈ l₁, isPut j) (h₂ : ∀ j ∈ l₂, isPut j)
    (h : ∀ k, (vals k l₁).Perm (vals k l₂)) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro x
  rcases x with ⟨x, hx⟩
  cases x with
  | put k v =>
    rw [count_vals l₁ h₁ _ k v rfl, count_vals l₂ h₂ _ k v rfl]
    exact (List.perm_iff_count.1 (h k)) v
  | get k =>
    have hz : ∀ l : List KIn, (∀ j ∈ l, isPut j) → l.count ⟨.get k, hx⟩ = 0 := by
      intro l hl
      rw [List.count_eq_zero]
      intro hm
      obtain ⟨k', v', h'⟩ := hl _ hm
      cases h'
    rw [hz l₁ h₁, hz l₂ h₂]

/-- A proper sub-multiset misses some element. -/
theorem subperm_proper {p L : List GoString} (h : p.Subperm L) (hn : ¬ p.Perm L) :
    ∃ x ∈ L, p.Subperm (L.erase x) := by
  rw [List.perm_iff_count] at hn
  obtain ⟨x, hx⟩ := Classical.not_forall.1 hn
  have hle := (List.subperm_ext_iff.1 h)
  have hlt : p.count x < L.count x := by
    by_cases hxp : x ∈ p
    · exact Nat.lt_of_le_of_ne (hle x hxp) hx
    · rw [List.count_eq_zero_of_not_mem hxp] at hx ⊢
      exact Nat.pos_of_ne_zero (Ne.symm hx)
  have hxL : x ∈ L := List.count_pos_iff.1 (by omega)
  refine ⟨x, hxL, List.subperm_ext_iff.2 fun y hy => ?_⟩
  rw [List.count_erase]
  by_cases hxy : x = y
  · subst hxy; simp; omega
  · simp [hxy]; exact hle y hy

end lists

/-! ## Local reachability: one key -/

section local_

/-- One key's configurations reached by its pending puts taking effect (up to the order of the
pending ones). -/
inductive LReach : Option GoString × List GoString → Option GoString × List GoString → Prop where
  | perm (a : Option GoString) {p p' : List GoString} (h : p.Perm p') : LReach (a, p) (a, p')
  | step (a : Option GoString) {p : List GoString} {v : GoString} (t : Option GoString × List GoString)
      (h : v ∈ p) (r : LReach (some v, p.erase v) t) : LReach (a, p) t

/-- From any value with `L` pending, `x ∈ L` taking effect last leaves any part `p` of the rest. -/
theorem lreach_last (a : Option GoString) {L : List GoString} {x : GoString} (hx : x ∈ L)
    {p : List GoString} (hp : p.Subperm (L.erase x)) : LReach (a, L) (some x, p) := by
  obtain ⟨l, hlp, hls⟩ := hp
  obtain ⟨D, hD⟩ := hls.exists_perm_append
  have hD' : (L.erase x).Perm (p ++ D) := hD.trans (hlp.append_right D)
  have hL : L.Perm (x :: (p ++ D)) := (List.perm_cons_erase hx).trans (.cons x hD')
  suffices H : ∀ (D : List GoString) (a : Option GoString) (M : List GoString),
      M.Perm (x :: (p ++ D)) → LReach (a, M) (some x, p) from H D a L hL
  intro D
  induction D with
  | nil =>
    intro a M hM
    have hxM : x ∈ M := hM.symm.subset (by simp)
    refine .step a _ hxM (.perm _ ?_)
    have := (hM.erase x)
    simpa using this
  | cons d D ih =>
    intro a M hM
    have hdM : d ∈ M := hM.symm.subset (by simp)
    refine .step a _ hdM (ih _ _ ?_)
    have h1 := hM.erase d
    have h2 : (x :: (p ++ d :: D)).Perm (d :: (x :: (p ++ D))) := by
      have : (p ++ d :: D).Perm (d :: (p ++ D)) := List.perm_middle
      exact (List.Perm.cons x this).trans (List.Perm.swap d x _)
    exact h1.trans (by simpa using h2.erase d)

theorem lreach_perm_left : ∀ {s t : Option GoString × List GoString}, LReach s t →
    ∀ p, p.Perm s.2 → LReach (s.1, p) t := by
  intro s t r
  induction r with
  | perm a h => intro p hp; exact .perm a (hp.trans h)
  | step a t hv _ ih => intro p hp; exact .step a t (hp.symm.subset hv) (ih _ (hp.erase _))

/-- One key's configurations are closed under a pending put taking effect. -/
theorem keyOk_apply {cur : Option GoString} {O N : List GoString} {a : Option GoString}
    {p : List GoString} {v : GoString} (h : keyOk cur O N a p) (hv : v ∈ p) :
    keyOk cur O N (some v) (p.erase v) := by
  right
  rcases h with ⟨-, O', hO', hp⟩ | ⟨x, hx, -, hp⟩
  · have hvO : v ∈ O' ++ N := hp.subset hv
    refine ⟨v, ?_, rfl, ?_⟩
    · rcases List.mem_append.1 hvO with h | h
      · exact List.mem_append_left _ (hO'.subset h)
      · exact List.mem_append_right _ h
    · exact (hp.erase v).subperm.trans (List.Subperm.erase v ((List.subperm_append_right N).2 hO'))
  · have hv' : v ∈ (O ++ N).erase x := hp.subset hv
    refine ⟨v, (List.erase_subperm _ _).subset hv', rfl, ?_⟩
    have := List.Subperm.erase v hp
    rw [List.erase_comm] at this
    exact this.trans (List.erase_subperm _ _)

theorem keyOk_perm {cur : Option GoString} {O N : List GoString} {a : Option GoString}
    {p p' : List GoString} (h : keyOk cur O N a p) (hp : p.Perm p') : keyOk cur O N a p' := by
  rcases h with ⟨h1, O', hO', h2⟩ | ⟨x, hx, h1, h2⟩
  · exact .inl ⟨h1, O', hO', hp.symm.trans h2⟩
  · exact .inr ⟨x, hx, h1, hp.symm.subperm.trans h2⟩

theorem keyOk_lreach {cur : Option GoString} {O N : List GoString} {s t : Option GoString × List GoString}
    (r : LReach s t) (h : keyOk cur O N s.1 s.2) : keyOk cur O N t.1 t.2 := by
  induction r with
  | perm a hp => exact keyOk_perm h hp
  | step a t hv _ ih => exact ih (keyOk_apply h hv)

/-- A base configuration: the value, all pending. -/
theorem keyOk_base (cur : Option GoString) (O N : List GoString) : keyOk cur O N cur (O ++ N) :=
  .inl ⟨rfl, O, List.Subperm.refl _, .refl _⟩

/-- Every configuration is reached from a base one. -/
theorem keyOk_from_base {cur : Option GoString} {O N : List GoString} {a : Option GoString}
    {p : List GoString} (h : keyOk cur O N a p) (hn : ¬ (a = cur ∧ ∃ O', O'.Subperm O ∧ p.Perm (O' ++ N))) :
    LReach (cur, O ++ N) (a, p) := by
  rcases h with h | ⟨x, hx, rfl, hp⟩
  · exact absurd h hn
  · exact lreach_last cur hx hp

end local_

/-! ## Finding and setting entries -/

section entries

theorem find?_map_set (es : List EntV) (e : EntV) (k : GoString) :
    (es.map (fun x => if x.k = e.k then e else x)).find? (fun x => decide (x.k = k)) =
      if e.k = k then (if es.any (fun x => decide (x.k = e.k)) then some e else none)
      else es.find? (fun x => decide (x.k = k)) := by
  induction es with
  | nil => simp
  | cons x es ih =>
    simp only [List.map_cons, List.find?_cons, List.any_cons]
    by_cases hx : x.k = e.k
    · by_cases he : e.k = k
      · simp [hx, he]
      · have hk : ¬ x.k = k := fun h => he (hx ▸ h)
        simp only [hx, ↓reduceIte, he, decide_false] at ih ⊢
        simpa [hk] using ih
    · by_cases hk : x.k = k
      · have he : e.k ≠ k := fun h => hx (hk.trans h.symm)
        subst hk
        simp [hx, he]
      · simp only [hx, ↓reduceIte, hk, decide_false] at ih ⊢
        simpa using ih

theorem findE_setE (es : List EntV) (e : EntV) (k : GoString) :
    findE (setE es e) k = if e.k = k then e else findE es k := by
  unfold findE setE
  split
  · rename_i hany
    rw [find?_map_set]
    by_cases he : e.k = k
    · rw [if_pos he, if_pos hany]; simp [he]
    · simp only [if_neg he]
  · rename_i hany
    rw [List.find?_append]
    by_cases he : e.k = k
    · subst he
      have : es.find? (fun x => decide (x.k = e.k)) = none := by
        rw [List.find?_eq_none]
        intro x hx hxk
        apply hany
        rw [List.any_eq_true]
        exact ⟨x, hx, hxk⟩
      simp [this]
    · simp only [he, ↓reduceIte]
      cases es.find? (fun x => decide (x.k = k)) <;> simp [he]

theorem setE_k (es : List EntV) (e : EntV) (k : GoString) (hk : e.k = k) : findE (setE es e) k = e := by
  rw [findE_setE, if_pos hk]

theorem setE_ne (es : List EntV) (e : EntV) (k : GoString) (hk : e.k ≠ k) :
    findE (setE es e) k = findE es k := by
  rw [findE_setE, if_neg hk]

theorem findE_nil (k : GoString) : findE [] k = ⟨k, [], [], []⟩ := rfl

end entries

/-! ## The sets -/

section sets

abbrev Cfg := PCfg KSt KIn

theorem kvSet_silent {es : List EntV} {c c' : Cfg} (hs : PSilent kvB c c') (hc : kvSet es c) :
    kvSet es c' := by
  obtain ⟨hput, hk⟩ := hc
  cases hs with
  | apply i hi =>
    obtain ⟨k0, v, hiv⟩ := hput i hi
    refine ⟨fun j hj => hput j ((List.erase_subperm _ _).subset hj), fun k => ?_⟩
    rw [kvB_step_put i k0 v hiv]
    dsimp only
    rw [vals_erase k c.pend i k0 v hiv]
    unfold upd
    by_cases h : k = k0
    · subst h
      simp only [↓reduceIte]
      have hv : v ∈ vals k c.pend := by
        simp only [vals, List.mem_filterMap]
        exact ⟨i, hi, by rw [valAt_put i k v hiv k, if_pos rfl]⟩
      exact keyOk_apply (hk k) hv
    · have h' : ¬ k0 = k := fun e => h e.symm
      simp only [h, h', ↓reduceIte]
      exact hk k
  | perm p hp =>
    exact ⟨fun j hj => hput j (hp.subset hj), fun k => keyOk_perm (hk k) (vals_perm k hp).symm⟩

theorem kvSet_closed (es : List EntV) : PSet.Closed kvB (kvSet es) := by
  intro c c' hc hr
  induction hr with
  | refl => exact hc
  | step hs _ ih => exact ih (kvSet_silent hs hc)

theorem ppost_iff {S : PSet KSt KIn} (hS : PSet.Closed kvB S) (i : KIn) (a : Ans KOut) (c' : Cfg) :
    ppost kvB S i a c' ↔ ∃ c c₁, S c ∧ PStep kvB c i a c₁ ∧ PReach kvB c₁ c' := by
  constructor
  · rintro ⟨c₀, c, c₁, h0, hr, hst, hr2⟩
    exact ⟨c, c₁, hS _ _ h0 hr, hst, hr2⟩
  · rintro ⟨c, c₁, hc, hst, hr2⟩
    exact ⟨c, c, c₁, hc, .refl _, hst, hr2⟩

theorem pSeq_some {S T : PSet KSt KIn} {i : KIn} {a : Ans KOut}
    (h : ∀ c', ppost kvB S i a c' ↔ T c') (hne : ∃ c, T c) :
    (pSeq kvB).step S (i, a) = some T := by
  have e : ppost kvB S i a = T := funext fun c => propext (h c)
  simp only [pSeq]
  rw [if_pos (by obtain ⟨c, hc⟩ := hne; exact ⟨c, (h c).2 hc⟩), e]

theorem pSeq_none {S : PSet KSt KIn} {i : KIn} {a : Ans KOut}
    (h : ∀ c', ¬ ppost kvB S i a c') : (pSeq kvB).step S (i, a) = none := by
  simp only [pSeq]
  rw [if_neg (fun ⟨c, hc⟩ => h c hc)]

/-- Lifting one key's reachability to the configurations. -/
theorem lift (k0 : GoString) : ∀ {s t : Option GoString × List GoString}, LReach s t →
    ∀ (c : Cfg), (∀ i ∈ c.pend, isPut i) → c.st k0 = s.1 → vals k0 c.pend = s.2 →
    ∃ c'', PReach kvB c c'' ∧ c''.st k0 = t.1 ∧ (vals k0 c''.pend).Perm t.2 ∧
      (∀ i ∈ c''.pend, isPut i) ∧ ∀ k, k ≠ k0 → c''.st k = c.st k ∧ vals k c''.pend = vals k c.pend := by
  intro s t r
  induction r with
  | perm a hp =>
    intro c hput hs hv
    exact ⟨c, .refl _, hs, hv ▸ hp, hput, fun _ _ => ⟨rfl, rfl⟩⟩
  | @step a p v t hv _ ih =>
    intro c hput hs hvals
    simp only at hs hvals
    rw [← hvals] at hv
    obtain ⟨i, hi, hiv⟩ := mem_vals hv
    have hip := valAt_some hiv
    let c₁ : Cfg := ⟨(kvB.step i c.st).1, c.pend.erase i⟩
    have hs1 : PSilent kvB c c₁ := .apply c i hi
    have hput1 : ∀ j ∈ c₁.pend, isPut j := fun j hj => hput j ((List.erase_subperm _ _).subset hj)
    have hst1 : c₁.st = upd c.st k0 (some v) := by simp [c₁, kvB_step_put i k0 v hip]
    obtain ⟨c'', hr, h1, h2, h3, h4⟩ := ih c₁ hput1 (by rw [hst1]; simp [upd])
      (by simp only [c₁]; rw [vals_erase k0 c.pend i k0 v hip, if_pos rfl, hvals])
    refine ⟨c'', .step hs1 hr, h1, h2, h3, fun k hk => ?_⟩
    obtain ⟨e1, e2⟩ := h4 k hk
    refine ⟨by rw [e1, hst1]; simp [upd, hk], ?_⟩
    rw [e2]
    simp only [c₁]
    rw [vals_erase k c.pend i k0 v hip, if_neg (fun e => hk e.symm)]

/-- **Reaching a configuration** that differs at one key by that key's reachability. -/
theorem reach_to (k0 : GoString) {c c' : Cfg} (hput : ∀ i ∈ c.pend, isPut i)
    (hput' : ∀ i ∈ c'.pend, isPut i)
    (hk : ∀ k, k ≠ k0 → c'.st k = c.st k ∧ (vals k c'.pend).Perm (vals k c.pend))
    (hr : LReach (c.st k0, vals k0 c.pend) (c'.st k0, vals k0 c'.pend)) : PReach kvB c c' := by
  obtain ⟨c'', hr', h1, h2, h3, h4⟩ := lift k0 hr c hput rfl rfl
  have hst : c''.st = c'.st := by
    funext k
    by_cases h : k = k0
    · subst h; exact h1
    · rw [(h4 k h).1, (hk k h).1]
  have hp : c'.pend.Perm c''.pend := perm_of_vals hput' h3 fun k => by
    by_cases h : k = k0
    · subst h; exact h2.symm
    · rw [(h4 k h).2]; exact (hk k h).2
  have hs : PSilent kvB c'' ⟨c''.st, c'.pend⟩ := .perm c'' c'.pend hp
  rw [hst] at hs
  exact hr'.trans (.single hs)

open Classical in
/-- The pending puts of the values `L` at `k0` (those that are valid inputs). -/
def mkPuts (k0 : GoString) (L : List GoString) : List KIn :=
  L.filterMap fun v => if h : inB (.put k0 v) then some ⟨.put k0 v, h⟩ else none

theorem mkPuts_put (k0 : GoString) (L : List GoString) : ∀ i ∈ mkPuts k0 L, isPut i := by
  intro i hi
  simp only [mkPuts, List.mem_filterMap] at hi
  obtain ⟨v, -, hv⟩ := hi
  split at hv
  · cases hv; exact ⟨k0, v, rfl⟩
  · cases hv

theorem vals_mkPuts (k0 : GoString) (L : List GoString) (hL : ∀ v ∈ L, inB (.put k0 v))
    (k : GoString) : vals k (mkPuts k0 L) = if k0 = k then L else [] := by
  induction L with
  | nil => simp [mkPuts, vals]
  | cons v L ih =>
    have hv := hL v (by simp)
    have ih' := ih (fun w hw => hL w (by simp [hw]))
    simp only [mkPuts, List.filterMap_cons, dif_pos hv] at ih' ⊢
    rw [show vals k (⟨.put k0 v, hv⟩ :: List.filterMap _ L) = _ from vals_cons k _ _]
    rw [valAt_put ⟨.put k0 v, hv⟩ k0 v rfl k]
    by_cases h : k0 = k
    · simp only [h, ↓reduceIte] at ih' ⊢
      unfold vals at ih'; unfold vals; rw [ih']
    · simp only [h, ↓reduceIte] at ih' ⊢
      unfold vals at ih'; unfold vals; rw [ih']

/-- `c` with key `k0` at the value `a0` and the pending values `L`. -/
def modK (c : Cfg) (k0 : GoString) (a0 : Option GoString) (L : List GoString) : Cfg :=
  ⟨upd c.st k0 a0, c.pend.filter (fun j => !decide (keyOf j = k0)) ++ mkPuts k0 L⟩

theorem valAt_key {k v : GoString} {j : KIn} (h : valAt k j = some v) : keyOf j = k := by
  have := valAt_some h
  simp [keyOf, this]

theorem valAt_none_of_key {k : GoString} {j : KIn} (h : keyOf j ≠ k) : valAt k j = none := by
  rcases hj : valAt k j with _ | v
  · rfl
  · exact absurd (valAt_key hj) h

theorem vals_filter_key (l : List KIn) (k0 k : GoString) :
    vals k (l.filter (fun j => !decide (keyOf j = k0))) = if k = k0 then [] else vals k l := by
  induction l with
  | nil => by_cases h : k = k0 <;> simp [vals, h]
  | cons j l ih =>
    rw [List.filter_cons]
    by_cases hkj : keyOf j = k0
    · simp only [hkj, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [ih, vals_cons]
      by_cases h : k = k0
      · simp [h]
      · simp [h, valAt_none_of_key (fun e => h (e.symm.trans hkj))]
    · simp only [hkj, decide_false, Bool.not_false, ↓reduceIte]
      rw [vals_cons, vals_cons, ih]
      by_cases h : k = k0
      · subst h
        simp [valAt_none_of_key hkj]
      · simp only [h, ↓reduceIte]

theorem modK_st (c : Cfg) (k0 : GoString) (a0 : Option GoString) (L : List GoString) (k : GoString) :
    (modK c k0 a0 L).st k = if k = k0 then a0 else c.st k := rfl

theorem modK_vals (c : Cfg) (k0 : GoString) (a0 : Option GoString) (L : List GoString)
    (hL : ∀ v ∈ L, inB (.put k0 v)) (k : GoString) :
    vals k (modK c k0 a0 L).pend = if k = k0 then L else vals k c.pend := by
  simp only [modK]
  rw [vals_append, vals_filter_key, vals_mkPuts k0 L hL]
  by_cases h : k = k0
  · simp [h]
  · have : ¬ k0 = k := fun e => h e.symm
    simp [h, this]

theorem modK_put (c : Cfg) (k0 : GoString) (a0 : Option GoString) (L : List GoString)
    (hput : ∀ i ∈ c.pend, isPut i) : ∀ i ∈ (modK c k0 a0 L).pend, isPut i := by
  intro i hi
  simp only [modK, List.mem_append, List.mem_filter] at hi
  rcases hi with ⟨hi, -⟩ | hi
  · exact hput i hi
  · exact mkPuts_put k0 L i hi

/-- A configuration of `kvSet es` changed at one key into another of that key's: in
`kvSet es`. -/
theorem kvSet_modK {es : List EntV} {c : Cfg} (hc : kvSet es c) (k0 : GoString) (a0 : Option GoString)
    (L : List GoString) (hL : ∀ v ∈ L, inB (.put k0 v)) (hk0 : entOk (findE es k0) a0 L) :
    kvSet es (modK c k0 a0 L) := by
  refine ⟨modK_put c k0 a0 L hc.1, fun k => ?_⟩
  rw [modK_st, modK_vals c k0 a0 L hL]
  by_cases h : k = k0
  · subst h; simpa using hk0
  · simp only [h, ↓reduceIte]; exact hc.2 k

/-- Every state's configurations are values at most bounded: none, or a bounded value. -/
theorem kvSet_st {es : List EntV} (hwf : WF es) {c : Cfg} (hc : kvSet es c) (k : GoString) :
    outB (.got (c.st k)) := by
  obtain ⟨hv, hcur⟩ := hwf k
  rcases hc.2 k with ⟨h1, -⟩ | ⟨x, hx, h1, -⟩
  · rw [h1]
    rcases hcur with h | h
    · rw [h, optS_nil]; trivial
    · rw [optS_ne h.1]; exact h
  · rw [h1]
    obtain ⟨⟨-, hne⟩, hlen⟩ := hv x hx
    exact ⟨hne, by simp only [valLen] at hlen; omega⟩

end sets

/-! ## The kinds of step -/

section steps

theorem pstep_err {c c₁ : Cfg} {i : KIn} (h : PStep kvB c i .err c₁) :
    (kvB.isWrite i = true ∧ c₁ = ⟨c.st, i :: c.pend⟩) ∨ (kvB.isWrite i = false ∧ c₁ = c) := by
  cases h with
  | errW hw _ => exact .inl ⟨hw, rfl⟩
  | errR hw _ => exact .inr ⟨hw, rfl⟩

theorem pstep_ok {c c₁ : Cfg} {i : KIn} {o : KOut} (h : PStep kvB c i (.ok o) c₁) :
    o = (kvB.step i c.st).2 ∧ c₁ = ⟨(kvB.step i c.st).1, c.pend⟩ := by
  cases h with
  | ok _ => exact ⟨rfl, rfl⟩
  | obs _ h _ => simp [kvB] at h

/-- `kvSet` holds a configuration (the state's witness). -/
theorem kvSet_reach {es : List EntV} {c₁ c' : Cfg} (h : kvSet es c₁) (r : PReach kvB c₁ c') :
    kvSet es c' := kvSet_closed es _ _ h r

/-- `M ++ [v]` without `v` is `M`. -/
theorem perm_erase_snoc (M : List GoString) (v : GoString) : ((M ++ [v]).erase v).Perm M := by
  have := (List.perm_append_singleton v M).erase v
  simpa using this

/-- A new pending put, locally. -/
theorem errput_local {cur : Option GoString} {O N : List GoString} {a : Option GoString}
    {p : List GoString} (v : GoString) (h : keyOk cur O N a p) :
    keyOk cur O (N ++ [v]) a (v :: p) := by
  rcases h with ⟨h1, O', hO', h2⟩ | ⟨x, hx, h1, h2⟩
  · refine .inl ⟨h1, O', hO', ?_⟩
    rw [← List.append_assoc]
    exact (h2.cons v).trans (List.perm_append_singleton v _).symm
  · refine .inr ⟨x, by rw [← List.append_assoc]; exact List.mem_append_left _ hx, h1, ?_⟩
    rw [← List.append_assoc, List.erase_append_left _ hx]
    exact ((List.subperm_cons v).2 h2).trans (List.perm_append_singleton v _).symm.subperm

/-- A new pending put still pending, locally: without it. -/
theorem errput_back {cur : Option GoString} {O N : List GoString} {a : Option GoString}
    {p : List GoString} {v : GoString} (hv : v ∈ p) (h : keyOk cur O (N ++ [v]) a p) :
    keyOk cur O N a (p.erase v) := by
  rcases h with ⟨h1, O', hO', h2⟩ | ⟨x, hx, h1, h2⟩
  · refine .inl ⟨h1, O', hO', ?_⟩
    rw [← List.append_assoc] at h2
    exact (h2.erase v).trans (perm_erase_snoc _ v)
  · rw [← List.append_assoc] at hx h2
    have hxL : x ∈ O ++ N := by
      rcases List.mem_append.1 hx with h | h
      · exact h
      · simp only [List.mem_singleton] at h
        subst h
        refine Classical.byContradiction fun hn => ?_
        rw [List.erase_append_right _ hn] at h2
        simp only [List.erase_cons_head, List.append_nil] at h2
        exact hn (h2.subset hv)
    refine .inr ⟨x, hxL, h1, ?_⟩
    rw [List.erase_append_left _ hxL] at h2
    exact (List.Subperm.erase v h2).trans (perm_erase_snoc _ v).subperm

theorem kvSet_mk {es : List EntV} {c : Cfg} (k0 : GoString) (hput : ∀ i ∈ c.pend, isPut i)
    (hk0 : entOk (findE es k0) (c.st k0) (vals k0 c.pend))
    (hoth : ∀ k', k0 ≠ k' → entOk (findE es k') (c.st k') (vals k' c.pend)) : kvSet es c := by
  refine ⟨hput, fun k' => ?_⟩
  by_cases h : k0 = k'
  · subst h; exact hk0
  · exact hoth k' h

theorem oth_of {es es' : List EntV} {k : GoString} {c : Cfg} (hc : kvSet es' c)
    (hfo : ∀ k', k ≠ k' → findE es' k' = findE es k') :
    ∀ k', k ≠ k' → entOk (findE es k') (c.st k') (vals k' c.pend) := fun k' h => by
  have := hc.2 k'; rwa [hfo k' h] at this

/-- The pre-configuration from the base at `k`. -/
theorem kvSet_base {es es' : List EntV} (hwf : WF es) {k : GoString} {c' : Cfg} (hc' : kvSet es' c')
    (hfo : ∀ k', k ≠ k' → findE es' k' = findE es k') :
    kvSet es (modK c' k (optS (findE es k).cur) ((findE es k).old ++ (findE es k).new)) := by
  refine kvSet_mk k (modK_put c' k (optS (findE es k).cur) _ hc'.1) ?_ fun k' h => ?_
  · rw [modK_st, if_pos rfl, modK_vals _ _ _ _ (hwf k).1, if_pos rfl]; exact keyOk_base _ _ _
  · rw [modK_st, if_neg (fun e => h e.symm), modK_vals _ _ _ _ (hwf k).1, if_neg (fun e => h e.symm)]
    exact oth_of hc' hfo k' h

theorem nonempty_of_step {S T : PSet KSt KIn} (hS : PSet.Closed kvB S) {i : KIn} {a : Ans KOut}
    (h : ∀ c', ppost kvB S i a c' ↔ T c') {c c₁ : Cfg} (hc : S c) (hst : PStep kvB c i a c₁) :
    ∃ c, T c :=
  ⟨c₁, (h c₁).1 ((ppost_iff hS i a c₁).2 ⟨c, c₁, hc, hst, .refl _⟩)⟩

theorem outB_optS {w : Option GoString} (h : outB (.got w)) : w = optS (w.getD []) := by
  cases w with
  | none => simp [optS]
  | some x => simp only [Option.getD_some]; exact (optS_ne h.1).symm

theorem optS_getD (s : GoString) : (optS s).getD [] = s := by
  unfold optS; split <;> simp_all

variable (es : List EntV) (hwf : WF es)
include hwf

/-- A get of unknown outcome changes nothing. -/
theorem step_err_get (i : KIn) (k : GoString) (hi : i.1 = .get k) :
    ∀ c', ppost kvB (kvSet es) i .err c' ↔ kvSet es c' := by
  intro c'
  rw [ppost_iff (kvSet_closed es)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    rcases pstep_err hst with ⟨hw, -⟩ | ⟨-, rfl⟩
    · simp [kvB, hi] at hw
    · exact kvSet_reach hc hr
  · intro hc
    exact ⟨c', c', hc, .errR c' i (by simp [kvB, hi]) rfl, .refl _⟩

/-- A put of unknown outcome is a new pending one. -/
theorem step_err_put (i : KIn) (k v : GoString) (hi : i.1 = .put k v) :
    ∀ c', ppost kvB (kvSet es) i .err c' ↔
      kvSet (setE es ⟨k, (findE es k).cur, (findE es k).old, (findE es k).new ++ [v]⟩) c' := by
  intro c'
  have hfk := setE_k es ⟨k, (findE es k).cur, (findE es k).old, (findE es k).new ++ [v]⟩ k rfl
  have hfo : ∀ k', k ≠ k' → findE (setE es ⟨k, (findE es k).cur, (findE es k).old,
      (findE es k).new ++ [v]⟩) k' = findE es k' := fun k' h => setE_ne _ _ k' h
  have hw : kvB.isWrite i = true := by simp [kvB, hi]
  rw [ppost_iff (kvSet_closed es)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    rcases pstep_err hst with ⟨-, rfl⟩ | ⟨hw', -⟩
    · refine kvSet_reach (kvSet_mk k ?_ ?_ fun k' h => ?_) hr
      · intro j hj
        rcases List.mem_cons.1 hj with rfl | hj
        · exact ⟨k, v, hi⟩
        · exact hc.1 j hj
      · show entOk _ (c.st k) (vals k (i :: c.pend))
        rw [hfk, vals_cons, valAt_put i k v hi k, if_pos rfl]
        exact errput_local v (hc.2 k)
      · show entOk _ (c.st k') (vals k' (i :: c.pend))
        rw [hfo k' h, vals_cons, valAt_put i k v hi k', if_neg h]
        exact hc.2 k'
    · rw [hw] at hw'; cases hw'
  · intro hc'
    have hst : keyOk (optS (findE es k).cur) (findE es k).old ((findE es k).new ++ [v])
        (c'.st k) (vals k c'.pend) := by have := hc'.2 k; rw [hfk] at this; exact this
    have hoth := oth_of hc' hfo
    by_cases hb : v ∈ vals k c'.pend
    · -- the new pending put is still pending
      obtain ⟨j, hj, hjv⟩ := mem_vals hb
      have hji : j = i := Subtype.ext ((valAt_some hjv).trans hi.symm)
      subst hji
      let c : Cfg := ⟨c'.st, c'.pend.erase j⟩
      refine ⟨c, ⟨c'.st, j :: c'.pend.erase j⟩, ?_, .errW c j hw rfl,
        .single (.perm _ _ (List.perm_cons_erase hj))⟩
      refine kvSet_mk k (fun i' hi' => hc'.1 i' ((List.erase_subperm _ _).subset hi')) ?_ fun k' h => ?_
      · show entOk _ (c'.st k) (vals k (c'.pend.erase j))
        rw [vals_erase k c'.pend j k v hi, if_pos rfl]
        exact errput_back hb hst
      · show entOk _ (c'.st k') (vals k' (c'.pend.erase j))
        rw [vals_erase k' c'.pend j k v hi, if_neg h]
        exact hoth k' h
    · -- from the base configuration
      have hn : ¬ (c'.st k = optS (findE es k).cur ∧ ∃ O', O'.Subperm (findE es k).old ∧
          (vals k c'.pend).Perm (O' ++ ((findE es k).new ++ [v]))) := by
        rintro ⟨-, O', -, h2⟩
        exact hb (h2.symm.subset (by simp))
      have hr := keyOk_from_base hst hn
      have hL := (hwf k).1
      let c := modK c' k (optS (findE es k).cur) ((findE es k).old ++ (findE es k).new)
      have hc : kvSet es c := kvSet_base hwf hc' hfo
      refine ⟨c, ⟨c.st, i :: c.pend⟩, hc, .errW c i hw rfl, ?_⟩
      refine reach_to k (fun j hj => ?_) hc'.1 (fun k' hk' => ?_) ?_
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact ⟨k, v, hi⟩
        · exact hc.1 j hj
      · show c'.st k' = c.st k' ∧ (vals k' c'.pend).Perm (vals k' (i :: c.pend))
        rw [modK_st, if_neg hk', vals_cons, valAt_put i k v hi k',
          if_neg (fun e => hk' e.symm), modK_vals c' k _ _ hL, if_neg hk']
        exact ⟨rfl, .refl _⟩
      · show LReach (c.st k, vals k (i :: c.pend)) (c'.st k, vals k c'.pend)
        rw [modK_st, if_pos rfl, vals_cons, valAt_put i k v hi k, if_pos rfl,
          modK_vals c' k _ _ hL, if_pos rfl]
        have hp : (v :: ((findE es k).old ++ (findE es k).new)).Perm
            ((findE es k).old ++ ((findE es k).new ++ [v])) := by
          rw [← List.append_assoc]; exact (List.perm_append_singleton v _).symm
        exact lreach_perm_left hr _ hp

/-- An answered put: its key's value, every pending put old. -/
theorem step_ok_put (i : KIn) (k v : GoString) (hi : i.1 = .put k v) (o : KOut)
    (ho : o.1 = .done) :
    ∀ c', ppost kvB (kvSet es) i (.ok o) c' ↔
      kvSet (setE es ⟨k, v, (findE es k).old ++ (findE es k).new, []⟩) c' := by
  intro c'
  have hfk := setE_k es ⟨k, v, (findE es k).old ++ (findE es k).new, []⟩ k rfl
  have hfo : ∀ k', k ≠ k' → findE (setE es ⟨k, v, (findE es k).old ++ (findE es k).new, []⟩) k' =
      findE es k' := fun k' h => setE_ne _ _ k' h
  have hvne : v ≠ [] := by have := i.2.1; rw [hi] at this; exact this.2
  have hov : o = (kvB.step i c'.st).2 := by
    rw [kvB_step_put i k v hi]; exact Subtype.ext (by rw [ho]; simp [clampO, outB])
  have hok : ∀ σ, (kvB.step i σ).2 = o := fun σ => by
    rw [kvB_step_put i k v hi]; exact Subtype.ext (by rw [ho]; simp [clampO, outB])
  rw [ppost_iff (kvSet_closed es)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    obtain ⟨-, rfl⟩ := pstep_ok hst
    rw [kvB_step_put i k v hi] at hr
    have hr' : PReach kvB ⟨upd c.st k (some v), c.pend⟩ c' := hr
    refine kvSet_reach (kvSet_mk (c := ⟨upd c.st k (some v), c.pend⟩) k hc.1 ?_ fun k' h => ?_) hr'
    · show entOk _ (upd c.st k (some v) k) (vals k c.pend)
      rw [hfk]
      simp only [upd, ↓reduceIte, entOk, optS_ne hvne]
      refine .inl ⟨rfl, vals k c.pend, ?_, by simp⟩
      rcases hc.2 k with ⟨-, O', hO', h2⟩ | ⟨x, -, -, h2⟩
      · exact h2.subperm.trans ((List.subperm_append_right _).2 hO')
      · exact h2.trans (List.erase_subperm _ _)
    · show entOk _ (upd c.st k (some v) k') (vals k' c.pend)
      rw [hfo k' h]
      simp only [upd, if_neg (fun e : k' = k => h e.symm)]
      exact hc.2 k'
  · intro hc'
    have hst : keyOk (some v) ((findE es k).old ++ (findE es k).new) [] (c'.st k) (vals k c'.pend) := by
      have := hc'.2 k; rw [hfk] at this; unfold entOk at this; rwa [optS_ne hvne] at this
    have hoth := oth_of hc' hfo
    rcases hst with ⟨h1, O', hO', h2⟩ | ⟨x, hx, h1, h2⟩
    · -- the put took effect last: from the same pending puts
      have hp : (vals k c'.pend).Subperm ((findE es k).old ++ (findE es k).new) :=
        (h2.trans (by simp)).subperm.trans hO'
      have hpre : ∃ a0, keyOk (optS (findE es k).cur) (findE es k).old (findE es k).new a0
          (vals k c'.pend) := by
        by_cases hpe : (vals k c'.pend).Perm ((findE es k).old ++ (findE es k).new)
        · exact ⟨_, .inl ⟨rfl, _, List.Subperm.refl _, hpe⟩⟩
        · obtain ⟨x, hx, hpx⟩ := subperm_proper hp hpe
          exact ⟨some x, .inr ⟨x, hx, rfl, hpx⟩⟩
      obtain ⟨a0, ha0⟩ := hpre
      let c : Cfg := ⟨upd c'.st k a0, c'.pend⟩
      have hc1 : (⟨(kvB.step i c.st).1, c.pend⟩ : Cfg) = c' := by
        rw [kvB_step_put i k v hi]
        cases c'
        simp only [c, PCfg.mk.injEq, and_true]
        funext k'
        by_cases h : k' = k
        · subst h; simp only [upd, if_pos rfl]; exact h1.symm
        · simp [upd, h]
      refine ⟨c, c', kvSet_mk k hc'.1 ?_ fun k' h => ?_, ?_, .refl _⟩
      · show entOk _ (upd c'.st k a0 k) (vals k c'.pend)
        simp only [upd, ↓reduceIte]; exact ha0
      · show entOk _ (upd c'.st k a0 k') (vals k' c'.pend)
        simp only [upd, if_neg (fun e : k' = k => h e.symm)]
        exact hoth k' h
      · have := PStep.ok c i (rfl : kvB.isObs i = false)
        rw [hok, hc1] at this
        exact this
    · -- some old pending put took effect after it: from the base
      have hL := (hwf k).1
      let c := modK c' k (optS (findE es k).cur) ((findE es k).old ++ (findE es k).new)
      have hc : kvSet es c := kvSet_base hwf hc' hfo
      have hst' := PStep.ok c i (rfl : kvB.isObs i = false)
      rw [hok] at hst'
      refine ⟨c, _, hc, hst', ?_⟩
      rw [kvB_step_put i k v hi]
      refine reach_to k (modK_put c' k (optS (findE es k).cur) _ hc'.1) hc'.1 (fun k' hk' => ?_) ?_
      · show c'.st k' = upd c.st k (some v) k' ∧ (vals k' c'.pend).Perm (vals k' c.pend)
        simp only [upd, if_neg hk']
        rw [modK_st, if_neg hk', modK_vals c' k _ _ hL, if_neg hk']
        exact ⟨rfl, .refl _⟩
      · show LReach (upd c.st k (some v) k, vals k c.pend) (c'.st k, vals k c'.pend)
        simp only [upd, ↓reduceIte]
        rw [modK_vals c' k _ _ hL, if_pos rfl, h1]
        simp only [List.append_nil] at hx h2
        exact lreach_last _ hx h2

theorem step_ok_put_no (i : KIn) (k v : GoString) (hi : i.1 = .put k v) (o : KOut)
    (ho : o.1 ≠ .done) : ∀ c', ¬ ppost kvB (kvSet es) i (.ok o) c' := by
  intro c' hp
  rw [ppost_iff (kvSet_closed es)] at hp
  obtain ⟨c, c₁, -, hst, -⟩ := hp
  obtain ⟨e, -⟩ := pstep_ok hst
  rw [kvB_step_put i k v hi] at e
  apply ho
  rw [e]; simp [clampO, outB]

/-- An answered get's value in a configuration of the state. -/
theorem get_out {c c₁ : Cfg} (hc : kvSet es c) {i : KIn} {k : GoString} (hi : i.1 = .get k)
    {o : KOut} (hst : PStep kvB c i (.ok o) c₁) : o.1 = .got (c.st k) ∧ c₁ = c := by
  obtain ⟨e, rfl⟩ := pstep_ok hst
  rw [kvB_step_get i k hi] at e ⊢
  refine ⟨by rw [e, clampO_of _ (kvSet_st hwf hc k)], rfl⟩

/-- An answered get of the state's value: nothing changes. -/
theorem step_ok_get_cur (i : KIn) (k : GoString) (hi : i.1 = .get k) (o : KOut)
    (ho : o.1 = .got (optS (findE es k).cur)) :
    ∀ c', ppost kvB (kvSet es) i (.ok o) c' ↔ kvSet es c' := by
  intro c'
  rw [ppost_iff (kvSet_closed es)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    obtain ⟨-, rfl⟩ := get_out es hwf hc hi hst
    exact kvSet_reach hc hr
  · intro hc'
    have hL := (hwf k).1
    -- a configuration of the state whose value is the state's: the get steps from it to itself
    have hget : ∀ c : Cfg, kvSet es c → c.st k = optS (findE es k).cur →
        PStep kvB c i (.ok o) c := by
      intro c hc hck
      have hst := PStep.ok c i (rfl : kvB.isObs i = false)
      have hoc : (kvB.step i c.st).2 = o := by
        rw [kvB_step_get i k hi]
        apply Subtype.ext
        rw [clampO_of _ (kvSet_st hwf hc k)]
        show KvOutput.got (c.st k) = o.1
        rw [ho, hck]
      have hc1 : (⟨(kvB.step i c.st).1, c.pend⟩ : Cfg) = c := by rw [kvB_step_get i k hi]
      rw [hoc, hc1] at hst
      exact hst
    by_cases hb : c'.st k = optS (findE es k).cur ∧ ∃ O', O'.Subperm (findE es k).old ∧
        (vals k c'.pend).Perm (O' ++ (findE es k).new)
    · exact ⟨c', c', hc', hget c' hc' hb.1, .refl _⟩
    · let c := modK c' k (optS (findE es k).cur) ((findE es k).old ++ (findE es k).new)
      have hc : kvSet es c := kvSet_base hwf hc' (fun _ _ => rfl)
      refine ⟨c, c, hc, hget c hc (by rw [modK_st, if_pos rfl]), ?_⟩
      refine reach_to k (modK_put c' k (optS (findE es k).cur) _ hc'.1) hc'.1 (fun k' hk' => ?_) ?_
      · rw [modK_st, if_neg hk', modK_vals c' k _ _ hL, if_neg hk']; exact ⟨rfl, .refl _⟩
      · rw [modK_st, if_pos rfl, modK_vals c' k _ _ hL, if_pos rfl]
        exact keyOk_from_base (hc'.2 k) hb

/-- An answered get of a pending put's value: that put took effect last, the others are old. -/
theorem step_ok_get_pend (i : KIn) (k : GoString) (hi : i.1 = .get k) (o : KOut) (u : GoString)
    (ho : o.1 = .got (some u)) (hu : u ≠ (findE es k).cur) (hm : u ∈ (findE es k).old ++ (findE es k).new) :
    ∀ c', ppost kvB (kvSet es) i (.ok o) c' ↔
      kvSet (setE es ⟨k, u, ((findE es k).old ++ (findE es k).new).erase u, []⟩) c' := by
  intro c'
  have hfk := setE_k es ⟨k, u, ((findE es k).old ++ (findE es k).new).erase u, []⟩ k rfl
  have hfo : ∀ k', k ≠ k' →
      findE (setE es ⟨k, u, ((findE es k).old ++ (findE es k).new).erase u, []⟩) k' = findE es k' :=
    fun k' h => setE_ne _ _ k' h
  have hL := (hwf k).1
  have hune : u ≠ [] := ((hL u hm).1).2
  have hL' : ∀ w ∈ ((findE es k).old ++ (findE es k).new).erase u, inB (.put k w) :=
    fun w hw => hL w ((List.erase_subperm _ _).subset hw)
  rw [ppost_iff (kvSet_closed es)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    obtain ⟨hout, hc1⟩ := get_out es hwf hc hi hst
    rw [hc1] at hr
    rw [ho] at hout
    have hck : c.st k = some u := by injection hout with h; exact h.symm
    refine kvSet_reach (kvSet_mk k hc.1 ?_ fun k' h => ?_) hr
    · rw [hfk]
      unfold entOk
      simp only [optS_ne hune]
      rcases hc.2 k with ⟨h1, -⟩ | ⟨x, -, h1, h2⟩
      · exfalso; apply hu; apply optS_inj; rw [optS_ne hune, ← hck, h1]
      · rw [hck] at h1
        injection h1 with h1
        subst h1
        exact .inl ⟨hck, vals k c.pend, h2, by simp⟩
    · rw [hfo k' h]; exact hc.2 k'
  · intro hc'
    have hst : keyOk (some u) (((findE es k).old ++ (findE es k).new).erase u) [] (c'.st k)
        (vals k c'.pend) := by
      have := hc'.2 k; rw [hfk] at this; unfold entOk at this; rwa [optS_ne hune] at this
    have hoth := oth_of hc' hfo
    -- a configuration of `es` whose value is `u`: the get steps from it to itself
    have hget : ∀ c : Cfg, kvSet es c → c.st k = some u → PStep kvB c i (.ok o) c := by
      intro c hc hck
      have hst := PStep.ok c i (rfl : kvB.isObs i = false)
      have hoc : (kvB.step i c.st).2 = o := by
        rw [kvB_step_get i k hi]
        apply Subtype.ext
        rw [clampO_of _ (kvSet_st hwf hc k)]
        show KvOutput.got (c.st k) = o.1
        rw [ho, hck]
      have hc1 : (⟨(kvB.step i c.st).1, c.pend⟩ : Cfg) = c := by rw [kvB_step_get i k hi]
      rw [hoc, hc1] at hst
      exact hst
    rcases hst with ⟨h1, O', hO', h2⟩ | ⟨y, hy, h1, h2⟩
    · -- `c'` itself
      have hc : kvSet es c' := kvSet_mk k hc'.1 (.inr ⟨u, hm, h1, (h2.trans (by simp)).subperm.trans hO'⟩)
        hoth
      exact ⟨c', c', hc, hget c' hc h1, .refl _⟩
    · -- from `u` with every other pending put
      let c := modK c' k (some u) (((findE es k).old ++ (findE es k).new).erase u)
      have hc : kvSet es c := kvSet_mk k (modK_put _ _ _ _ hc'.1)
        (by rw [modK_st, if_pos rfl, modK_vals _ _ _ _ hL', if_pos rfl]
            exact .inr ⟨u, hm, rfl, List.Subperm.refl _⟩)
        (fun k' h => by
          rw [modK_st, if_neg (fun e => h e.symm), modK_vals _ _ _ _ hL', if_neg (fun e => h e.symm)]
          exact hoth k' h)
      refine ⟨c, c, hc, hget c hc (by rw [modK_st, if_pos rfl]), ?_⟩
      refine reach_to k (modK_put c' k (some u) _ hc'.1) hc'.1 (fun k' hk' => ?_) ?_
      · rw [modK_st, if_neg hk', modK_vals c' k _ _ hL', if_neg hk']; exact ⟨rfl, .refl _⟩
      · rw [modK_st, if_pos rfl, modK_vals c' k _ _ hL', if_pos rfl, h1]
        simp only [List.append_nil] at hy h2
        exact lreach_last _ hy h2

/-- Any other answered get: refused. -/
theorem step_ok_get_no (i : KIn) (k : GoString) (hi : i.1 = .get k) (o : KOut)
    (hno : ∀ w, o.1 = .got w → w.getD [] ≠ (findE es k).cur ∧
      ¬ (w.getD [] ≠ [] ∧ w.getD [] ∈ (findE es k).old ++ (findE es k).new)) :
    ∀ c', ¬ ppost kvB (kvSet es) i (.ok o) c' := by
  intro c' hp
  rw [ppost_iff (kvSet_closed es)] at hp
  obtain ⟨c, c₁, hc, hst, -⟩ := hp
  obtain ⟨hout, -⟩ := get_out es hwf hc hi hst
  obtain ⟨h1, h2⟩ := hno _ hout
  rcases hc.2 k with ⟨ha, -⟩ | ⟨x, hx, ha, -⟩
  · apply h1; rw [ha, optS_getD]
  · apply h2; rw [ha]
    exact ⟨((hwf k).1 x hx).1.2, hx⟩

theorem step_ok_get_done (i : KIn) (k : GoString) (hi : i.1 = .get k) (o : KOut) (ho : o.1 = .done) :
    ∀ c', ¬ ppost kvB (kvSet es) i (.ok o) c' := by
  intro c' hp
  rw [ppost_iff (kvSet_closed es)] at hp
  obtain ⟨c, c₁, hc, hst, -⟩ := hp
  obtain ⟨hout, -⟩ := get_out es hwf hc hi hst
  rw [ho] at hout; cases hout

/-- **`step` is the model's step** on the set its state stands for. -/
theorem stepG_pSeq (hne : ∃ c, kvSet es c) (i : KIn) (a : Ans KOut) :
    (pSeq kvB).step (kvSet es) (i, a) =
      if (stepG es i a).1 then some (kvSet (stepG es i a).2) else none := by
  obtain ⟨c0, hc0⟩ := hne
  rcases hi : i.1 with k | ⟨k, v⟩
  · -- a get
    cases a with
    | err =>
      have hst : stepG es i .err = (true, es) := by simp [stepG, hi]
      rw [hst]; simp only [↓reduceIte]
      have h := step_err_get es hwf i k hi
      exact pSeq_some h (nonempty_of_step (kvSet_closed es) h hc0 (.errR c0 i (by simp [kvB, hi]) rfl))
    | ok o =>
      rcases ho : o.1 with w | _
      · have hst : stepG es i (.ok o) = (if w.getD [] = (findE es k).cur then (true, es)
            else if w.getD [] ≠ [] ∧ w.getD [] ∈ (findE es k).old ++ (findE es k).new then
              (true, setE es ⟨k, w.getD [], ((findE es k).old ++ (findE es k).new).erase (w.getD []), []⟩)
            else (false, es)) := by simp [stepG, hi, ho]
        have hob : outB (.got w) := ho ▸ o.2
        rw [hst]
        by_cases h1 : w.getD [] = (findE es k).cur
        · simp only [h1, ↓reduceIte]
          have hw : w = optS (findE es k).cur := by rw [outB_optS hob, h1]
          have h := step_ok_get_cur es hwf i k hi o (by rw [ho, hw])
          refine pSeq_some h ?_
          -- a configuration at the state's value
          have hL := (hwf k).1
          let c := modK c0 k (optS (findE es k).cur) ((findE es k).old ++ (findE es k).new)
          exact ⟨c, kvSet_base hwf hc0 (fun _ _ => rfl)⟩
        · simp only [h1, ↓reduceIte]
          by_cases h2 : w.getD [] ≠ [] ∧ w.getD [] ∈ (findE es k).old ++ (findE es k).new
          · simp only [h2, and_self, ↓reduceIte, ne_eq, not_false_eq_true]
            have hw : w = some (w.getD []) := by
              cases w with
              | none => exact absurd rfl h2.1
              | some x => rfl
            have h := step_ok_get_pend es hwf i k hi o (w.getD []) (by rw [ho, ← hw]) h1 h2.2
            refine pSeq_some h ⟨modK c0 k (some (w.getD [])) (((findE es k).old ++
              (findE es k).new).erase (w.getD [])), ?_⟩
            have hL' : ∀ x ∈ ((findE es k).old ++ (findE es k).new).erase (w.getD []), inB (.put k x) :=
              fun x hx => (hwf k).1 x ((List.erase_subperm _ _).subset hx)
            refine kvSet_mk k (modK_put _ _ _ _ hc0.1) ?_ fun k' hk' => ?_
            · rw [setE_k _ _ k rfl, modK_st, if_pos rfl, modK_vals _ _ _ _ hL', if_pos rfl]
              unfold entOk
              rw [optS_ne h2.1]
              exact .inl ⟨rfl, _, List.Subperm.refl _, by simp⟩
            · rw [setE_ne _ _ k' hk', modK_st, if_neg (fun e => hk' e.symm), modK_vals _ _ _ _ hL',
                if_neg (fun e => hk' e.symm)]
              exact hc0.2 k'
          · simp only [h2, ↓reduceIte]
            exact pSeq_none (step_ok_get_no es hwf i k hi o (fun w' hw' => by
              rw [ho] at hw'; injection hw' with hw'; subst hw'; exact ⟨h1, h2⟩))
      · have hst : (stepG es i (.ok o)).1 = false := by simp [stepG, hi, ho]
        rw [hst]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact pSeq_none (step_ok_get_done es hwf i k hi o ho)
  · -- a put
    cases a with
    | err =>
      have hst : stepG es i .err = (true, setE es ⟨k, (findE es k).cur, (findE es k).old,
          (findE es k).new ++ [v]⟩) := by simp [stepG, hi]
      rw [hst]; simp only [↓reduceIte]
      have h := step_err_put es hwf i k v hi
      exact pSeq_some h (nonempty_of_step (kvSet_closed es) h hc0 (.errW c0 i (by simp [kvB, hi]) rfl))
    | ok o =>
      have hst : stepG es i (.ok o) = (decide (o.1 = .done),
          setE es ⟨k, v, (findE es k).old ++ (findE es k).new, []⟩) := by simp [stepG, hi]
      rw [hst]
      by_cases ho : o.1 = .done
      · simp only [ho, decide_true, ↓reduceIte]
        have h := step_ok_put es hwf i k v hi o ho
        have hok : (kvB.step i c0.st).2 = o := by
          rw [kvB_step_put i k v hi]; exact Subtype.ext (by rw [ho]; simp [clampO, outB])
        have hs := PStep.ok c0 i (rfl : kvB.isObs i = false)
        rw [hok] at hs
        exact pSeq_some h (nonempty_of_step (kvSet_closed es) h hc0 hs)
      · simp only [ho, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact pSeq_none (step_ok_put_no es hwf i k v hi o ho)

end steps

/-! ## The initial state, well-formedness, bounds -/

section init

theorem kvSet_init : kvSet [] = pInit kvB := by
  funext c
  apply propext
  constructor
  · rintro ⟨hput, hk⟩
    have hst : ∀ k, c.st k = none ∧ vals k c.pend = [] := by
      intro k
      have := hk k
      rw [findE_nil] at this
      unfold entOk keyOk at this
      rcases this with ⟨h1, O', hO', h2⟩ | ⟨x, hx, -⟩
      · refine ⟨by rw [h1]; rfl, ?_⟩
        have hO : O' = [] := List.subperm_nil.1 hO'
        subst hO
        exact List.Perm.eq_nil (by simpa using h2)
      · simp at hx
    have hp : c.pend = [] := by
      cases hc : c.pend with
      | nil => rfl
      | cons j l =>
        exfalso
        obtain ⟨k, v, hj⟩ := hput j (by rw [hc]; simp)
        have := (hst k).2
        rw [hc, vals_cons, valAt_put j k v hj k, if_pos rfl] at this
        cases this
    cases c
    simp only [pInit, PCfg.mk.injEq]
    exact ⟨funext fun k => (hst k).1, hp⟩
  · intro h
    simp only [pInit] at h
    subst h
    refine ⟨by simp, fun k => ?_⟩
    rw [findE_nil]
    exact .inl ⟨rfl, [], List.Subperm.refl _, by simp [vals]⟩

theorem kvSet_init_ne : ∃ c, kvSet [] c := ⟨⟨kvB.init, []⟩, by rw [kvSet_init]; rfl⟩

theorem WF_nil : WF [] := fun k => by rw [findE_nil]; simp

theorem findE_mem (es : List EntV) (k : GoString) :
    findE es k ∈ es ∨ findE es k = ⟨k, [], [], []⟩ := by
  unfold findE
  rcases h : es.find? (fun e => decide (e.k = k)) with _ | e
  · right; rw [h]; rfl
  · left; rw [h]; exact List.mem_of_find?_eq_some h

theorem WF_setE {es : List EntV} (hwf : WF es) (e : EntV)
    (he : (∀ v ∈ e.old ++ e.new, inB (.put e.k v)) ∧ (e.cur = [] ∨ valB e.cur)) :
    WF (setE es e) := fun k => by
  rw [findE_setE]
  by_cases h : e.k = k
  · subst h; simpa using he
  · simp only [h, ↓reduceIte]; exact hwf k

theorem WF_stepG {es : List EntV} (hwf : WF es) (i : KIn) (a : Ans KOut) :
    WF (stepG es i a).2 := by
  rcases hi : i.1 with k | ⟨k, v⟩
  · cases a with
    | err => simp only [stepG, hi]; exact hwf
    | ok o =>
      rcases ho : o.1 with w | _
      · simp only [stepG, hi, ho]
        split
        · exact hwf
        · split
          · rename_i h2
            refine WF_setE hwf _ ⟨fun x hx => ?_, .inr ⟨h2.1, ?_⟩⟩
            · simp only [List.append_nil] at hx
              exact (hwf k).1 x ((List.erase_subperm _ _).subset hx)
            · have := ((hwf k).1 _ h2.2).2; simp only [valLen] at this; simp only; omega
          · exact hwf
      · simp only [stepG, hi, ho]; exact hwf
  · have hv : inB (.put k v) := hi ▸ i.2
    cases a with
    | err =>
      simp only [stepG, hi]
      refine WF_setE hwf _ ⟨fun x hx => ?_, (hwf k).2⟩
      simp only [← List.append_assoc, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact (hwf k).1 x (List.mem_append.2 hx)
      · exact hv
    | ok o =>
      simp only [stepG, hi]
      refine WF_setE hwf _ ⟨fun x hx => ?_, .inr ⟨hv.1.2, by have := hv.2; simp only [valLen] at this; simp only; omega⟩⟩
      simp only [List.append_nil] at hx
      exact (hwf k).1 x hx

/-- The state's size after `n` steps: at most `n` entries, each with at most `n` pending puts. -/
def EB (n : Nat) (es : List EntV) : Prop :=
  es.length ≤ n ∧ ∀ e ∈ es, e.old.length + e.new.length ≤ n

theorem EB_nil : EB 0 [] := by simp [EB]

theorem EB_mono {n m : Nat} {es : List EntV} (h : EB n es) (hnm : n ≤ m) : EB m es :=
  ⟨by have := h.1; omega, fun e he => by have := h.2 e he; omega⟩

theorem EB_findE {n : Nat} {es : List EntV} (h : EB n es) (k : GoString) :
    (findE es k).old.length + (findE es k).new.length ≤ n := by
  rcases findE_mem es k with hm | he
  · exact h.2 _ hm
  · rw [he]; simp

theorem EB_setE {n : Nat} {es : List EntV} (h : EB n es) (e : EntV)
    (he : e.old.length + e.new.length ≤ n + 1) : EB (n + 1) (setE es e) := by
  unfold setE
  split
  · refine ⟨by simp; have := h.1; omega, fun x hx => ?_⟩
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    split
    · exact he
    · have := h.2 y hy; omega
  · refine ⟨by simp; have := h.1; omega, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have := h.2 x hx; omega
    · exact he

theorem EB_stepG {n : Nat} {es : List EntV} (h : EB n es) (i : KIn) (a : Ans KOut) :
    EB (n + 1) (stepG es i a).2 := by
  have hk := EB_findE h
  rcases hi : i.1 with k | ⟨k, v⟩
  · cases a with
    | err => simp only [stepG, hi]; exact EB_mono h (by omega)
    | ok o =>
      rcases ho : o.1 with w | _
      · simp only [stepG, hi, ho]
        split
        · exact EB_mono h (by omega)
        · split
          · refine EB_setE h _ ?_
            have := hk k
            have := List.length_erase_le (a := w.getD []) (l := (findE es k).old ++ (findE es k).new)
            simp only [List.length_append, List.length_nil] at *
            omega
          · exact EB_mono h (by omega)
      · simp only [stepG, hi, ho]; exact EB_mono h (by omega)
  · cases a with
    | err =>
      simp only [stepG, hi]
      refine EB_setE h _ ?_
      have := hk k
      simp only [List.length_append, List.length_singleton] at *
      omega
    | ok o =>
      simp only [stepG, hi]
      refine EB_setE h _ ?_
      have := hk k
      simp only [List.length_append, List.length_nil] at *
      omega

end init

end Perennial.rabia.examples.rabianet
