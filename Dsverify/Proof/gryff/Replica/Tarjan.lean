/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Replica/Tarjan.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The executor's search (`Exec.strongconnect`, `src/gryff/epaxos-exec.go`) as a pure model: Tarjan's
strongly-connected-components search over the committed instances' dependency graph, with the
executed instances removed.

* `E u w`: instance `u` depends on `w` (an edge; for the replica, `w` is in `u`'s committed deps'
  ranges). Kept abstract here; the graph only grows while the search runs (instances get
  committed while the executor waits), and the edges of a visited instance never change
  (`TInv.mono`).
* `TState`: the executed instances `X` (in execution order), the stack `S` (bottom first), the
  instances' `Index` (`num`, 0 = not visited in this search) and `Lowlink` (`low`), the next index
  `idx`.
* `TInv E σ G`: the search's invariant, `G` the instances whose calls are in progress (gray).
* The steps the code takes, each a lemma: `visit` (push), `edge_done` (an executed dependency),
  `edge_onstack` (`w.Index != 0`), `edge_child` (after the recursive call), `finish_pop` (the
  component is found: `sccStep`), `finish_keep`.
* `sccStep E X L`: the component `L` popped after `X`: disjoint from `X`, closed under `E` up to `X`,
  strongly connected. What the replica gives the protocol's agreement (hub request H3).
-/
module

public import Perennial.Std.Word

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica

/-- An instance: (leader, slot). -/
abbrev Node := Int × Int

/-- Paths (reflexive, transitive). -/
inductive Reach (E : Node → Node → Prop) : Node → Node → Prop
  | refl (a : Node) : Reach E a a
  | step (a b c : Node) : E a b → Reach E b c → Reach E a c

theorem Reach.trans {E : Node → Node → Prop} {a b c : Node} (h1 : Reach E a b)
    (h2 : Reach E b c) : Reach E a c := by
  induction h1 with
  | refl => exact h2
  | step a b' _ hab _ ih => exact .step a b' c hab (ih h2)

theorem Reach.single {E : Node → Node → Prop} {a b : Node} (h : E a b) : Reach E a b :=
  .step a b b h (.refl b)

theorem Reach.mono {E E' : Node → Node → Prop} (hE : ∀ a b, E a b → E' a b) {a b : Node}
    (h : Reach E a b) : Reach E' a b := by
  induction h with
  | refl => exact .refl _
  | step a b c hab _ ih => exact .step a b c (hE a b hab) ih

/-- A component popped after the executed instances `X`. -/
def sccStep (E : Node → Node → Prop) (X L : List Node) : Prop :=
  L ≠ [] ∧ L.Nodup ∧ (∀ u ∈ L, u ∉ X) ∧ (∀ u ∈ L, ∀ w, E u w → w ∈ X ∨ w ∈ L) ∧
    (∀ u ∈ L, ∀ w ∈ L, Reach E u w)

/-- The search's state. -/
structure TState where
  X : List Node
  S : List Node
  num : Node → Nat
  low : Node → Nat
  idx : Nat

/-- A finished instance still on the stack: its lowlink is below its index, and each dependency is
executed or on the stack at an index at least its lowlink. -/
def fin (E : Node → Node → Prop) (σ : TState) (u : Node) : Prop :=
  σ.low u < σ.num u ∧ ∀ w, E u w → w ∈ σ.X ∨ (w ∈ σ.S ∧ σ.low u ≤ σ.num w)

/-- The search's invariant, `G` the instances whose calls are in progress. -/
structure TInv (E : Node → Node → Prop) (σ : TState) (G : List Node) : Prop where
  nodup : σ.S.Nodup
  notX : ∀ u ∈ σ.S, u ∉ σ.X
  numS : ∀ u ∈ σ.S, 0 < σ.num u ∧ σ.num u < σ.idx
  visited : ∀ u, σ.num u ≠ 0 → u ∉ σ.X → u ∈ σ.S
  sorted : σ.S.Pairwise (fun a b => σ.num a < σ.num b)
  lowS : ∀ u ∈ σ.S, σ.low u ≤ σ.num u ∧ ∃ w ∈ σ.S, σ.num w = σ.low u ∧ Reach E u w
  finS : ∀ u ∈ σ.S, u ∉ G → fin E σ u
  grayS : ∀ g ∈ G, g ∈ σ.S

/-- Updating a function at one point. -/
def upd (f : Node → Nat) (v : Node) (n : Nat) : Node → Nat := fun u => if u = v then n else f u

@[simp] theorem upd_eq (f : Node → Nat) (v : Node) (n : Nat) : upd f v n v = n := by simp [upd]
theorem upd_ne (f : Node → Nat) (v u : Node) (n : Nat) (h : u ≠ v) : upd f v n u = f u := by
  simp [upd, h]

/-! ## The start of a search -/

theorem TInv.start (E : Node → Node → Prop) (X : List Node) (num low : Node → Nat)
    (hvis : ∀ u, num u ≠ 0 → u ∈ X) :
    TInv E ⟨X, [], num, low, 1⟩ [] where
  nodup := List.nodup_nil
  notX := by simp
  numS := by simp
  visited u h hX := absurd (hvis u h) hX
  sorted := List.Pairwise.nil
  lowS := by simp
  finS := by simp
  grayS := by simp

/-! ## Visiting an instance (push) -/

/-- The state after visiting `v`. -/
def TState.visit (σ : TState) (v : Node) : TState :=
  ⟨σ.X, σ.S ++ [v], upd σ.num v σ.idx, upd σ.low v σ.idx, σ.idx + 1⟩

theorem num_lt_idx_of_S {E} {σ : TState} {G} (h : TInv E σ G) {u : Node} (hu : u ∈ σ.S) :
    σ.num u < σ.idx := (h.numS u hu).2

theorem not_S_of_num0 {E} {σ : TState} {G} (h : TInv E σ G) {u : Node} (hn : σ.num u = 0) :
    u ∉ σ.S := fun hu => by have := (h.numS u hu).1; omega

theorem TInv.visit {E} {σ : TState} {G} (h : TInv E σ G) (v : Node) (hX : v ∉ σ.X)
    (hn : σ.num v = 0) (hidx : 0 < σ.idx) : TInv E (σ.visit v) (G ++ [v]) := by
  have hvS : v ∉ σ.S := not_S_of_num0 h hn
  have hne : ∀ u ∈ σ.S, u ≠ v := fun u hu huv => hvS (huv ▸ hu)
  constructor
  · simp only [TState.visit]; exact List.nodup_append.2 ⟨h.nodup, by simp, by simpa using hne⟩
  · intro u hu; simp only [TState.visit, List.mem_append, List.mem_singleton] at hu ⊢
    rcases hu with hu | rfl
    · exact h.notX u hu
    · exact hX
  · intro u hu; simp only [TState.visit, List.mem_append, List.mem_singleton] at hu ⊢
    rcases hu with hu | rfl
    · rw [upd_ne _ _ _ _ (hne u hu)]; have := h.numS u hu; omega
    · simp; omega
  · intro u hnum hXu; simp only [TState.visit, List.mem_append, List.mem_singleton] at hnum hXu ⊢
    by_cases huv : u = v
    · exact .inr huv
    · rw [upd_ne _ _ _ _ huv] at hnum; exact .inl (h.visited u hnum hXu)
  · simp only [TState.visit]
    refine List.pairwise_append.2 ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · refine h.sorted.imp_of_mem ?_
      intro a b ha hb hab
      rw [upd_ne _ _ _ _ (hne a ha), upd_ne _ _ _ _ (hne b hb)]; exact hab
    · intro a ha b hb; simp at hb; subst hb
      rw [upd_ne _ _ _ _ (hne a ha), upd_eq]; exact num_lt_idx_of_S h ha
  · intro u hu; simp only [TState.visit, List.mem_append, List.mem_singleton] at hu ⊢
    rcases hu with hu | rfl
    · obtain ⟨hl, w, hw, hnw, hr⟩ := h.lowS u hu
      rw [upd_ne _ _ _ _ (hne u hu), upd_ne _ _ _ _ (hne u hu)]
      refine ⟨hl, w, .inl hw, ?_, hr⟩
      rw [upd_ne _ _ _ _ (hne w hw)]; exact hnw
    · simp only [upd_eq]; exact ⟨Nat.le_refl _, u, .inr rfl, by simp, .refl _⟩
  · intro u hu hG; simp only [TState.visit, List.mem_append, List.mem_singleton] at hu hG
    rcases hu with hu | rfl
    · have huv := hne u hu
      obtain ⟨hlt, hf⟩ := h.finS u hu (fun h' => hG (.inl h'))
      refine ⟨by simp only [TState.visit]; rw [upd_ne _ _ _ _ huv, upd_ne _ _ _ _ huv]; exact hlt,
        fun w hw => ?_⟩
      simp only [TState.visit, List.mem_append, List.mem_singleton]
      rcases hf w hw with hwX | ⟨hwS, hle⟩
      · exact .inl hwX
      · refine .inr ⟨.inl hwS, ?_⟩
        rw [upd_ne _ _ _ _ huv, upd_ne _ _ _ _ (hne w hwS)]; exact hle
    · exact absurd (.inr rfl) hG
  · intro g hg; simp only [TState.visit, List.mem_append, List.mem_singleton] at hg ⊢
    rcases hg with hg | rfl
    · exact .inl (h.grayS g hg)
    · exact .inr rfl

/-! ## Graph growth: the edges of the stack's instances do not change -/

theorem TInv.mono {E E' : Node → Node → Prop} {σ : TState} {G : List Node}
    (hE : ∀ a b, E a b → E' a b) (hS : ∀ u ∈ σ.S, ∀ w, E' u w → E u w) (h : TInv E σ G) :
    TInv E' σ G where
  nodup := h.nodup
  notX := h.notX
  numS := h.numS
  visited := h.visited
  sorted := h.sorted
  lowS u hu := by
    obtain ⟨hl, w, hw, hn, hr⟩ := h.lowS u hu
    exact ⟨hl, w, hw, hn, hr.mono hE⟩
  finS u hu hG := by
    obtain ⟨hlt, hf⟩ := h.finS u hu hG
    exact ⟨hlt, fun w hw => hf w (hS u hu w hw)⟩
  grayS := h.grayS

/-! ## The frame of one call: `strongconnect(v)` called in state `σ0` with gray `G` -/

/-- The loop invariant of `v`'s call: `done` are the dependencies handled so far. -/
structure LInv (E : Node → Node → Prop) (σ0 : TState) (G : List Node) (v : Node)
    (done : Node → Prop) (σ : TState) : Prop where
  inv : TInv E σ (G ++ [v])
  stk : ∃ T, σ.S = σ0.S ++ v :: T ∧ ∀ u ∈ T, σ.low v ≤ σ.low u ∧ Reach E v u
  Xpre : σ0.X <+: σ.X
  old : ∀ u ∈ σ0.S, σ.num u = σ0.num u ∧ σ.low u = σ0.low u
  numv : σ.num v = σ0.idx
  idxlt : σ0.idx < σ.idx
  part : ∀ w, E v w → done w → w ∈ σ.X ∨ (w ∈ σ.S ∧ σ.low v ≤ σ.num w)
  gray0 : ∀ g ∈ G, g ∈ σ0.S

/-- What a call of `strongconnect(v)` from state `σ0` (gray `G`) ends with: `v`'s component was
popped (`v` executed, the stack as before), or `v` stays on the stack, with the instances above it
reachable from it and lowlinks at least its own. -/
structure Post (E : Node → Node → Prop) (σ0 : TState) (G : List Node) (v : Node)
    (σ : TState) : Prop where
  inv : TInv E σ G
  Xpre : σ0.X <+: σ.X
  old : ∀ u ∈ σ0.S, σ.num u = σ0.num u ∧ σ.low u = σ0.low u
  idxlt : σ0.idx < σ.idx
  res : (σ.S = σ0.S ∧ v ∈ σ.X ∧ σ.low v = σ0.idx) ∨
    (∃ T, σ.S = σ0.S ++ v :: T ∧ σ.low v < σ.num v ∧ σ.num v = σ0.idx ∧
      ∀ u ∈ T, σ.low v ≤ σ.low u ∧ Reach E v u)

theorem LInv.mono {E E' : Node → Node → Prop} {σ0 σ : TState} {G : List Node} {v : Node}
    {done : Node → Prop} (hE : ∀ a b, E a b → E' a b) (hS : ∀ u ∈ σ.S, ∀ w, E' u w → E u w)
    (h : LInv E σ0 G v done σ) : LInv E' σ0 G v done σ where
  inv := h.inv.mono hE hS
  stk := by
    obtain ⟨T, hT, hT'⟩ := h.stk
    exact ⟨T, hT, fun u hu => ⟨(hT' u hu).1, (hT' u hu).2.mono hE⟩⟩
  Xpre := h.Xpre
  old := h.old
  numv := h.numv
  idxlt := h.idxlt
  part w hw hd := h.part w (hS v (by obtain ⟨T, hT, _⟩ := h.stk; rw [hT]; simp) w hw) hd
  gray0 := h.gray0

theorem Post.mono {E E' : Node → Node → Prop} {σ0 σ : TState} {G : List Node} {v : Node}
    (hE : ∀ a b, E a b → E' a b) (hS : ∀ u ∈ σ.S, ∀ w, E' u w → E u w)
    (h : Post E σ0 G v σ) : Post E' σ0 G v σ where
  inv := h.inv.mono hE hS
  Xpre := h.Xpre
  old := h.old
  idxlt := h.idxlt
  res := by
    rcases h.res with h1 | ⟨T, hT, h2, h3, h4⟩
    · exact .inl h1
    · exact .inr ⟨T, hT, h2, h3, fun u hu => ⟨(h4 u hu).1, (h4 u hu).2.mono hE⟩⟩

theorem LInv.init {E} {σ0 : TState} {G} (h : TInv E σ0 G) (v : Node) (hX : v ∉ σ0.X)
    (hn : σ0.num v = 0) (hidx : 0 < σ0.idx) : LInv E σ0 G v (fun _ => False) (σ0.visit v) where
  inv := h.visit v hX hn hidx
  stk := ⟨[], by simp [TState.visit], by simp⟩
  Xpre := List.prefix_refl _
  old u hu := by
    have huv : u ≠ v := fun e => not_S_of_num0 h hn (e ▸ hu)
    simp only [TState.visit]; exact ⟨upd_ne _ _ _ _ huv, upd_ne _ _ _ _ huv⟩
  numv := by simp [TState.visit]
  idxlt := by simp [TState.visit]
  part _ _ hd := hd.elim
  gray0 := h.grayS

theorem LInv.vS {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ) : v ∈ σ.S := by
  obtain ⟨T, hT, _⟩ := h.stk; rw [hT]; simp

/-- A dependency that is executed (`Status == EXECUTED`, or below `ExecedUpTo`). -/
theorem LInv.edge_done {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ) (w : Node)
    (hw : w ∈ σ.X) : LInv E σ0 G v (fun x => done x ∨ x = w) σ where
  inv := h.inv
  stk := h.stk
  Xpre := h.Xpre
  old := h.old
  numv := h.numv
  idxlt := h.idxlt
  part x hx hd := by
    rcases hd with hd | rfl
    · exact h.part x hx hd
    · exact .inl hw
  gray0 := h.gray0

/-- Lowering a gray instance's lowlink to an index on the stack it reaches. -/
theorem TInv.setLow {E} {σ : TState} {G : List Node} (h : TInv E σ G) (v : Node) (hvG : v ∈ G)
    (n : Nat) (hn : n ≤ σ.low v)
    (hw : n = σ.low v ∨ ∃ w ∈ σ.S, σ.num w = n ∧ Reach E v w) :
    TInv E { σ with low := upd σ.low v n } G where
  nodup := h.nodup
  notX := h.notX
  numS := h.numS
  visited := h.visited
  sorted := h.sorted
  lowS u hu := by
    simp only
    by_cases huv : u = v
    · subst huv; rw [upd_eq]
      refine ⟨Nat.le_trans hn (h.lowS u hu).1, ?_⟩
      rcases hw with rfl | hw
      · exact (h.lowS u hu).2
      · exact hw
    · rw [upd_ne _ _ _ _ huv]; exact h.lowS u hu
  finS u hu hG := by
    have huv : u ≠ v := fun e => hG (e ▸ hvG)
    obtain ⟨hlt, hf⟩ := h.finS u hu hG
    simp only [fin]; rw [upd_ne _ _ _ _ huv]; exact ⟨hlt, hf⟩
  grayS := h.grayS

theorem LInv.split {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ) :
    ∃ T, σ.S = σ0.S ++ v :: T ∧ v ∉ σ0.S ∧ v ∉ T ∧ (∀ u ∈ σ0.S, u ∉ T) ∧
      ∀ u ∈ T, σ.low v ≤ σ.low u ∧ Reach E v u := by
  obtain ⟨T, hT, hT'⟩ := h.stk
  have hnd := h.inv.nodup; rw [hT] at hnd
  obtain ⟨hnd1, hnd2, hdisj⟩ := List.nodup_append.1 hnd
  have hvT : v ∉ T := (List.nodup_cons.1 hnd2).1
  refine ⟨T, hT, fun hv => hdisj v hv v (by simp) rfl, hvT,
    fun u hu hu' => hdisj u hu u (by simp [hu']) rfl, hT'⟩

/-- Changing the handled dependencies to ones handled or executed. -/
theorem LInv.done_mono {E} {σ0 σ : TState} {G v} {D D' : Node → Prop} (h : LInv E σ0 G v D σ)
    (hD : ∀ w, E v w → D' w → D w ∨ w ∈ σ.X) : LInv E σ0 G v D' σ where
  inv := h.inv
  stk := h.stk
  Xpre := h.Xpre
  old := h.old
  numv := h.numv
  idxlt := h.idxlt
  part w hw hd := by
    rcases hD w hw hd with hd | hX
    · exact h.part w hw hd
    · exact .inl hX
  gray0 := h.gray0

/-- A dependency on the stack (`w.Index != 0`, not executed): `v.Lowlink = min(v.Lowlink, w.Index)`. -/
theorem LInv.edge_onstack {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ) (w : Node)
    (hE : E v w) (hX : w ∉ σ.X) (hn : σ.num w ≠ 0) :
    LInv E σ0 G v (fun x => done x ∨ x = w)
      { σ with low := upd σ.low v (min (σ.low v) (σ.num w)) } := by
  have hwS : w ∈ σ.S := h.inv.visited w hn hX
  obtain ⟨T, hT, hv0, hvT, hdisj, hT'⟩ := h.split
  have hmin : min (σ.low v) (σ.num w) ≤ σ.low v := Nat.min_le_left _ _
  constructor
  · refine h.inv.setLow v (by simp) _ hmin ?_
    by_cases hlt : σ.num w < σ.low v
    · exact .inr ⟨w, hwS, by omega, .single hE⟩
    · exact .inl (by omega)
  · refine ⟨T, hT, fun u hu => ?_⟩
    have huv : u ≠ v := fun e => hvT (e ▸ hu)
    simp only [upd_eq]; rw [upd_ne _ _ _ _ huv]
    exact ⟨Nat.le_trans hmin (hT' u hu).1, (hT' u hu).2⟩
  · exact h.Xpre
  · intro u hu
    have huv : u ≠ v := fun e => hv0 (e ▸ hu)
    simp only; rw [upd_ne _ _ _ _ huv]; exact h.old u hu
  · exact h.numv
  · exact h.idxlt
  · intro x hx hd; simp only [upd_eq]
    rcases hd with hd | rfl
    · rcases h.part x hx hd with h1 | ⟨h1, h2⟩
      · exact .inl h1
      · exact .inr ⟨h1, Nat.le_trans hmin h2⟩
    · exact .inr ⟨hwS, Nat.min_le_right _ _⟩
  · exact h.gray0

/-- A dependency visited by the recursive call (`w.Index == 0` before it): after it,
`v.Lowlink = min(v.Lowlink, w.Lowlink)`. -/
theorem LInv.edge_child {E} {σ0 σ σ' : TState} {G v done} (h : LInv E σ0 G v done σ) (w : Node)
    (hE : E v w) (hc : Post E σ (G ++ [v]) w σ') :
    LInv E σ0 G v (fun x => done x ∨ x = w)
      { σ' with low := upd σ'.low v (min (σ'.low v) (σ'.low w)) } := by
  obtain ⟨T, hT, hv0, hvT, hdisj, hT'⟩ := h.split
  have hvS : v ∈ σ.S := h.vS
  have hold := hc.old v hvS
  have hlowv : σ.low v ≤ σ.num v := (h.inv.lowS v hvS).1
  have hnumv : σ.num v < σ.idx := num_lt_idx_of_S h.inv hvS
  have hmin : min (σ'.low v) (σ'.low w) ≤ σ'.low v := Nat.min_le_left _ _
  have hXsub : ∀ x, x ∈ σ.X → x ∈ σ'.X := fun x hx => hc.Xpre.subset hx
  have hSsub : ∀ x, x ∈ σ.S → x ∈ σ'.S := by
    intro x hx
    rcases hc.res with ⟨h1, _⟩ | ⟨T', h1, _⟩ <;> rw [h1] <;> simp [hx]
  constructor
  · refine hc.inv.setLow v (by simp) _ hmin ?_
    rcases hc.res with ⟨h1, h2, h3⟩ | ⟨T', h1, h2, h3, h4⟩
    · exact .inl (by rw [h3, hold.2]; omega)
    · by_cases hlt : σ'.low w < σ'.low v
      · obtain ⟨_, x, hx, hnx, hr⟩ := hc.inv.lowS w (by rw [h1]; simp)
        exact .inr ⟨x, hx, by omega, .step v w x hE hr⟩
      · exact .inl (by omega)
  · rcases hc.res with ⟨h1, h2, h3⟩ | ⟨T', h1, h2, h3, h4⟩
    · refine ⟨T, by simp only; rw [h1, hT], fun u hu => ?_⟩
      have huv : u ≠ v := fun e => hvT (e ▸ hu)
      have huS : u ∈ σ.S := by rw [hT]; simp [hu]
      simp only [upd_eq]; rw [upd_ne _ _ _ _ huv, (hc.old u huS).2]
      exact ⟨Nat.le_trans hmin (by rw [hold.2]; exact (hT' u hu).1), (hT' u hu).2⟩
    · refine ⟨T ++ w :: T', by simp only; rw [h1, hT]; simp, fun u hu => ?_⟩
      simp only [upd_eq]
      rcases List.mem_append.1 hu with hu | hu
      · have huv : u ≠ v := fun e => hvT (e ▸ hu)
        have huS : u ∈ σ.S := by rw [hT]; simp [hu]
        rw [upd_ne _ _ _ _ huv, (hc.old u huS).2]
        exact ⟨Nat.le_trans hmin (by rw [hold.2]; exact (hT' u hu).1), (hT' u hu).2⟩
      · have hnd := hc.inv.nodup; rw [h1] at hnd
        have hv' : v ∉ w :: T' := by
          intro hv'; exact (List.nodup_append.1 hnd).2.2 v hvS v hv' rfl
        have huv : u ≠ v := fun e => hv' (e ▸ hu)
        rw [upd_ne _ _ _ _ huv]
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨Nat.min_le_right _ _, .single hE⟩
        · exact ⟨Nat.le_trans (Nat.min_le_right _ _) (h4 u hu).1, .step v w u hE (h4 u hu).2⟩
  · exact h.Xpre.trans hc.Xpre
  · intro u hu
    have huv : u ≠ v := fun e => hv0 (e ▸ hu)
    have huS : u ∈ σ.S := by rw [hT]; simp [hu]
    simp only; rw [upd_ne _ _ _ _ huv, (hc.old u huS).1, (hc.old u huS).2]; exact h.old u hu
  · simp only; rw [hold.1]; exact h.numv
  · exact Nat.lt_trans h.idxlt hc.idxlt
  · intro x hx hd; simp only [upd_eq]
    rcases hd with hd | rfl
    · rcases h.part x hx hd with h1 | ⟨h1, h2⟩
      · exact .inl (hXsub x h1)
      · refine .inr ⟨hSsub x h1, ?_⟩
        rw [(hc.old x h1).1]; exact Nat.le_trans hmin (by rw [hold.2]; exact h2)
    · rcases hc.res with ⟨h1, h2, h3⟩ | ⟨T', h1, h2, h3, h4⟩
      · exact .inl h2
      · exact .inr ⟨by rw [h1]; simp, Nat.le_trans (Nat.min_le_right _ _) (Nat.le_of_lt h2)⟩
  · exact h.gray0

/-- Every dependency handled, `v.Lowlink != v.Index`: `v` stays on the stack. -/
theorem LInv.finish_keep {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ)
    (hall : ∀ w, E v w → done w) (hne : σ.low v ≠ σ.num v) : Post E σ0 G v σ := by
  obtain ⟨T, hT, hv0, hvT, hdisj, hT'⟩ := h.split
  have hvS := h.vS
  have hlt : σ.low v < σ.num v := by have := (h.inv.lowS v hvS).1; omega
  refine ⟨⟨h.inv.nodup, h.inv.notX, h.inv.numS, h.inv.visited, h.inv.sorted, h.inv.lowS,
    fun u hu hG => ?_, fun g hg => h.inv.grayS g (by simp [hg])⟩, h.Xpre, h.old, h.idxlt,
    .inr ⟨T, hT, hlt, h.numv, hT'⟩⟩
  by_cases huv : u = v
  · subst huv; exact ⟨hlt, fun w hw => h.part w hw (hall w hw)⟩
  · exact h.inv.finS u hu (by simp [hG, huv])

/-- Instances on the stack above `v`'s position have indices at least `v`'s. -/
theorem LInv.num_ge {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ) :
    ∀ T, σ.S = σ0.S ++ v :: T → ∀ u ∈ T, σ.num v < σ.num u := by
  intro T hT u hu
  have hs := h.inv.sorted; rw [hT] at hs
  have := (List.pairwise_append.1 hs).2.1
  exact (List.pairwise_cons.1 this).1 u hu

/-- Instances of the stack below `v`'s position have indices below `v`'s. -/
theorem LInv.num_old_lt {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ) :
    ∀ u ∈ σ0.S, σ.num u < σ.num v := by
  intro u hu
  rw [(h.old u hu).1, h.numv]
  have hS0 : u ∈ σ.S := by obtain ⟨T, hT, _⟩ := h.stk; rw [hT]; simp [hu]
  have := h.inv
  have hs := h.inv.sorted
  obtain ⟨T, hT, _⟩ := h.stk
  rw [hT] at hs
  have := (List.pairwise_append.1 hs).2.2 u hu v (by simp)
  rw [(h.old u hu).1, h.numv] at this; exact this

/-- Every dependency handled, `v.Lowlink == v.Index`: the instances from `v` up are a component
(`sccStep`), and executing them in any order (`Ls`, a permutation) and popping them ends the
call. -/
theorem LInv.finish_pop {E} {σ0 σ : TState} {G v done} (h : LInv E σ0 G v done σ)
    (hall : ∀ w, E v w → done w) (heq : σ.low v = σ.num v) :
    ∃ T, σ.S = σ0.S ++ v :: T ∧ sccStep E σ.X (v :: T) ∧
      ∀ Ls, Ls.Perm (v :: T) → Post E σ0 G v { σ with X := σ.X ++ Ls, S := σ0.S } := by
  obtain ⟨T, hT, hv0, hvT, hdisj, hT'⟩ := h.split
  have hvS := h.vS
  have hge := h.num_ge T hT
  have hlt0 := h.num_old_lt
  -- a stack instance at an index at least `v`'s is in the component
  have hinL : ∀ w ∈ σ.S, σ.num v ≤ σ.num w → w ∈ v :: T := by
    intro w hw hle
    rw [hT] at hw
    rcases List.mem_append.1 hw with hw | hw
    · have := hlt0 w hw; omega
    · exact hw
  have hfinT : ∀ u ∈ T, fin E σ u := by
    intro u hu
    have huv : u ≠ v := fun e => hvT (e ▸ hu)
    have huG : u ∉ G := fun hg => hdisj u (h.gray0 u hg) hu
    exact h.inv.finS u (by rw [hT]; simp [hu]) (by simp [huG, huv])
  have hlowL : ∀ u ∈ v :: T, σ.num v ≤ σ.low u := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · omega
    · rw [← heq]; exact (hT' u hu).1
  -- every instance of the component reaches `v`
  have hback : ∀ n, ∀ u ∈ v :: T, σ.num u ≤ n → Reach E u v := by
    intro n
    induction n with
    | zero =>
      intro u hu hn
      rcases List.mem_cons.1 hu with rfl | hu
      · exact .refl _
      · have := hge u hu; omega
    | succ n ih =>
      intro u hu hn
      rcases List.mem_cons.1 hu with rfl | hu
      · exact .refl _
      · obtain ⟨hlt, _⟩ := hfinT u hu
        obtain ⟨_, x, hx, hnx, hr⟩ := h.inv.lowS u (by rw [hT]; simp [hu])
        have hxL := hinL x hx (by have := hlowL u (by simp [hu]); omega)
        exact hr.trans (ih x hxL (by omega))
  have hfwd : ∀ u ∈ v :: T, Reach E v u := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact .refl _
    · exact (hT' u hu).2
  have hnd : (v :: T).Nodup := by
    have := h.inv.nodup; rw [hT] at this; exact (List.nodup_append.1 this).2.1
  have hnotX : ∀ u ∈ v :: T, u ∉ σ.X := fun u hu => h.inv.notX u (by rw [hT]; simp [hu])
  refine ⟨T, hT, ⟨by simp, hnd, hnotX, ?_, ?_⟩, ?_⟩
  · -- closed
    intro u hu w hw
    have hfu : w ∈ σ.X ∨ (w ∈ σ.S ∧ σ.low u ≤ σ.num w) := by
      rcases List.mem_cons.1 hu with rfl | hu
      · exact h.part w hw (hall w hw)
      · exact (hfinT u hu).2 w hw
    rcases hfu with hX | ⟨hwS, hle⟩
    · exact .inl hX
    · exact .inr (hinL w hwS (Nat.le_trans (hlowL u hu) hle))
  · intro u hu w hw
    exact (hback _ u hu (Nat.le_refl _)).trans (hfwd w hw)
  · intro Ls hperm
    have hmemLs : ∀ x, x ∈ Ls ↔ x ∈ v :: T := fun x => hperm.mem_iff
    have hS0sub : ∀ u ∈ σ0.S, u ∈ σ.S := fun u hu => by rw [hT]; simp [hu]
    have hS0L : ∀ u ∈ σ0.S, u ∉ v :: T := by
      intro u hu hu'
      rcases List.mem_cons.1 hu' with rfl | hu'
      · exact hv0 hu
      · exact hdisj u hu hu'
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h.old, h.idxlt, .inl ⟨rfl, ?_, ?_⟩⟩
    · have := h.inv.nodup; rw [hT] at this; exact (List.nodup_append.1 this).1
    · intro u hu hX
      rcases List.mem_append.1 hX with hX | hX
      · exact h.inv.notX u (hS0sub u hu) hX
      · exact hS0L u hu ((hmemLs u).1 hX)
    · intro u hu
      exact ⟨(h.inv.numS u (hS0sub u hu)).1, (h.inv.numS u (hS0sub u hu)).2⟩
    · intro u hn hX
      have hX1 : u ∉ σ.X := fun h' => hX (List.mem_append_left _ h')
      have hX2 : u ∉ v :: T := fun h' => hX (List.mem_append_right _ ((hmemLs u).2 h'))
      have := h.inv.visited u hn hX1
      rw [hT] at this
      rcases List.mem_append.1 this with h' | h'
      · exact h'
      · exact absurd h' hX2
    · have := h.inv.sorted; rw [hT] at this; exact (List.pairwise_append.1 this).1
    · intro u hu
      obtain ⟨hl, x, hx, hnx, hr⟩ := h.inv.lowS u (hS0sub u hu)
      refine ⟨hl, x, ?_, hnx, hr⟩
      have hxlt : σ.num x < σ.num v := by have := hlt0 u hu; omega
      rw [hT] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · have := hge x hx; omega
    · intro u hu hG
      have huv : u ≠ v := fun e => hv0 (e ▸ hu)
      obtain ⟨hlt, hf⟩ := h.inv.finS u (hS0sub u hu) (by simp [hG, huv])
      refine ⟨hlt, fun w hw => ?_⟩
      rcases hf w hw with hX | ⟨hwS, hle⟩
      · exact .inl (List.mem_append_left _ hX)
      · rw [hT] at hwS
        rcases List.mem_append.1 hwS with hwS | hwS
        · exact .inr ⟨hwS, hle⟩
        · exact .inl (List.mem_append_right _ ((hmemLs w).2 hwS))
    · exact h.gray0
    · exact h.Xpre.trans (List.prefix_append _ _)
    · exact List.mem_append_right _ ((hmemLs v).2 (by simp))
    · simp only; rw [heq, h.numv]

/-- A search started on an empty stack pops its root's component. -/
theorem Post.root_popped {E} {σ0 σ : TState} {v : Node} (h : Post E σ0 [] v σ)
    (hS0 : σ0.S = []) : σ.S = [] ∧ v ∈ σ.X := by
  rcases h.res with ⟨h1, h2, _⟩ | ⟨T, hT, hlt, _, _⟩
  · exact ⟨hS0 ▸ h1, h2⟩
  · exfalso
    rw [hS0, List.nil_append] at hT
    obtain ⟨_, x, hx, hnx, _⟩ := h.inv.lowS v (by rw [hT]; simp)
    rw [hT] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have hs := h.inv.sorted; rw [hT] at hs
      have := (List.pairwise_cons.1 hs).1 x hx
      omega

end Perennial.gryff.replica
