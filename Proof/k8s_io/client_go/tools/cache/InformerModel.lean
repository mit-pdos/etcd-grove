/-
**The informer contract, as a pure model** (phase 4 of `notes/k8s-daemonset-plan.md`). Lean-first.

An informer of one resource of the model API server (`apimodel`: its table's change `log`, sorted
by version, `St.wf`) is, abstractly, three things (`Inf`): the indexer's contents and resource
version (`View`: the store's items by key and its version, `none` before the first list), the
FIFO's queued deltas (`Delta`: a watch event's change, a relist's `ReplacedAll` with the list's
objects and version, a bookmark's version), and the reflector's last seen version (`last`,
`Reflector.lastSyncResourceVersion`).

**The invariant** (`Inf.ok`): the store is the log's table at its version (`tableAt`: the replay
of the changes at or below it), and the queue is a `Chain` from the store's version to the
reflector's: each change the next one of the log after the version before it, each relist at a
version at least the one before it with the table there, each bookmark at a version with no change
between. What the code does to the three, and the lemmas that keep the invariant:
* the reflector enqueues a watch event: the next change after its last version (`ok_push_change`;
  the model's watch delivers exactly those, `apimodel.evStep`), or a bookmark (`ok_push_bookmark`);
* the reflector enqueues a relist's `Replace` at the list's version, the server's current one, at
  least every version it has seen (`ok_push_replaced`);
* the controller's loop pops a delta and the informer applies it to the store (`ok_pop`), the
  store's version never decreasing (`pop_rv_le`);
* the server appends changes, at versions after every version the informer has (`ok_extend`).

So **the contract**: at every point the store holds exactly `tableAt log v` with `v` its version,
and `v` only grows, across relists too (`View.le`). `synced_rv`: once the first `Replace` is
processed (`HasSynced`), the store has a version. The informer's Iris proofs (the reflector, the
FIFO, the shared informer) keep a ghost `Inf` and this invariant.

Two facts of the code this rests on, checked against it (2026-10-27): the store's resource version
after a deletion is the deleted object's (`cache.Delete` calls `DeleteWithObject`, and the model
logs a deletion with the object at the deletion's version), so a deletion's version is never lost;
and the model's first version is `1` (`St.empty`), so a list's version is never `"0"` (a watch from
`""`/`"0"` replays the objects as synthetic `ADDED` events in map order: their versions would not
be a chain; the reflector watches from a list's version, never `""`/`"0"`, on this model).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.State

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open apimodel

section model
variable [GooseExts]

/-- **The table at version `v`**: the replay of the log's changes at or below `v`. -/
def tableAt (l : List Change) (v : Nat) : GMap Key Obj :=
  replay (l.filter (fun c => decide (c.rv.toNat ≤ v)))

/-- `c` is the log's first change after version `u`. -/
def NextChange (l : List Change) (u : Nat) (c : Change) : Prop :=
  c ∈ l ∧ u < c.rv.toNat ∧ ∀ d ∈ l, u < d.rv.toNat → c.rv.toNat ≤ d.rv.toNat

/-- No change of the log between versions `u` and `v` (a bookmark from `u` at `v`). -/
def Quiet (l : List Change) (u v : Nat) : Prop :=
  u ≤ v ∧ ∀ d ∈ l, u < d.rv.toNat → v < d.rv.toNat

/-- **A FIFO delta**, abstractly: a watch event's change, a relist's objects (by key) at its
version (`ReplacedAll`), a bookmark's version. -/
inductive Delta where
  | change (c : Change)
  | replaced (M : GMap Key Obj) (v : Nat)
  | bookmark (v : Nat)

/-- **The store's view**: its items and its version (`none`: `""`, nothing listed yet). -/
structure View where
  items : GMap Key Obj
  rv : Option Nat

/-- A delta applied to the store (`processDeltas`: an `ADDED`/`MODIFIED` change's `Add`/`Update`,
a `DELETED` one's `Delete`, a `ReplacedAll`'s `Replace`, a `Bookmark`'s `Bookmark`). -/
def View.apply (s : View) : Delta → View
  | .change c => ⟨applyChange s.items c, some c.rv.toNat⟩
  | .replaced M v => ⟨M, some v⟩
  | .bookmark v => ⟨s.items, some v⟩

/-- The store is the log's table at its version. -/
def View.ok (l : List Change) (s : View) : Prop :=
  match s.rv with
  | none => s.items = ∅
  | some u => s.items = tableAt l u

/-- Versions, `none` (nothing listed) below every version. -/
def rvLe : Option Nat → Option Nat → Prop
  | none, _ => True
  | some _, none => False
  | some u, some v => u ≤ v

/-- **The queued deltas are a chain** from version `u` to version `w`. -/
def Chain (l : List Change) : Option Nat → List Delta → Option Nat → Prop
  | u, [], w => u = w
  | u, .change c :: ds, w =>
      (∃ u', u = some u' ∧ NextChange l u' c) ∧ Chain l (some c.rv.toNat) ds w
  | u, .replaced M v :: ds, w => rvLe u (some v) ∧ M = tableAt l v ∧ Chain l (some v) ds w
  | u, .bookmark v :: ds, w => (∃ u', u = some u' ∧ Quiet l u' v) ∧ Chain l (some v) ds w

/-- **An informer's abstract state**: the store, the FIFO's deltas, the reflector's last
version. -/
structure Inf where
  store : View
  fifo : List Delta
  last : Option Nat

/-- **The informer invariant.** -/
def Inf.ok (l : List Change) (s : Inf) : Prop := s.store.ok l ∧ Chain l s.store.rv s.fifo s.last

/-- The informer before its reflector's first list. -/
def Inf.init : Inf := ⟨⟨∅, none⟩, [], none⟩

theorem Inf.init_ok (l : List Change) : Inf.init.ok l := ⟨rfl, rfl⟩

/-! ### The log's tables -/

/-- In a sorted log, the changes at or below the next change after `u` are those at or below `u`
and it. -/
theorem filter_next (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (u : Nat) (c : Change) (hc : NextChange l u c) :
    l.filter (fun d => decide (d.rv.toNat ≤ c.rv.toNat)) =
      l.filter (fun d => decide (d.rv.toNat ≤ u)) ++ [c] := by
  obtain ⟨hmem, hu, hmin⟩ := hc
  induction l with
  | nil => simp at hmem
  | cons d l ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hd, hs⟩ := hs
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have h1 : l.filter (fun d => decide (d.rv.toNat ≤ c.rv.toNat)) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hd x hx; simp; omega
      have h2 : l.filter (fun d => decide (d.rv.toNat ≤ u)) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hd x hx; simp; omega
      simp [List.filter_cons, h1, h2]; omega
    · have hdc := hd c hmem'
      have hdu : d.rv.toNat ≤ u := by
        rcases Nat.lt_or_ge u d.rv.toNat with h | h
        · have := hmin d List.mem_cons_self h; omega
        · exact h
      have ih' := ih hs hmem' (fun x hx => hmin x (List.mem_cons_of_mem _ hx))
      simp only [List.filter_cons, show decide (d.rv.toNat ≤ c.rv.toNat) = true by simp; omega,
        show decide (d.rv.toNat ≤ u) = true by simp; omega, ite_true, ih', List.cons_append]

theorem tableAt_next (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (u : Nat) (c : Change) (hc : NextChange l u c) :
    tableAt l c.rv.toNat = applyChange (tableAt l u) c := by
  unfold tableAt replay
  rw [filter_next l hs u c hc, List.foldl_append]
  rfl

theorem tableAt_quiet (l : List Change) (u v : Nat) (hq : Quiet l u v) :
    tableAt l v = tableAt l u := by
  unfold tableAt
  congr 1
  apply List.filter_congr
  intro d hd
  have := hq.2 d hd
  have := hq.1
  by_cases h : d.rv.toNat ≤ u
  · simp only [decide_eq_decide]; omega
  · simp only [decide_eq_decide]; constructor
    · intro h'; have := this; have := hq.2 d hd (by omega); omega
    · intro h'; omega

/-- Changes appended after version `b` leave the tables at or below `b`. -/
theorem tableAt_append (l l' : List Change) (b v : Nat) (hv : v ≤ b)
    (hl' : ∀ c ∈ l', b < c.rv.toNat) : tableAt (l ++ l') v = tableAt l v := by
  unfold tableAt
  rw [List.filter_append]
  have : l'.filter (fun c => decide (c.rv.toNat ≤ v)) = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; have := hl' x hx; simp; omega
  rw [this, List.append_nil]

/-! ### The invariant's steps -/

/-- The chain's versions are below its end. -/
theorem Chain.le_last (l : List Change) :
    ∀ (u : Option Nat) (ds : List Delta) (w : Option Nat), Chain l u ds w → rvLe u w
  | none, [], w, h => by simp [rvLe]
  | some u, [], w, h => by simp only [Chain] at h; subst h; simp [rvLe]
  | u, .change c :: ds, w, ⟨⟨u', hu, hn⟩, hc⟩ => by
      have := Chain.le_last l _ ds w hc
      subst hu
      cases w with
      | none => simp [rvLe] at this
      | some w => simp only [rvLe] at this ⊢; have := hn.2.1; omega
  | u, .replaced M v :: ds, w, ⟨hle, _, hc⟩ => by
      have := Chain.le_last l _ ds w hc
      cases u with
      | none => simp [rvLe]
      | some u =>
        cases w with
        | none => simp [rvLe] at this
        | some w => simp only [rvLe] at this hle ⊢; omega
  | u, .bookmark v :: ds, w, ⟨⟨u', hu, hq⟩, hc⟩ => by
      have := Chain.le_last l _ ds w hc
      subst hu
      cases w with
      | none => simp [rvLe] at this
      | some w => simp only [rvLe] at this ⊢; have := hq.1; omega

/-- **The controller's loop pops a delta and the store applies it**: the invariant holds of the
store after it and the rest of the queue. -/
theorem ok_pop (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (st : View) (d : Delta) (ds : List Delta) (w : Option Nat)
    (h : Inf.ok l ⟨st, d :: ds, w⟩) : Inf.ok l ⟨st.apply d, ds, w⟩ := by
  obtain ⟨hst, hc⟩ := h
  cases d with
  | change c =>
    obtain ⟨⟨u, hu, hn⟩, hc⟩ := hc
    refine ⟨?_, hc⟩
    unfold View.ok at hst
    rw [hu] at hst
    show applyChange st.items c = tableAt l c.rv.toNat
    rw [hst, tableAt_next l hs u c hn]
  | replaced M v =>
    obtain ⟨_, hM, hc⟩ := hc
    exact ⟨hM, hc⟩
  | bookmark v =>
    obtain ⟨⟨u, hu, hq⟩, hc⟩ := hc
    refine ⟨?_, hc⟩
    unfold View.ok at hst
    rw [hu] at hst
    show st.items = tableAt l v
    rw [hst, tableAt_quiet l u v hq]

/-- **The store's version never decreases** when it applies the queue's next delta. -/
theorem pop_rv_le (l : List Change) (st : View) (d : Delta) (ds : List Delta) (w : Option Nat)
    (h : Inf.ok l ⟨st, d :: ds, w⟩) : rvLe st.rv (st.apply d).rv := by
  obtain ⟨_, hc⟩ := h
  cases d with
  | change c =>
    obtain ⟨⟨u, hu, hn⟩, _⟩ := hc
    show rvLe st.rv (some c.rv.toNat)
    rw [hu]; simp only [rvLe]; have := hn.2.1; omega
  | replaced M v => exact hc.1
  | bookmark v =>
    obtain ⟨⟨u, hu, hq⟩, _⟩ := hc
    show rvLe st.rv (some v)
    rw [hu]; exact hq.1

theorem chain_snoc (l : List Change) :
    ∀ (u : Option Nat) (ds : List Delta) (w : Option Nat) (d : Delta) (w' : Option Nat),
      Chain l u ds w → Chain l w [d] w' → Chain l u (ds ++ [d]) w'
  | u, [], w, d, w', h, h' => by simp only [Chain] at h; subst h; simpa using h'
  | u, .change c :: ds, w, d, w', ⟨h1, h2⟩, h' => ⟨h1, chain_snoc l _ ds w d w' h2 h'⟩
  | u, .replaced M v :: ds, w, d, w', ⟨h1, h2, h3⟩, h' => ⟨h1, h2, chain_snoc l _ ds w d w' h3 h'⟩
  | u, .bookmark v :: ds, w, d, w', ⟨h1, h2⟩, h' => ⟨h1, chain_snoc l _ ds w d w' h2 h'⟩

/-- **The reflector enqueues a watch event's change**: the log's next change after its last
version. -/
theorem ok_push_change (l : List Change) (s : Inf) (u : Nat) (c : Change)
    (h : s.ok l) (hu : s.last = some u) (hn : NextChange l u c) :
    Inf.ok l ⟨s.store, s.fifo ++ [.change c], some c.rv.toNat⟩ :=
  ⟨h.1, chain_snoc l _ _ _ _ _ h.2 ⟨⟨u, hu, hn⟩, rfl⟩⟩

/-- **The reflector enqueues a bookmark** at a version with no change since its last. -/
theorem ok_push_bookmark (l : List Change) (s : Inf) (u v : Nat)
    (h : s.ok l) (hu : s.last = some u) (hq : Quiet l u v) :
    Inf.ok l ⟨s.store, s.fifo ++ [.bookmark v], some v⟩ :=
  ⟨h.1, chain_snoc l _ _ _ _ _ h.2 ⟨⟨u, hu, hq⟩, rfl⟩⟩

/-- **The reflector enqueues a relist's `Replace`** at a version at least its last, with the
table there. -/
theorem ok_push_replaced (l : List Change) (s : Inf) (v : Nat)
    (h : s.ok l) (hv : rvLe s.last (some v)) :
    Inf.ok l ⟨s.store, s.fifo ++ [.replaced (tableAt l v) v], some v⟩ :=
  ⟨h.1, chain_snoc l _ _ _ _ _ h.2 ⟨hv, rfl, rfl⟩⟩

/-- The chain's steps are below its end, so changes appended after it keep it. -/
theorem chain_extend (l l' : List Change) (b : Nat) (hl' : ∀ c ∈ l', b < c.rv.toNat) :
    ∀ (u : Option Nat) (ds : List Delta) (w : Option Nat), rvLe w (some b) →
      Chain l u ds w → Chain (l ++ l') u ds w
  | u, [], w, _, h => h
  | u, .change c :: ds, w, hw, ⟨⟨u', hu, hn⟩, hc⟩ => by
      have hle := Chain.le_last l _ ds w hc
      have hcb : c.rv.toNat ≤ b := by
        cases w with
        | none => simp [rvLe] at hle
        | some w => simp only [rvLe] at hle hw; omega
      refine ⟨⟨u', hu, List.mem_append_left _ hn.1, hn.2.1, ?_⟩,
        chain_extend l l' b hl' _ ds w hw hc⟩
      intro d hd hud
      rcases List.mem_append.mp hd with hd | hd
      · exact hn.2.2 d hd hud
      · have := hl' d hd; omega
  | u, .replaced M v :: ds, w, hw, ⟨h1, h2, hc⟩ => by
      have hle := Chain.le_last l _ ds w hc
      have hvb : v ≤ b := by
        cases w with
        | none => simp [rvLe] at hle
        | some w => simp only [rvLe] at hle hw; omega
      exact ⟨h1, by rw [h2, tableAt_append l l' b v hvb hl'],
        chain_extend l l' b hl' _ ds w hw hc⟩
  | u, .bookmark v :: ds, w, hw, ⟨⟨u', hu, hq⟩, hc⟩ => by
      have hle := Chain.le_last l _ ds w hc
      have hvb : v ≤ b := by
        cases w with
        | none => simp [rvLe] at hle
        | some w => simp only [rvLe] at hle hw; omega
      refine ⟨⟨u', hu, hq.1, ?_⟩, chain_extend l l' b hl' _ ds w hw hc⟩
      intro d hd hud
      rcases List.mem_append.mp hd with hd | hd
      · exact hq.2 d hd hud
      · have := hl' d hd; omega

/-- **The server appends changes** at versions after `b`, which bounds the reflector's last
version: the invariant holds of the longer log. -/
theorem ok_extend (l l' : List Change) (s : Inf) (b : Nat) (h : s.ok l)
    (hw : rvLe s.last (some b)) (hl' : ∀ c ∈ l', b < c.rv.toNat) : s.ok (l ++ l') := by
  obtain ⟨hst, hc⟩ := h
  refine ⟨?_, chain_extend l l' b hl' _ _ _ hw hc⟩
  have hrv := Chain.le_last l _ _ _ hc
  unfold View.ok at hst ⊢
  cases hs : s.store.rv with
  | none => rw [hs] at hst; exact hst
  | some u =>
    rw [hs] at hst hrv
    dsimp only at hst ⊢
    have hub : u ≤ b := by
      cases hl : s.last with
      | none => rw [hl] at hrv; simp [rvLe] at hrv
      | some w => rw [hl] at hrv hw; simp only [rvLe] at hrv hw; omega
    rw [hst, tableAt_append l l' b u hub hl']

/-! ### The model's watch delivers the log's next change -/

/-- The log's change at a watch's cursor (`logStart l n`, the first after version `n`) is the next
change after `n`, and the cursor after it is the first after its version. -/
theorem next_logStart (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (n : Nat) (c : Change)
    (hc : l[(l.takeWhile (fun d => decide (d.rv.toNat ≤ n))).length]? = some c) :
    NextChange l n c ∧
      (l.takeWhile (fun d => decide (d.rv.toNat ≤ c.rv.toNat))).length =
        (l.takeWhile (fun d => decide (d.rv.toNat ≤ n))).length + 1 := by
  induction l with
  | nil => simp at hc
  | cons d l ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hd, hs⟩ := hs
    by_cases hdn : d.rv.toNat ≤ n
    · have hdn' : decide (d.rv.toNat ≤ n) = true := by simp; omega
      simp only [List.takeWhile_cons, hdn', ite_true, List.length_cons,
        List.getElem?_cons_succ] at hc ⊢
      obtain ⟨⟨hm, hlt, hmin⟩, hlen⟩ := ih hs hc
      refine ⟨⟨List.mem_cons_of_mem _ hm, hlt, ?_⟩, ?_⟩
      · intro e he hne
        rcases List.mem_cons.mp he with rfl | he
        · omega
        · exact hmin e he hne
      · simp only [show decide (d.rv.toNat ≤ c.rv.toNat) = true by simp; omega, ite_true,
          List.length_cons, hlen]
    · have hdn' : decide (d.rv.toNat ≤ n) = false := by simp; omega
      simp only [List.takeWhile_cons, hdn', Bool.false_eq_true, ite_false, List.length_nil,
        List.getElem?_cons_zero, Option.some.injEq] at hc ⊢
      subst hc
      refine ⟨⟨List.mem_cons_self, by omega, ?_⟩, ?_⟩
      · intro e he _
        rcases List.mem_cons.mp he with rfl | he
        · omega
        · have := hd e he; omega
      · have : l.takeWhile (fun e => decide (e.rv.toNat ≤ d.rv.toNat)) = [] := by
          cases l with
          | nil => rfl
          | cons e l' =>
            have := hd e List.mem_cons_self
            simp only [List.takeWhile_cons, show decide (e.rv.toNat ≤ d.rv.toNat) = false by
              simp; omega, Bool.false_eq_true, ite_false]
        simp [List.takeWhile_cons, this]

/-- A watch whose cursor has passed every change (`logStart l n = |l|`): every change of the log
is at or below `n` (so a bookmark then, at any later version, is `Quiet`). -/
theorem all_le_logStart (l : List Change) (n : Nat)
    (hend : (l.takeWhile (fun d => decide (d.rv.toNat ≤ n))).length = l.length) :
    ∀ d ∈ l, d.rv.toNat ≤ n := by
  induction l with
  | nil => simp
  | cons e l ih =>
    by_cases h : e.rv.toNat ≤ n
    · have h' : decide (e.rv.toNat ≤ n) = true := by simp; omega
      simp only [List.takeWhile_cons, h', ite_true, List.length_cons] at hend
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact h
      · exact ih (by omega) d hd
    · have h' : decide (e.rv.toNat ≤ n) = false := by simp; omega
      simp only [List.takeWhile_cons, h', Bool.false_eq_true, ite_false, List.length_nil,
        List.length_cons] at hend
      omega

/-- Hence a bookmark at `v ≥ n` from such a cursor is `Quiet`. -/
theorem quiet_of_all_le (l : List Change) (n v : Nat) (hnv : n ≤ v)
    (h : ∀ d ∈ l, d.rv.toNat ≤ n) : Quiet l n v :=
  ⟨hnv, fun d hd hlt => absurd (h d hd) (by omega)⟩

/-- **The first delta is a relist's**: from the empty store (no version), the queue's next delta is
a `ReplacedAll`. -/
theorem chain_none_head (l : List Change) (d : Delta) (ds : List Delta) (w : Option Nat)
    (h : Chain l none (d :: ds) w) : ∃ M v, d = .replaced M v := by
  cases d with
  | change c => obtain ⟨⟨u, hu, _⟩, _⟩ := h; cases hu
  | replaced M v => exact ⟨M, v, rfl⟩
  | bookmark v => obtain ⟨⟨u, hu, _⟩, _⟩ := h; cases hu

/-- **`synced_rv`**: once the store has applied a delta (`HasSynced` closes after the first
`Replace` is processed), it has a version, and keeps one. -/
theorem synced_rv (st : View) (d : Delta) : ∃ v, (st.apply d).rv = some v := by
  cases d <;> exact ⟨_, rfl⟩

/-- **The store's contents at its version**: the invariant's first half, unfolded. -/
theorem ok_store (l : List Change) (s : Inf) (u : Nat) (h : s.ok l) (hu : s.store.rv = some u) :
    s.store.items = tableAt l u := by
  have := h.1; unfold View.ok at this; rw [hu] at this; exact this

end model

end informer
end EtcdGrove
end Perennial
