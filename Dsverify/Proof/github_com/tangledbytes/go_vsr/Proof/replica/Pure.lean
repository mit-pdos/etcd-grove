/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Pure.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
Pure lemmas of the replica's proof: list facts, the store and the replies of an executed
prefix, the view-change selection loop's invariant (`SelInv`, giving `IsBest`), the model steps'
frame conditions (what `ghost_step` asks besides `*_inv`), and the client table's coverage.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Model.Basic

@[expose] public section

namespace VsrReplica

open VsrModel

/-! ## Lists -/

theorem prefix_eq_take {α} {l m : List α} (h : l <+: m) : l = m.take l.length :=
  List.prefix_iff_eq_take.mp h

theorem take_prefix_of_le {α} (l : List α) {i j : Nat} (h : i ≤ j) : l.take i <+: l.take j := by
  rw [show l.take i = (l.take j).take i by rw [List.take_take]; congr 1; omega]
  exact List.take_prefix _ _

theorem take_succ_eq {α} (l : List α) (k : Nat) (e : α) (he : l[k]? = some e) :
    l.take (k + 1) = l.take k ++ [e] := by
  rw [List.take_add_one, he]; rfl

/-- A prefix `mine` of `l` of length `k - 1` extends by `l`'s `k`-th entry to `l.take k`. -/
theorem prefix_take_succ {α} {mine l : List α} (h : mine <+: l) (e : α)
    (he : l[mine.length]? = some e) : l.take (mine.length + 1) = mine ++ [e] := by
  rw [take_succ_eq l _ e he, ← prefix_eq_take h]

/-! ## The store and replies -/

theorem storeOf_append_one (l : List Entry) (e : Entry) :
    storeOf (l ++ [e]) = (handle (storeOf l) e.op).1 := by
  simp [storeOf, List.foldl_append]

/-- The reply of the last entry of `mine ++ [e]` is the store's reply on `e`. -/
theorem outOf_last (mine : List Entry) (e : Entry) :
    outOf (mine ++ [e]) mine.length = (handle (storeOf mine) e.op).2 := by
  unfold outOf
  simp

/-- `ghost_lin`'s reply string at the `k`-th op of `l` extending `mine` is the store's. -/
theorem outOf_lin {mine l : List Entry} (h : mine <+: l) (e : Entry)
    (he : l[mine.length]? = some e) :
    outOf (l.take (mine.length + 1)) (mine.length + 1 - 1) = (handle (storeOf mine) e.op).2 ∧
    l.take (mine.length + 1) = mine ++ [e] := by
  have ht := prefix_take_succ h e he
  refine ⟨?_, ht⟩
  rw [ht, Nat.add_sub_cancel]
  exact outOf_last mine e

/-! ## Commitment -/

theorem committedBy_mono (s : Sys) {w v : Nat} (l : List Entry) (h : w ≤ v)
    (hc : CommittedBy s w l) : CommittedBy s v l := by
  obtain ⟨u, hu, hin⟩ := hc
  exact ⟨u, by omega, hin⟩

/-- All the replicas make a quorum (there is at least one). -/
theorem quorum_range (n : Nat) (hn : 0 < n) : Quorum n (List.range n) :=
  ⟨List.nodup_range, fun a ha => List.mem_range.mp ha, by simp; omega⟩

/-- The empty log is committed by any view (the system has at least one replica). -/
theorem committedBy_nil (s : Sys) (hn : 0 < s.n) (v : Nat) : CommittedBy s v [] :=
  ⟨0, Nat.zero_le _, List.range s.n, quorum_range s.n hn, fun _ _ => List.nil_prefix⟩

/-! ## The view change's selection loop (`finalizeViewChange`) -/

/-- The selection loop's invariant after the DoViewChanges `seen`: when one was seen (`found`),
the best one so far has last normal view `bl`, length `bo` and log `blog`, and is at least every
seen one; `bc` is the largest commit number seen (0 if none). -/
def SelInv (found : Bool) (bl bo bc : Nat) (blog : List Entry) (seen : List Dvc) : Prop :=
  (found = false ↔ seen = []) ∧
  (found = true → ∃ d ∈ seen, d.lnv = bl ∧ d.log.length = bo ∧ d.log = blog ∧
    ∀ d' ∈ seen, d'.lnv < bl ∨ (d'.lnv = bl ∧ d'.log.length ≤ bo)) ∧
  (∀ d' ∈ seen, d'.commit ≤ bc) ∧ (bc = 0 ∨ ∃ d ∈ seen, d.commit = bc)

theorem selInv_nil : SelInv false 0 0 0 [] [] := by
  refine ⟨by simp, by simp, by simp, Or.inl rfl⟩

/-- The selection replaces the best so far by `d`: none was found, or `d`'s `(lnv, length)` is
larger. -/
def SelNew (found : Bool) (bl bo : Nat) (d : Dvc) : Prop :=
  found = false ∨ bl < d.lnv ∨ (d.lnv = bl ∧ bo < d.log.length)

instance (found : Bool) (bl bo : Nat) (d : Dvc) : Decidable (SelNew found bl bo d) := by
  unfold SelNew; infer_instance

/-- One step of the loop on the DoViewChange `d`: the selection is replaced when `SelNew`; the
commit number when `d`'s is larger. -/
theorem selInv_step {found : Bool} {bl bo bc : Nat} {blog : List Entry} {seen : List Dvc}
    (h : SelInv found bl bo bc blog seen) (d : Dvc) :
    SelInv true (if SelNew found bl bo d then d.lnv else bl)
      (if SelNew found bl bo d then d.log.length else bo)
      (if bc < d.commit then d.commit else bc) (if SelNew found bl bo d then d.log else blog)
      (seen ++ [d]) := by
  obtain ⟨hf, hbest, hc, hc0⟩ := h
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro _
    by_cases hs : SelNew found bl bo d
    · simp only [hs, ↓reduceIte]
      refine ⟨d, by simp, rfl, rfl, rfl, ?_⟩
      intro d' hd'
      rcases List.mem_append.mp hd' with hd' | hd'
      · cases found with
        | false => have := hf.mp rfl; subst this; simp at hd'
        | true =>
          obtain ⟨d0, -, h1, h2, -, hall⟩ := hbest rfl
          have := hall d' hd'
          simp only [SelNew, Bool.true_eq_false, false_or] at hs
          omega
      · simp at hd'; subst hd'; right; exact ⟨rfl, Nat.le_refl _⟩
    · simp only [hs, ↓reduceIte]
      cases found with
      | false => exact absurd (Or.inl rfl) hs
      | true =>
        obtain ⟨d0, hd0, h1, h2, h3, hall⟩ := hbest rfl
        refine ⟨d0, List.mem_append_left _ hd0, h1, h2, h3, ?_⟩
        intro d' hd'
        rcases List.mem_append.mp hd' with hd' | hd'
        · exact hall d' hd'
        · simp at hd'; subst hd'
          simp only [SelNew, Bool.true_eq_false, false_or, not_or, not_and, Nat.not_lt] at hs
          omega
  · intro d' hd'
    rcases List.mem_append.mp hd' with hd' | hd'
    · have := hc d' hd'; split <;> omega
    · simp at hd'; subst hd'; split <;> omega
  · split
    · right; exact ⟨d, by simp, rfl⟩
    · rcases hc0 with h0 | ⟨d0, hd0, h0⟩
      · left; exact h0
      · right; exact ⟨d0, List.mem_append_left _ hd0, h0⟩

/-- At the end of the loop: the selected log is the best (`IsBest`), and the commit number is one
of the seen ones' (or 0) and at least each. -/
theorem isBest_of_selInv {bl bo bc : Nat} {blog : List Entry} {seen : List Dvc}
    (h : SelInv true bl bo bc blog seen) :
    IsBest seen blog ∧ (∀ d' ∈ seen, d'.commit ≤ bc) ∧ (bc = 0 ∨ ∃ d ∈ seen, d.commit = bc) := by
  obtain ⟨-, hbest, hc, hc0⟩ := h
  obtain ⟨d, hd, h1, h2, h3, hall⟩ := hbest rfl
  refine ⟨⟨d, hd, h3, ?_⟩, hc, hc0⟩
  intro d' hd'
  rcases hall d' hd' with h | ⟨h, h'⟩
  · left; omega
  · right; exact ⟨by omega, by rw [← h3]; omega⟩

theorem selInv_ne_nil {bl bo bc : Nat} {blog : List Entry} {seen : List Dvc}
    (h : SelInv true bl bo bc blog seen) : seen ≠ [] := by
  intro hs; have := h.1.mpr hs; simp at this

/-- The DoViewChanges' distinct replica ids (their keys), more than half of `n`, make a
quorum. -/
theorem quorum_of_rids (n : Nat) (ds : List Dvc) (hlt : ∀ d ∈ ds, d.rid < n) (ids : List Nat)
    (hids : ds.map (·.rid) = ids) (hnd : ids.Nodup) (hmaj : n < 2 * ids.length) :
    ∃ Q, Quorum n Q ∧ ∀ a ∈ Q, ∃ d ∈ ds, d.rid = a := by
  subst hids
  refine ⟨ds.map (·.rid), ⟨hnd, ?_, hmaj⟩, ?_⟩
  · intro a ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    exact hlt d hd
  · intro a ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    exact ⟨d, hd, rfl⟩

/-- The new primary's commit number: committed in the selected log. -/
theorem finalize_commit (s : Sys) (h : Inv s) (r v : Nat) (ds : List Dvc) (l : List Entry)
    (bc : Nat) (hr : r < s.n) (hp : primary s.n v = r) (hvc : (s.reps r).status = .viewChange)
    (hv : (s.reps r).view ≤ v) (hds : ∀ d ∈ ds, d.view = v ∧ DvcValid s d)
    (hq : ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, ∃ d ∈ ds, d.rid = a)
    (hbest : IsBest ds l) (hc0 : bc = 0 ∨ ∃ d ∈ ds, d.commit = bc) :
    bc ≤ l.length ∧ CommittedBy s v (l.take bc) := by
  rcases hc0 with h0 | ⟨d, hd, hdc⟩
  · subst h0; exact ⟨Nat.zero_le _, by simpa using committedBy_nil s (by omega) v⟩
  · subst hdc; exact finalize_committed s r v ds l h hr hp hvc hv hds hq hbest d hd

/-! ## Frame conditions of the model steps (what `ghost_step` asks besides `*_inv`) -/

theorem stepFinalize_frame (s : Sys) (r v : Nat) (l : List Entry) :
    (stepFinalize s r v l).reps r = { s.reps r with view := v, status := .normal, log := l } ∧
    (∀ x, x ≠ r → (stepFinalize s r v l).reps x = s.reps x) ∧
    (stepFinalize s r v l).lin = s.lin ∧ (stepFinalize s r v l).reg = s.reg ∧
    (stepFinalize s r v l).vinit v = some l := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · simp [stepFinalize, Sys.setRep, Sys.setAcc, Sys.setVlog]
  · intro x hx; simp [stepFinalize, Sys.setRep, Sys.setAcc, Sys.setVlog, hx]
  · simp [stepFinalize, Sys.setRep, Sys.setAcc, Sys.setVlog]

theorem stepAppend_frame (s : Sys) (r : Nat) (e : Entry) :
    (stepAppend s r e).reps r = { s.reps r with log := (s.reps r).log ++ [e] } ∧
    (∀ x, x ≠ r → (stepAppend s r e).reps x = s.reps x) ∧
    (stepAppend s r e).lin = s.lin ∧ (stepAppend s r e).reg = s.reg := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [stepAppend, Sys.setRep, Sys.setAcc, Sys.setVlog]
  · intro x hx; simp [stepAppend, Sys.setRep, Sys.setAcc, Sys.setVlog, hx]

theorem stepAccept_frame (s : Sys) (r : Nat) (e : Entry) :
    (stepAccept s r e).reps r = { s.reps r with log := (s.reps r).log ++ [e] } ∧
    (∀ x, x ≠ r → (stepAccept s r e).reps x = s.reps x) ∧
    (stepAccept s r e).lin = s.lin ∧ (stepAccept s r e).reg = s.reg := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [stepAccept, Sys.setRep, Sys.setAcc]
  · intro x hx; simp [stepAccept, Sys.setRep, Sys.setAcc, hx]

theorem stepInitVC_frame (s : Sys) (r v : Nat) :
    (stepInitVC s r v).reps r = ⟨v, .viewChange, (s.reps r).log,
      if (s.reps r).status = .viewChange then (s.reps r).lnv else (s.reps r).view⟩ ∧
    (∀ x, x ≠ r → (stepInitVC s r v).reps x = s.reps x) ∧
    (stepInitVC s r v).lin = s.lin ∧ (stepInitVC s r v).reg = s.reg := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [stepInitVC, Sys.setRep]
  · intro x hx; simp [stepInitVC, Sys.setRep, hx]

theorem stepStartView_frame (s : Sys) (r v : Nat) (l : List Entry) :
    (stepStartView s r v l).reps r = { s.reps r with view := v, status := .normal, log := l } ∧
    (∀ x, x ≠ r → (stepStartView s r v l).reps x = s.reps x) ∧
    (stepStartView s r v l).lin = s.lin ∧ (stepStartView s r v l).reg = s.reg := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [stepStartView, Sys.setRep, Sys.setAcc]
  · intro x hx; simp [stepStartView, Sys.setRep, Sys.setAcc, hx]

theorem stepEnterST_frame (s : Sys) (r : Nat) :
    (stepEnterST s r).reps r = { s.reps r with status := .stateTransfer } ∧
    (∀ x, x ≠ r → (stepEnterST s r).reps x = s.reps x) ∧
    (stepEnterST s r).lin = s.lin ∧ (stepEnterST s r).reg = s.reg := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [stepEnterST, Sys.setRep]
  · intro x hx; simp [stepEnterST, Sys.setRep, hx]

theorem stepNewState_frame (s : Sys) (r : Nat) (logs : List Entry) :
    (stepNewState s r logs).reps r =
      { s.reps r with status := .normal, log := (s.reps r).log ++ logs } ∧
    (∀ x, x ≠ r → (stepNewState s r logs).reps x = s.reps x) ∧
    (stepNewState s r logs).lin = s.lin ∧ (stepNewState s r logs).reg = s.reg := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [stepNewState, Sys.setRep, Sys.setAcc]
  · intro x hx; simp [stepNewState, Sys.setRep, Sys.setAcc, hx]

/-! ## Facts from the invariant about one replica -/

theorem repInv_of (s : Sys) (h : Inv s) (r : Nat) (hr : r < s.n) : RepInv s r := h.1 r hr

/-- The system has at least one replica. -/
theorem n_pos (s : Sys) (h : Inv s) : 0 < s.n := h.2.2.2.2.2.2.2.2.2.2.2

/-- A replica in view change was last normal before its view. -/
theorem lnv_lt_view (s : Sys) (h : Inv s) (r : Nat) (hr : r < s.n)
    (hvc : (s.reps r).status = .viewChange) : (s.reps r).lnv < (s.reps r).view :=
  ((repInv_of s h r hr).2.2.2 hvc).1

/-- The primary of a started view `v` is past `v`, or in it and not changing views: a StartView
of `v` never reaches `v`'s primary in a state where it would install it. -/
theorem startView_not_primary (s : Sys) (h : Inv s) (v : Nat) (l : List Entry)
    (hinit : s.vinit v = some l) (r : Nat) (hp : primary s.n v = r)
    (hv : (s.reps r).view < v ∨ ((s.reps r).view = v ∧ (s.reps r).status = .viewChange)) :
    False := by
  have := h.2.2.2.2.2.1 v (by simp [hinit])
  rw [hp] at this
  rcases this with h1 | ⟨h1, h2⟩ <;> rcases hv with h3 | ⟨h3, h4⟩ <;> first | omega | exact h2 h4

end VsrReplica

namespace VsrReplica
open VsrModel

/-- Everything `finalizeViewChange` needs of the model, at its ghost step: the new primary `r`
(state `p`, in view change at a view up to `v`) with the DoViewChanges `seen` of `v` from distinct
replicas (`keys`, at least two) and the selection's result (`SelInv`): its executed prefix extends
the selected log, the commit number is within it, and the step `stepFinalize` is a valid ghost
step after which the StartView of `v` and the commit are valid. -/
theorem finalize_all (s : Sys) (h : Inv s) (r v : Nat) (p : Rep) (hrp : s.reps r = p)
    (hr : r < s.n) (hp : primary s.n v = r) (hvc : p.status = .viewChange) (hv : p.view ≤ v)
    (seen : List Dvc) (hds : ∀ d ∈ seen, d.view = v ∧ DvcValid s d) (keys : List Nat)
    (hids : seen.map (·.rid) = keys) (hnd : keys.Nodup) (hmaj : s.n < 2 * keys.length)
    (bl bo bc : Nat) (blog : List Entry) (hsel : SelInv true bl bo bc blog seen)
    (mine : List Entry) (mw : Nat) (hmw : mw ≤ p.lnv) (hm : CommittedBy s mw mine) :
    mine <+: blog ∧ bc ≤ blog.length ∧ bo = blog.length ∧
    Inv (stepFinalize s r v blog) ∧ Le s (stepFinalize s r v blog) ∧
    (stepFinalize s r v blog).reps r = { p with view := v, status := .normal, log := blog } ∧
    (∀ x, x ≠ r → (stepFinalize s r v blog).reps x = s.reps x) ∧
    (stepFinalize s r v blog).lin = s.lin ∧ (stepFinalize s r v blog).reg = s.reg ∧
    MsgValid (stepFinalize s r v blog) (.startView v blog.length bc blog r) ∧
    CommittedBy (stepFinalize s r v blog) v (blog.take bc) := by
  have hvc' : (s.reps r).status = .viewChange := by rw [hrp]; exact hvc
  have hv' : (s.reps r).view ≤ v := by rw [hrp]; exact hv
  have hq : ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, ∃ d ∈ seen, d.rid = a :=
    quorum_of_rids s.n seen (fun d hd => (hds d hd).2.1) keys hids hnd hmaj
  obtain ⟨hbest, hcle, hc0⟩ := isBest_of_selInv hsel
  obtain ⟨-, hb, -, -⟩ := hsel
  obtain ⟨d0, -, -, hlen0, hlog0, -⟩ := hb rfl
  have hbo : bo = blog.length := by rw [← hlen0, hlog0]
  have hlnv := lnv_lt_view s h r hr hvc'
  rw [hrp] at hlnv
  have hmine : mine <+: blog :=
    finalize_mine s r v seen blog mine h hr hp hvc' hv' hds hq hbest
      (committedBy_mono s mine (by omega) hm)
  obtain ⟨hcl, hcom⟩ := finalize_commit s h r v seen blog bc hr hp hvc' hv' hds hq hbest hc0
  obtain ⟨hinv, hle⟩ := stepFinalize_inv s r v seen blog h hr hp hvc' hv' hds hq hbest
  obtain ⟨hfr, hfo, hfl, hfg, hfi⟩ := stepFinalize_frame s r v blog
  refine ⟨hmine, hcl, hbo, hinv, hle, by rw [hfr, hrp], hfo, hfl, hfg, ?_, ?_⟩
  · exact ⟨hfi, rfl, hcl, holds_mono hle (.committedBy v _) hcom⟩
  · exact holds_mono hle (.committedBy v _) hcom

end VsrReplica

namespace VsrReplica
open VsrModel

/-- The normal primary's log is its view's log. -/
theorem primary_vlog (s : Sys) (h : Inv s) (r : Nat) (hr : r < s.n)
    (hn : (s.reps r).status = .normal) (hp : primary s.n (s.reps r).view = r) :
    s.vlog (s.reps r).view = some (s.reps r).log := by
  obtain ⟨L, I, hL, -, -, -, -, hpl⟩ := (repInv_of s h r hr).2.2.1 (Or.inl hn)
  rw [hL, hpl hp]

end VsrReplica
