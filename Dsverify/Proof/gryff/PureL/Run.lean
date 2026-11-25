/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/Run.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: runs, cut by cut. A run's label `n` is a step of replica `r` from `cutSt l n r`, `.ok`,
whose result is `cutSt l (n+1) r` and whose outputs are `outsAt l n`; the other replicas' states do
not change. (Self-contained: does not use `kahn.grun_state`.)
-/
module

public import Dsverify.Proof.gryff.Pure.Run

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn

theorem grun_append {c c'' : Cfg gNet} {l1 l2 : List Label} (h : GRun c (l1 ++ l2) c'') :
    ∃ c', GRun c l1 c' ∧ GRun c' l2 c'' := by
  induction l1 generalizing c with
  | nil => exact ⟨c, GRun.nil c, h⟩
  | cons x l1 ih =>
    cases h with
    | cons hs hr =>
      obtain ⟨c', h1, h2⟩ := ih hr
      exact ⟨c', GRun.cons hs h1, h2⟩

theorem grun_snoc {c c' c'' : Cfg gNet} {l : List Label} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun c l c') (hs : GStep c' i e c'' x) : GRun c (l ++ [(i, e)]) c'' := by
  induction h with
  | nil c => exact GRun.cons hs (GRun.nil _)
  | cons hs' _ ih => exact GRun.cons hs' (ih hs)

theorem runFrom_snoc (i : Fin 3) (s : gNet.S) (es : List Ev) (e : Ev) :
    runFrom gNet i s (es ++ [e]) =
      (runFrom gNet i s es).bind fun r =>
        (gNet.step i r.1 e).map fun r' => (r'.1, r.2 ++ r'.2) := by
  induction es generalizing s with
  | nil =>
    simp only [List.nil_append, runFrom]
    rcases hst : gNet.step i s e with _ | ⟨s', o⟩ <;> simp [hst]
  | cons e0 es ih =>
    simp only [List.cons_append, runFrom]
    rcases hst : gNet.step i s e0 with _ | ⟨s', o⟩
    · rfl
    · simp only
      rw [ih s']
      rcases runFrom gNet i s' es with _ | ⟨s1, o1⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some]
        rcases gNet.step i s1 e with _ | ⟨s2, o2⟩ <;> simp
theorem proj_append (l l' : List Label) (r : Fin 3) :
    projR (l ++ l') r = projR l r ++ projR l' r := by
  unfold projR proj
  exact (congrArg (List.map Prod.snd) (List.filter_append ..)).trans (List.map_append ..)
theorem proj_single (i r : Fin 3) (e : Ev) :
    projR [(i, e)] r = if i = r then [e] else [] := by
  show List.map Prod.snd (List.filter (fun x : Fin 3 × Ev => decide (x.1 = r)) [(i, e)]) = _
  by_cases h : i = r <;> simp [h]
theorem runP_snoc {r : Fin 3} {es : List Ev} {e : Ev} {s s' : RState} {o o' : List Out}
    (h0 : runP gNet r es = some (s, o)) (hs : gStep r s e = some (s', o')) :
    runP gNet r (es ++ [e]) = some (s', o ++ o') := by
  unfold runP at h0 ⊢
  rw [runFrom_snoc, h0]
  show Option.map (fun r' => (r'.1, o ++ r'.2)) (gStep r s e) = _
  rw [hs]; rfl

theorem proj_snoc (l : List Label) (i r : Fin 3) (e : Ev) :
    projR (l ++ [(i, e)]) r = if i = r then projR l r ++ [e] else projR l r := by
  rw [proj_append, proj_single]; split <;> simp

theorem grun_of_eq {c c' : Cfg gNet} {l l' : List Label} (e : l = l') (h : GRun c l c') :
    GRun c l' c' := e ▸ h

theorem grun_cons_inv {c c' : Cfg gNet} {x : Label} {rest : List Label} (h : GRun c (x :: rest) c') :
    ∃ c1 xx, GStep c x.1 x.2 c1 xx ∧ GRun c1 rest c' := by
  cases h with
  | cons hs hr => exact ⟨_, _, hs, hr⟩

theorem runP_nil (r : Fin 3) : runP gNet r (projR ([] : List Label) r) = some (gNet.init r, []) := rfl

/-- The configuration after the first `n` labels of a run holds the replicas' states `cutSt`. -/
theorem grun_cut {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (n : Nat) :
    ∃ cn, GRun (Cfg.init gNet) (l.take n) cn ∧ GRun cn (l.drop n) c ∧
      ∀ r : Fin 3, ∃ o, runP gNet r (projR (l.take n) r) = some (cn.st r, o) := by
  induction n with
  | zero =>
    exact ⟨Cfg.init gNet, GRun.nil _, h, fun (r : Fin 3) => ⟨[], runP_nil r⟩⟩
  | succ n ih =>
    obtain ⟨cn, h1, h2, h3⟩ := ih
    cases hd : l.drop n with
    | nil =>
      have : l.length ≤ n := by simpa using hd
      have e1 : l.take (n + 1) = l.take n := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      have e2 : l.drop (n + 1) = [] := by simp; omega
      have h2' := grun_of_eq hd h2
      cases h2'
      refine ⟨c, grun_of_eq e1.symm h1, grun_of_eq e2.symm (GRun.nil _), ?_⟩
      rw [e1]; exact h3
    | cons x rest =>
      obtain ⟨c1, xx, hs, hr⟩ := grun_cons_inv (grun_of_eq hd h2)
      obtain ⟨i, e⟩ := x
      have hx : l[n]? = some (i, e) := by
        rw [← List.head?_drop, hd]; rfl
      have et : l.take (n + 1) = l.take n ++ [(i, e)] := by
        rw [List.take_add_one, hx]; rfl
      have ed : l.drop (n + 1) = rest := by
        rw [← List.drop_drop, hd]; rfl
      refine ⟨c1, grun_of_eq et.symm (grun_snoc h1 hs), grun_of_eq ed.symm hr, fun (r : Fin 3) => ?_⟩
      obtain ⟨s', o, hst, -, -, hst', -⟩ := hs
      change gStep i (cn.st i) e = some (s', o) at hst
      rw [et, proj_snoc]
      obtain ⟨o0, h0⟩ := h3 r
      by_cases hir : i = r
      · subst hir
        refine ⟨o0 ++ o, ?_⟩
        rw [if_pos rfl]
        have : c1.st i = s' := by rw [hst']; exact if_pos rfl
        rw [this]; exact runP_snoc h0 hst
      · refine ⟨o0, ?_⟩
        rw [if_neg hir]
        have : c1.st r = cn.st r := by rw [hst']; exact if_neg (Ne.symm hir)
        rw [this]; exact h0

theorem stOf_of_runP {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : runP gNet r es = some (s, o)) : stOf r es = s := by
  simp [stOf, h]

/-- **A run's label `n`**: replica `r`'s step from `cutSt l n r` is `.ok`, its result is the
state at `n + 1`, its outputs are `outsAt l n`; the other replicas do not move. -/
theorem grun_label {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {n : Nat}
    {r : Fin 3} {e : Ev} (hn : l[n]? = some (r, e)) :
    ∃ s' o, stepR r (cutSt l n r) e = .ok (s', o) ∧ cutSt l (n + 1) r = s' ∧
      (∀ q, q ≠ r → cutSt l (n + 1) q = cutSt l n q) ∧ outsAt l n = o ∧
      (∀ m, e.recv = some m → ∃ cn : Cfg gNet, m ∈ cn.inflight r ∧
        GRun (Cfg.init gNet) (l.take n) cn) := by
  obtain ⟨cn, h1, h2, h3⟩ := grun_cut h n
  have hd : l.drop n = (r, e) :: l.drop (n + 1) := by
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hn
    rw [List.drop_eq_getElem_cons hlt, he]
  obtain ⟨c1, xx, hs, -⟩ := grun_cons_inv (grun_of_eq hd h2)
  · obtain ⟨s', o, hst, hrecv, -, hst', -⟩ := hs
    change gStep r (cn.st r) e = some (s', o) at hst
    change ∀ m, e.recv = some m → m ∈ cn.inflight r at hrecv
    change c1.st = fun j => if j = r then s' else cn.st j at hst' 
    have hc : ∀ q : Fin 3, cutSt l n q = cn.st q := fun q => by
      obtain ⟨o', h'⟩ := h3 q; exact stOf_of_runP h'
    have et : l.take (n + 1) = l.take n ++ [(r, e)] := by
      rw [List.take_add_one, hn]; rfl
    have hok : stepR r (cn.st r) e = .ok (s', o) := by
      unfold gStep at hst
      cases hres : stepR r (cn.st r) e with
      | error f => rw [hres] at hst; cases hst
      | ok p => rw [hres] at hst; cases hst; rfl
    refine ⟨s', o, by rw [hc]; exact hok, ?_, ?_, ?_, ?_⟩
    · obtain ⟨o0, h0⟩ := h3 r
      unfold cutSt; rw [et, proj_snoc, if_pos rfl]
      exact stOf_of_runP (runP_snoc h0 hst)
    · intro q hq
      unfold cutSt; rw [et, proj_snoc, if_neg (Ne.symm hq)]
    · simp only [outsAt, hn]
      rw [show stOf r (projR (l.take n) r) = cn.st r from hc r, hok]
    · intro m hm; exact ⟨cn, hrecv m hm, h1⟩

end Perennial.gryff.pure

namespace Perennial.gryff.pure

open model kahn

/-- Replica `r`'s `j`-th event in a run is some label `n` of it, with `r`'s first `j` events
before it. -/
theorem snoc_ind {α : Type} {P : List α → Prop} (h0 : P [])
    (hs : ∀ l x, P l → P (l ++ [x])) (l : List α) : P l := by
  rw [← List.reverse_reverse l]
  generalize l.reverse = m
  induction m with
  | nil => exact h0
  | cons x m ih => rw [List.reverse_cons]; exact hs _ _ ih

theorem proj_index (l : List Label) (r : Fin 3) {j : Nat} {e : Ev} (hj : (projR l r)[j]? = some e) :
    ∃ n, l[n]? = some (r, e) ∧ projR (l.take n) r = (projR l r).take j := by
  revert j e
  refine snoc_ind (P := fun l => ∀ {j : Nat} {e : Ev}, (projR l r)[j]? = some e →
    ∃ n, l[n]? = some (r, e) ∧ projR (l.take n) r = (projR l r).take j) ?_ ?_ l
  · intro j e hj; exact absurd hj (by rw [show projR ([] : List Label) r = [] from rfl]; simp)
  · intro l x ih j e hj
    obtain ⟨i, e'⟩ := x
    rw [proj_snoc] at hj ⊢
    by_cases hir : i = r
    · subst hir
      rw [if_pos rfl] at hj ⊢
      by_cases hjl : j < (projR l i).length
      · rw [List.getElem?_append_left hjl] at hj
        obtain ⟨n, h1, h2⟩ := ih hj
        have hn : n < l.length := (List.getElem?_eq_some_iff.1 h1).1
        refine ⟨n, by rw [List.getElem?_append_left hn]; exact h1, ?_⟩
        rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega), h2]
      · have hj' : j = (projR l i).length := by
          have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
        subst hj'
        rw [List.getElem?_append_right (by omega)] at hj
        simp at hj; subst hj
        refine ⟨l.length, by simp, ?_⟩
        rw [List.take_append_of_le_length (by omega), List.take_length]
        simp
    · rw [if_neg hir] at hj ⊢
      obtain ⟨n, h1, h2⟩ := ih hj
      have hn : n < l.length := (List.getElem?_eq_some_iff.1 h1).1
      refine ⟨n, by rw [List.getElem?_append_left hn]; exact h1, ?_⟩
      rw [List.take_append_of_le_length (by omega), h2]

end Perennial.gryff.pure
