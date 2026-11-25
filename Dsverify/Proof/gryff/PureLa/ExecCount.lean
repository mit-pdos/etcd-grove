/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/ExecCount.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: the executions with a result so far (`execSeq`'s lengths): one more at an execution
step with a result, and at most `3 · 2^21` per replica (an execution's instance is in the box,
and a replica executes an instance at most once: unit A's `exec_nodup`).
-/
module

public import Dsverify.Proof.gryff.Pure.Agree
public import Dsverify.Proof.gryff.PureL.Peel
public import Dsverify.Proof.gryff.PureL.Run

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model kahn Perennial.gryff.pure

/-- An execution step's count: one if it is an execution with a result. -/
def dEx (e : Ev) (o : List Out) : Nat :=
  match e with
  | .exec _ _ => if (execRes o).isSome then 1 else 0
  | _ => 0

theorem filterMap_congr'' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      filterMap_congr'' (fun b hb => h b (by simp [hb]))]

theorem outsOf_snoc_lt (r : Fin 3) (es : List Ev) (e : Ev) {j : Nat} (hj : j < es.length) :
    outsOf r (es ++ [e]) j = outsOf r es j := by
  unfold outsOf resOf
  rw [List.getElem?_append_left hj, List.take_append_of_le_length (Nat.le_of_lt hj)]

theorem execSeq_snoc (r : Fin 3) (es : List Ev) (e : Ev) :
    (execSeq r (es ++ [e])).length = (execSeq r es).length +
      dEx e (match stepR r (stOf r es) e with
        | .ok (_, o) => o
        | .error _ => []) := by
  unfold execSeq
  rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
  rw [filterMap_congr'' (g := fun j => match es[j]? with
      | some (Ev.exec q i) => (execRes (outsOf r es j)).map fun vt => ((q, i), vt)
      | _ => none)]
  · rw [List.length_append]
    congr 1
    simp only [List.filterMap_cons, List.filterMap_nil]
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    simp only [List.getElem?_cons_zero]
    have ho : outsOf r (es ++ [e]) es.length = (match stepR r (stOf r es) e with
        | .ok (_, o) => o
        | .error _ => []) := by
      unfold outsOf resOf
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.take_left' rfl]
      rfl
    rw [ho]
    generalize (match stepR r (stOf r es) e with
        | .ok (_, o) => o
        | .error _ => []) = o
    cases e <;> simp only [dEx] <;> try rfl
    cases execRes o <;> simp
  · intro j hj
    have hj' := List.mem_range.1 hj
    rw [List.getElem?_append_left hj', outsOf_snoc_lt r es e hj']
    rfl

theorem stepExec_inBox {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : inBox q i = true := by
  unfold stepExec at h
  peel h
  all_goals (simp only [Bool.not_eq_true', Bool.not_eq_false] at *; assumption)

theorem execSeq_inBox (r : Fin 3) (es : List Ev) {x : (w32 × w32) × ValTag}
    (hx : x ∈ execSeq r es) : inBox x.1.1 x.1.2 = true := by
  unfold execSeq at hx
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hx
  split at hj
  · rename_i q i heq
    obtain ⟨vt, hvt, rfl⟩ := Option.map_eq_some_iff.1 hj
    unfold outsOf at hvt
    cases hres : resOf r es j with
    | error => rw [hres] at hvt; simp [execRes] at hvt
    | ok p =>
      unfold resOf at hres
      rw [heq] at hres
      exact stepExec_inBox (s' := p.1) (o := p.2) hres
  · cases hj

theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => by simp
  | a :: l, hf, hn => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_on (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])) hn.2⟩
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.1 hm
    have := hf b (by simp [hb]) a (by simp) he
    subst this; exact hn.1 hb

/-- The index of an instance of the box. -/
def boxIdx (x : w32 × w32) : Nat := x.1.toNat * 2 ^ 21 + x.2.toNat

theorem inBox_toNat {q i : w32} (h : inBox q i = true) : q.toNat < 3 ∧ i.toNat < 2 ^ 21 := by
  unfold inBox at h
  obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true h
  simp only [SLOTS] at h4
  have e1 : (q.toNat : Int) = sint.Z q := by
    unfold sint.Z; rw [BitVec.toInt_eq_toNat_of_msb]
    exact BitVec.msb_eq_false_iff_two_mul_lt.2 (BitVec.toInt_pos_iff.1 (by unfold sint.Z at h1; exact h1))
  have e2 : (i.toNat : Int) = sint.Z i := by
    unfold sint.Z; rw [BitVec.toInt_eq_toNat_of_msb]
    exact BitVec.msb_eq_false_iff_two_mul_lt.2 (BitVec.toInt_pos_iff.1 (by unfold sint.Z at h3; exact h3))
  omega

theorem execSeq_len (r : Fin 3) (es : List Ev) (hn : ((execSeq r es).map Prod.fst).Nodup) :
    (execSeq r es).length ≤ 3 * 2 ^ 21 := by
  have hb : ∀ x ∈ (execSeq r es).map Prod.fst, inBox x.1 x.2 = true := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact execSeq_inBox r es hy
  have hn2 : (((execSeq r es).map Prod.fst).map boxIdx).Nodup := by
    refine nodup_map_on ?_ hn
    intro x hx y hy hxy
    obtain ⟨a1, a2⟩ := inBox_toNat (hb x hx)
    obtain ⟨b1, b2⟩ := inBox_toNat (hb y hy)
    unfold boxIdx at hxy
    have e1 : x.1.toNat = y.1.toNat := by omega
    have e2 : x.2.toNat = y.2.toNat := by omega
    exact Prod.ext (BitVec.eq_of_toNat_eq e1) (BitVec.eq_of_toNat_eq e2)
  have hsub : ((execSeq r es).map Prod.fst).map boxIdx ⊆ List.range (3 * 2 ^ 21) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    obtain ⟨a1, a2⟩ := inBox_toNat (hb x hx)
    rw [List.mem_range]; unfold boxIdx; omega
  have := hn2.length_le_of_subset hsub
  simpa using this

end Perennial.gryff.pure.La
