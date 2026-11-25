/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/AEList.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AE, internal: list facts for the execution chain.
* `sorted_closed_prefix`: two lists sorted by a strict order that is total on a set `D` holding
  their members, each downward closed in `D`, are prefix-comparable.
* `chainR`: a list of results computed one by one from the previous one (the executor's
  `PrevValTag` rule); prefix-comparable inputs give prefix-comparable chains.
* `execSeqA`: a copy of `Pure/Agree.lean`'s `execSeq` (which `PureA` cannot import), and how it grows
  along a replica's events.
-/
module

public import Dsverify.Proof.gryff.PureA.AEStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AE

open Perennial Perennial.gryff.model Perennial.gryff.pure

theorem sorted_closed_prefix {α : Type} {lt : α → α → Prop} (hirr : ∀ x, ¬ lt x x)
    (htr : ∀ x y z, lt x y → lt y z → lt x z) :
    ∀ (D : α → Prop) (l1 l2 : List α), (∀ x y, D x → D y → x ≠ y → lt x y ∨ lt y x) →
    l1.Pairwise lt → l2.Pairwise lt → (∀ x ∈ l1, D x) → (∀ x ∈ l2, D x) →
    (∀ y ∈ l1, ∀ x, D x → lt x y → x ∈ l1) → (∀ y ∈ l2, ∀ x, D x → lt x y → x ∈ l2) →
    l1 <+: l2 ∨ l2 <+: l1
  | _, [], _, _, _, _, _, _, _, _ => Or.inl List.nil_prefix
  | _, _ :: _, [], _, _, _, _, _, _, _ => Or.inr List.nil_prefix
  | D, a :: t1, b :: t2, htot, p1, p2, d1, d2, c1, c2 => by
    rw [List.pairwise_cons] at p1 p2
    have hab : a = b := by
      apply Classical.byContradiction
      intro hne
      rcases htot a b (d1 a (by simp)) (d2 b (by simp)) hne with h | h
      · have ha := c2 b (by simp) a (d1 a (by simp)) h
        rcases List.mem_cons.1 ha with e | ha'
        · exact hne e
        · exact hirr _ (htr _ _ _ h (p2.1 a ha'))
      · have hb := c1 a (by simp) b (d2 b (by simp)) h
        rcases List.mem_cons.1 hb with e | hb'
        · exact hne e.symm
        · exact hirr _ (htr _ _ _ h (p1.1 b hb'))
    subst hab
    have ne1 : ∀ x ∈ t1, x ≠ a := fun x hx e => by subst e; exact hirr _ (p1.1 _ hx)
    have ne2 : ∀ x ∈ t2, x ≠ a := fun x hx e => by subst e; exact hirr _ (p2.1 _ hx)
    have ih := sorted_closed_prefix hirr htr (fun x => D x ∧ x ≠ a) t1 t2
      (fun x y hx hy hne => htot x y hx.1 hy.1 hne) p1.2 p2.2
      (fun x hx => ⟨d1 x (List.mem_cons_of_mem _ hx), ne1 x hx⟩)
      (fun x hx => ⟨d2 x (List.mem_cons_of_mem _ hx), ne2 x hx⟩)
      (fun y hy x hx hlt => (List.mem_cons.1 (c1 y (List.mem_cons_of_mem _ hy) x hx.1 hlt)).resolve_left hx.2)
      (fun y hy x hx hlt => (List.mem_cons.1 (c2 y (List.mem_cons_of_mem _ hy) x hx.1 hlt)).resolve_left hx.2)
    rcases ih with h | h
    · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    · exact Or.inr (List.cons_prefix_cons.2 ⟨rfl, h⟩)

/-! ## Result chains -/

/-- Results computed one by one: `F prev x` from the previous result. -/
def chainR {α β : Type} (F : Option β → α → β) : Option β → List α → List (α × β)
  | _, [] => []
  | p, x :: xs => (x, F p x) :: chainR F (some (F p x)) xs

theorem chainR_map_fst {α β : Type} (F : Option β → α → β) :
    ∀ (p : Option β) (xs : List α), (chainR F p xs).map Prod.fst = xs
  | _, [] => rfl
  | p, x :: xs => by simp [chainR, chainR_map_fst F _ xs]

theorem chainR_snoc {α β : Type} (F : Option β → α → β) :
    ∀ (p : Option β) (xs : List α) (x : α),
      chainR F p (xs ++ [x]) = chainR F p xs ++ [(x, F (((chainR F p xs).getLast?.map Prod.snd).or p) x)]
  | p, [], x => by simp [chainR]
  | p, y :: ys, x => by
    simp only [List.cons_append, chainR, List.cons_append]
    rw [chainR_snoc F _ ys x]
    congr 3
    cases ys with
    | nil => simp [chainR]
    | cons z zs =>
      simp only [chainR, List.getLast?_cons_cons]
      cases h : (chainR F (some (F (some (F p y)) z)) zs).getLast? <;>
        simp [List.getLast?_cons, h]

theorem chainR_prefix {α β : Type} (F : Option β → α → β) :
    ∀ (p : Option β) (xs ys : List α), xs <+: ys → chainR F p xs <+: chainR F p ys
  | _, [], _, _ => List.nil_prefix
  | _, _ :: _, [], h => absurd h (by simp)
  | p, x :: xs, y :: ys, h => by
    rw [List.cons_prefix_cons] at h
    obtain ⟨rfl, h⟩ := h
    simp only [chainR, List.cons_prefix_cons, true_and]
    exact chainR_prefix F _ xs ys h

theorem nodup_fst_eq {α β : Type} : ∀ {L : List (α × β)} {x : α} {a b : β},
    (L.map Prod.fst).Nodup → (x, a) ∈ L → (x, b) ∈ L → a = b
  | [], _, _, _, _, ha, _ => by cases ha
  | p :: L, x, a, b, hn, ha, hb => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 ha with e | ha' <;> rcases List.mem_cons.1 hb with e' | hb'
    · rw [← e] at e'; cases e'; rfl
    · subst e; exact absurd (List.mem_map.2 ⟨_, hb', rfl⟩) hn.1
    · subst e'; exact absurd (List.mem_map.2 ⟨_, ha', rfl⟩) hn.1
    · exact nodup_fst_eq hn.2 ha' hb'

/-! ## A replica's executed sequence -/

/-- Event `j`'s entry (`Pure/Agree.lean`'s `execSeq`'s body). -/
noncomputable def entryA (r : Fin 3) (es : List Ev) (j : Nat) : Option ((w32 × w32) × ValTag) :=
  match es[j]? with
  | some (Ev.exec q i) => (execRes (outsOf r es j)).map fun vt => ((q, i), vt)
  | _ => none

/-- `Pure/Agree.lean`'s `execSeq` (the same body). -/
noncomputable def execSeqA (r : Fin 3) (es : List Ev) : List ((w32 × w32) × ValTag) :=
  (List.range es.length).filterMap (entryA r es)

theorem entryA_take (r : Fin 3) (es : List Ev) {j k : Nat} (hjk : j < k) :
    entryA r (es.take k) j = entryA r es j := by
  have e1 : (es.take k)[j]? = es[j]? := by rw [List.getElem?_take]; simp [hjk]
  have e2 : (es.take k).take j = es.take j := by rw [List.take_take]; congr 1; omega
  unfold entryA outsOf resOf
  rw [e1, e2]

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons]
    rw [h a (by simp), filterMap_congr' l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem execSeqA_succ (r : Fin 3) (es : List Ev) {j : Nat} (hj : j < es.length) :
    execSeqA r (es.take (j + 1)) = execSeqA r (es.take j) ++ (entryA r es j).toList := by
  unfold execSeqA
  have l1 : (es.take (j + 1)).length = j + 1 := by simp; omega
  have l0 : (es.take j).length = j := by simp; omega
  rw [l1, l0, List.range_succ, List.filterMap_append]
  congr 1
  · apply filterMap_congr'
    intro x hx
    rw [List.mem_range] at hx
    rw [entryA_take r es (by omega : x < j + 1), entryA_take r es hx]
  · simp only [List.filterMap_cons, List.filterMap_nil]
    rw [entryA_take r es (by omega : j < j + 1)]
    cases entryA r es j <;> rfl

theorem execSeqA_full (r : Fin 3) (es : List Ev) : execSeqA r (es.take es.length) = execSeqA r es := by
  rw [List.take_length]

theorem execSeqA_mono (r : Fin 3) (es : List Ev) {j : Nat} :
    ∀ k, j ≤ k → k ≤ es.length → execSeqA r (es.take j) <+: execSeqA r (es.take k)
  | 0, hjk, _ => by rw [show j = 0 by omega]; exact List.prefix_refl _
  | k + 1, hjk, hk => by
    by_cases e : j = k + 1
    · subst e; exact List.prefix_refl _
    · rw [execSeqA_succ r es (by omega)]
      exact (execSeqA_mono r es k (by omega) (by omega)).trans (List.prefix_append _ _)

theorem execSeqA_prefix (r : Fin 3) (es : List Ev) {j : Nat} (hj : j ≤ es.length) :
    execSeqA r (es.take j) <+: execSeqA r es := by
  rw [← execSeqA_full r es]; exact execSeqA_mono r es _ hj (Nat.le_refl _)

end Perennial.gryff.pureA.AE
