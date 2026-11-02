/- Lean-first (no Rocq counterpart).

# Lemmas of the frontier helpers' proofs (2026-11-02)

For `chains.isComplete`, `chains.removeFromFrontier` and `chains.addToFrontier`: what every
client's struct says purely (`clientFacts`, `clients_facts`), the client of a head operation
(`clientOf_opAt`), and `Check`'s answer on unrelated head operations (`linOrder_unrelated`).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ChainsOwn
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Oracles

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

/-- Erasing the first occurrence of `x`, found at `k`. -/
theorem erase_eq_eraseIdx_of {l : List Nat} {x k : Nat} (hk : l[k]? = some x)
    (hpre : ∀ j, j < k → l[j]? ≠ some x) : l.erase x = l.eraseIdx k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons y l ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp
    | succ k =>
      have hy : y ≠ x := fun h => hpre 0 (by omega) (by simp [h])
      rw [List.erase_cons_tail (by simpa using hy), List.eraseIdx_cons_succ]
      congr 1
      exact ih (by simpa using hk) (fun j hj => by simpa using hpre (j + 1) (by omega))

theorem eraseIdx_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (k : Nat), (l.map f).eraseIdx k = (l.eraseIdx k).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => by simp [eraseIdx_map f l k]

section pure
variable {α : Type}

/-- The client of a chain's operation. -/
theorem clientOf_opAt {h : List (Op α)} {cs : List (List Nat)} (hok : ChainsOk h cs) {c k : Nat}
    (hc : c < cs.length) (hk : k < (chain cs c).length) : clientOf cs (opAt cs c k) = c := by
  have hmem : opAt cs c k ∈ chain cs c := by
    rw [opAt_eq hk]; exact List.getElem_mem hk
  have hcs : chain cs c = cs[c] := by
    unfold chain; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; rfl
  unfold clientOf
  rw [List.findIdx_eq hc]
  refine ⟨by simpa [← hcs] using hmem, fun j hj => ?_⟩
  have hj' : chain cs j = cs[j] := by
    unfold chain; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  simp only [decide_eq_false_iff_not]
  intro hm
  rw [← hj'] at hm
  have := hok.2.2 _ _ _ hm hmem
  omega

theorem keyGt_trans {h : List (Op α)} {cs : List (List Nat)} {x y z : Nat}
    (h1 : KeyGt h cs x y) (h2 : KeyGt h cs y z) : KeyGt h cs x z := by
  unfold KeyGt at *; omega

/-- Inserting `x` at `i` in a list sorted by a transitive relation, after the members it is
below and before the first it is above, keeps it sorted. -/
theorem pairwise_insert {R : Nat → Nat → Prop} (htr : ∀ a b c, R a b → R b c → R a c)
    {L : List Nat} {x i : Nat} (hL : L.Pairwise R) (hi : i ≤ L.length)
    (hbefore : ∀ j (hj : j < i), R (L[j]'(by omega)) x)
    (hafter : ∀ (hi' : i < L.length), R x L[i]) :
    (L.take i ++ x :: L.drop i).Pairwise R := by
  have hsplit := hL
  rw [← List.take_append_drop i L, List.pairwise_append] at hsplit
  obtain ⟨hT, hD, hTD⟩ := hsplit
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hT, ⟨fun y hy => ?_, hD⟩, fun a ha b hb => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_drop]
    have hi' : i < L.length := by simp at hj; omega
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simpa using hafter hi'
    · refine htr _ _ _ (hafter hi') ?_
      have := List.pairwise_iff_getElem.mp hL i (i + j) hi' (by simp at hj; omega) (by omega)
      exact this
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [List.length_take] at hj
      rw [List.getElem_take]
      exact hbefore j (by omega)
    · exact hTD _ (List.getElem_mem _) _ hb

theorem mem_insert_iff {L : List Nat} {x i y : Nat} :
    y ∈ L.take i ++ x :: L.drop i ↔ y = x ∨ y ∈ L := by
  constructor
  · intro hy
    rcases List.mem_append.mp hy with h1 | h1
    · exact Or.inr (List.mem_of_mem_take h1)
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (List.mem_of_mem_drop h2)
  · rintro (rfl | hy)
    · simp
    · rw [← List.take_append_drop i L] at hy
      rcases List.mem_append.mp hy with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)

/-- `s = append(s, 0); copy(s[i+1:], s[i:]); s[i] = x` inserts `x` at `i`. -/
theorem insert_by_copy {A : Type} (L : List A) (z x : A) (i : Nat) (hi : i < L.length) :
    ((L ++ [z]).take (i + 1) ++
      ((subslice i (L.length + 1) (L ++ [z])).take (L.length + 1 - (i + 1)) ++
        (subslice (i + 1) (L.length + 1) (L ++ [z])).drop (L.length + 1 - i)) ++
      (L ++ [z]).drop (L.length + 1)).set i x = L.take i ++ x :: L.drop i := by
  have h1 : (L ++ [z]).take (i + 1) = L.take (i + 1) := List.take_append_of_le_length (by omega)
  have h2 : (subslice i (L.length + 1) (L ++ [z])).take (L.length + 1 - (i + 1)) = L.drop i := by
    have e : subslice i (L.length + 1) (L ++ [z]) = L.drop i ++ [z] := by
      simp only [subslice]
      rw [List.take_of_length_le (by simp)]
      simp [List.drop_append, show i - L.length = 0 by omega]
    rw [e, List.take_append_of_le_length (by simp)]
    exact List.take_of_length_le (by simp)
  have h3 : (subslice (i + 1) (L.length + 1) (L ++ [z])).drop (L.length + 1 - i) = [] := by
    simp only [subslice]
    apply List.drop_of_length_le
    simp; omega
  have h4 : (L ++ [z]).drop (L.length + 1) = [] := by
    apply List.drop_of_length_le; simp
  rw [h1, h2, h3, h4, List.append_nil, List.append_nil, List.take_succ_eq_append_getElem hi,
    List.append_assoc, List.set_append_right _ _ (by simp; omega)]
  simp [Nat.min_eq_left (Nat.le_of_lt hi)]

/-- The frontier with `cc` inserted at `k`, before its member `x` it is `KeyGt` than, after the
members `KeyGt` than it, is sorted. -/
theorem frontier_insert_sorted {h : List (Op α)} {cs : List (List Nat)} {f : Nat → Nat}
    {fr : List Nat} {cc k x : Nat} (hsorted : (fr.map f).Pairwise (KeyGt h cs))
    (hk : fr[k]? = some x)
    (hbefore : ∀ j y, j < k → fr[j]? = some y → KeyGt h cs (f y) (f cc))
    (hafter : KeyGt h cs (f cc) (f x)) :
    ((fr.take k ++ cc :: fr.drop k).map f).Pairwise (KeyGt h cs) := by
  have hkl : k < fr.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [List.map_append, List.map_cons, List.map_take, List.map_drop]
  refine pairwise_insert (R := KeyGt h cs) (L := fr.map f) (x := f cc) (i := k)
    (fun _ _ _ h1 h2 => keyGt_trans h1 h2) hsorted
    (by rw [List.length_map]; omega) (fun j hj => ?_)
    (fun hi' => ?_)
  · rw [List.getElem_map]
    exact hbefore j _ hj (List.getElem?_eq_getElem _)
  · rw [List.getElem_map, (List.getElem?_eq_some_iff.mp hk).2]
    exact hafter

/-- The frontier with `cc` appended, when every member is `KeyGt` than it, is sorted. -/
theorem frontier_append_sorted {h : List (Op α)} {cs : List (List Nat)} {f : Nat → Nat}
    {fr : List Nat} {cc : Nat} (hsorted : (fr.map f).Pairwise (KeyGt h cs))
    (hbefore : ∀ j y, j < fr.length → fr[j]? = some y → KeyGt h cs (f y) (f cc)) :
    ((fr ++ [cc]).map f).Pairwise (KeyGt h cs) := by
  rw [List.map_append, List.pairwise_append]
  refine ⟨hsorted, by simp, fun a ha b hb => ?_⟩
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  exact hbefore j _ hj (List.getElem?_eq_getElem _)

end pure

/-- On operations unrelated in real time, `Check`'s answer is `GeneralLikely`'s. -/
theorem linOrder_unrelated [GooseExts] {a b : Operation} (h1 : ¬ sint.Z a.Return' < sint.Z b.Call')
    (h2 : ¬ sint.Z b.Return' < sint.Z a.Call') : linOrder a b = glOrder a b := by
  unfold linOrder glOrder
  simp only [h1, h2, ↓reduceIte]

theorem glOrder_eq_one [GooseExts] {a b : Operation} :
    glOrder a b = W64 1 ↔ sint.Z b.Call' < sint.Z a.Call' := by
  unfold glOrder
  split
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h; omega
  · split
    · exact ⟨fun _ => by assumption, fun _ => rfl⟩
    · constructor
      · intro h; exact absurd h (by decide)
      · intro h; omega

theorem glOrder_eq_zero [GooseExts] {a b : Operation} :
    glOrder a b = W64 0 ↔ sint.Z a.Call' = sint.Z b.Call' := by
  unfold glOrder
  split
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h; omega
  · split
    · constructor
      · intro h; exact absurd h (by decide)
      · intro h; omega
    · exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem glOrder_ne_three [GooseExts] {a b : Operation} : glOrder a b ≠ W64 3 := by
  rcases glOrder_cases a b with h | h | h <;> rw [h] <;> decide

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- A client's struct does not depend on the frontier. -/
theorem clientOwn_frontier (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (fr : List Nat)
    (c : Nat) (cv : client) :
    clientOwn (GF := GF) h cs { st with frontier := fr } c cv = clientOwn h cs st c cv := rfl

/-- A slice's element, read and put back unchanged. -/
theorem ownSlice_elem_acc' {V : Type} [TypedPointsto (GF := GF) V] [ZeroVal V] (i : Int) (v : V)
    (s : GoSlice) (dq : DFrac) (vs : List V) (hpos : 0 ≤ i) (hlookup : vs[i.toNat]? = some v) :
    (s ↦*{dq} vs : IProp GF) ⊢
      typedPointsto (sliceIndexRef V i s) v dq ∗
      (typedPointsto (sliceIndexRef V i s) v dq -∗ s ↦*{dq} vs) := by
  iintro Hs
  icases ownSlice_elem_acc i v s dq vs hpos hlookup $$ Hs with ⟨Hv, Hs⟩
  iframe Hv
  iintro Hv
  ihave Hs := Hs $$ %v Hv
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hlookup
  rw [← heq, List.set_getElem_self]
  iexact Hs

/-- What client `c`'s struct says purely: its id, its head, its operations slice's length. -/
def clientFacts (cs : List (List Nat)) (st : ChSt) (c : Nat) (cv : client) : Prop :=
  sint.Z cv.id' = c ∧ sint.Z cv.head' = st.head c ∧
  sint.nat cv.cltOps'.len = (chain cs c).length ∧ 0 ≤ sint.Z cv.cltOps'.len

theorem clientOwn_facts (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : Nat)
    (cv : client) :
    clientOwn h cs st c cv ⊢ clientOwn (GF := GF) h cs st c cv ∗ ⌜clientFacts cs st c cv⌝ := by
  unfold clientOwn
  iintro ⟨%Hc, %cos, Hcl, %Hok, Hfu⟩
  ihave %Hlen := ownSlice_len $$ Hcl
  isplitl
  · isplitr
    · ipureintro; exact Hc
    iexists cos
    iframe
    ipureintro; exact Hok
  · ipureintro
    exact ⟨Hc.1, Hc.2.1, by rw [← Hlen.1, Hok.1], Hlen.2⟩

/-- Every client's `clientFacts`. -/
theorem clients_facts (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (cvs : List client) :
    ([∗list] c ↦ cv ∈ cvs, clientOwn h cs st c cv) ⊢
      ([∗list] c ↦ cv ∈ cvs, clientOwn (GF := GF) h cs st c cv) ∗
      ⌜∀ j cv, cvs[j]? = some cv → clientFacts cs st j cv⌝ := by
  iintro Hl
  ihave Hl := BigSepL.bigSepL_mono (fun {k x} _ => clientOwn_facts (GF := GF) h cs st k x) $$ Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hl, Hp⟩
  ihave %Hp := BigSepL.bigSepL_pure_intro $$ Hp
  iframe Hl
  ipureintro; exact Hp

end heap

end github_com.anishathalye.porcupine

end Perennial
