/-
Lean-first (no Rocq counterpart).

# The chains, in pure terms (2026-11-02)

PR #46's search keeps a partition's operations as one *chain* per client (`cs[c]`: client `c`'s
operation ids, in the order listed), linearized from the front: client `c`'s first `H[c]`
operations are linearized (`headsSet`), and its *head* is `opAt cs c H[c]`. For the head of `c`
and another client `d`, `FU h cs c k d` is the number of `d`'s operations preceding `c`'s `k`-th
in real time (`firstUnk[d]` once computed), and `deps h cs H c` the number of clients `d` with
preceding operations not all linearized (`nDeps`).

`ChainsOk h cs` is the PR's premise on a partition, in these terms (`ClientsOk` for a slice of
`Operation`s): the chains hold every operation once, and each is sequential (an operation
precedes the next in real time). Under it the preceding operations of a chain are a prefix
(`fu_prefix`), `FU` grows along a chain (`fu_mono`), and the candidates (`DagTheory.Cand`) are
exactly the heads with no dependency (`cand_iff`).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.DagTheory

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

variable {α : Type}

/-- Client `c`'s chain (`[]` past the clients). -/
def chain (cs : List (List Nat)) (c : Nat) : List Nat := cs.getD c []

/-- Client `c`'s `k`-th operation (`0` past its chain). -/
def opAt (cs : List (List Nat)) (c k : Nat) : Nat := (chain cs c).getD k 0

/-- The chains hold every operation of `h` exactly once, and each chain is sequential. -/
def ChainsOk (h : List (Op α)) (cs : List (List Nat)) : Prop :=
  (∀ c, (chain cs c).Nodup ∧ (chain cs c).Pairwise (Prec h)) ∧
  (∀ y, y < h.length ↔ ∃ c, c < cs.length ∧ y ∈ chain cs c) ∧
  (∀ y c c', y ∈ chain cs c → y ∈ chain cs c' → c = c')

/-- `Prec`, decided. -/
def precB (h : List (Op α)) (a b : Nat) : Bool :=
  match h[a]?, h[b]? with
  | some oa, some ob => decide (oa.ret < ob.call)
  | _, _ => false

theorem precB_iff {h : List (Op α)} {a b : Nat} : precB h a b = true ↔ Prec h a b := by
  unfold precB Prec
  cases ha : h[a]? <;> cases hb : h[b]? <;> simp

/-- The number of client `d`'s operations preceding client `c`'s `k`-th. -/
def FU (h : List (Op α)) (cs : List (List Nat)) (c k d : Nat) : Nat :=
  ((chain cs d).filter (fun z => precB h z (opAt cs c k))).length

/-- The number of other clients whose operations preceding `c`'s head are not all linearized. -/
def deps (h : List (Op α)) (cs : List (List Nat)) (H : List Nat) (c : Nat) : Nat :=
  ((List.range cs.length).filter
    (fun d => decide (d ≠ c ∧ H.getD c 0 < (chain cs c).length ∧
      H.getD d 0 < FU h cs c (H.getD c 0) d))).length

/-- The operations linearized: each client's first `H[c]`. -/
def headsSet (cs : List (List Nat)) (H : List Nat) (y : Nat) : Prop :=
  ∃ c k, k < H.getD c 0 ∧ (chain cs c)[k]? = some y

/-- The heads are within the chains. -/
def HeadsOk (cs : List (List Nat)) (H : List Nat) : Prop :=
  H.length = cs.length ∧ ∀ c, H.getD c 0 ≤ (chain cs c).length

section lemmas
variable {h : List (Op α)} {cs : List (List Nat)}

theorem chain_of_ge {c : Nat} (hc : cs.length ≤ c) : chain cs c = [] := by
  unfold chain; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc]

theorem opAt_eq {c k : Nat} (hk : k < (chain cs c).length) : opAt cs c k = (chain cs c)[k] := by
  unfold opAt; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- A downward-closed predicate on a list keeps a prefix. -/
theorem filter_prefix {R : Nat → Nat → Prop} {P : Nat → Bool} :
    ∀ {l : List Nat}, l.Pairwise R → (∀ a b, R a b → P b = true → P a = true) →
      ∀ i (hi : i < l.length), (i < (l.filter P).length ↔ P l[i] = true)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | a :: t, hpw, hdc, i, hi => by
    rw [List.pairwise_cons] at hpw
    by_cases hPa : P a = true
    · rw [List.filter_cons_of_pos hPa]
      cases i with
      | zero => simp [hPa]
      | succ i =>
        simp only [List.length_cons, List.getElem_cons_succ]
        exact Nat.succ_lt_succ_iff.trans (filter_prefix hpw.2 hdc i (by simpa using hi))
    · rw [List.filter_cons_of_neg hPa]
      have hnone : t.filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hPb
        exact hPa (hdc a b (hpw.1 b hb) hPb)
      rw [hnone]
      cases i with
      | zero => simpa using hPa
      | succ i =>
        have hit : i < t.length := by simpa using hi
        simp only [List.length_nil, List.getElem_cons_succ]
        have hm : t[i] ∈ t := List.getElem_mem hit
        constructor
        · intro h; omega
        · intro hP; exact absurd hP (List.filter_eq_nil_iff.mp hnone t[i] hm)

/-- Under `ChainsOk`, `Prec` is transitive through an operation (its call is at most its return). -/
theorem prec_trans (hwf : CallLeRet h) {a b c : Nat} (h1 : Prec h a b) (h2 : Prec h b c) :
    Prec h a c := by
  obtain ⟨oa, ob, ha, hb, h1⟩ := h1
  obtain ⟨ob', oc, hb', hc, h2⟩ := h2
  rw [hb] at hb'; cases hb'
  have := hwf ob (List.mem_of_getElem? hb)
  exact ⟨oa, oc, ha, hc, by omega⟩

/-- The operations of a chain preceding an operation are a prefix of it. -/
theorem fu_prefix (hok : ChainsOk h cs) (hwf : CallLeRet h) {c k d i : Nat}
    (hi : i < (chain cs d).length) :
    i < FU h cs c k d ↔ Prec h (chain cs d)[i] (opAt cs c k) := by
  unfold FU
  rw [filter_prefix (hok.1 d).2 (fun a b hab hb => by
    rw [precB_iff] at hb ⊢; exact prec_trans hwf hab hb) i hi, precB_iff]

theorem fu_le {c k d : Nat} : FU h cs c k d ≤ (chain cs d).length := List.length_filter_le _ _

theorem filter_length_mono {p q : Nat → Bool} (hpq : ∀ z, p z = true → q z = true) :
    ∀ {l : List Nat}, (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | a :: t => by
    have ih := filter_length_mono hpq (l := t)
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (hpq a hp)]
      simp only [List.length_cons]; omega
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq]; simp only [List.length_cons]; omega
      · rw [List.filter_cons_of_neg hq]; exact ih

/-- `FU` grows along a chain: what preceded an operation precedes the next. -/
theorem fu_mono (hok : ChainsOk h cs) (hwf : CallLeRet h) {c k d : Nat}
    (hk : k + 1 < (chain cs c).length) : FU h cs c k d ≤ FU h cs c (k + 1) d := by
  unfold FU
  have hp : Prec h (opAt cs c k) (opAt cs c (k + 1)) := by
    rw [opAt_eq (by omega), opAt_eq hk]
    exact List.pairwise_iff_getElem.mp (hok.1 c).2 k (k + 1) (by omega) hk (by omega)
  exact filter_length_mono (fun z hz => by
    rw [precB_iff] at hz ⊢; exact prec_trans hwf hz hp)

/-- An operation's position is unique. -/
theorem pos_unique (hok : ChainsOk h cs) {c c' k k' y : Nat}
    (h1 : (chain cs c)[k]? = some y) (h2 : (chain cs c')[k']? = some y) : c = c' ∧ k = k' := by
  have hc : c = c' := hok.2.2 y c c' (List.mem_of_getElem? h1) (List.mem_of_getElem? h2)
  subst hc
  refine ⟨rfl, ?_⟩
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hk', he⟩ := List.getElem?_eq_some_iff.mp h2
  have hnd := List.pairwise_iff_getElem.mp (hok.1 c).1
  refine Classical.byContradiction fun hne => ?_
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hnd k k' hk hk' hlt he.symm
  · exact hnd k' k hk' hk hlt he

theorem lt_length_of_mem (hok : ChainsOk h cs) {c y : Nat} (hy : y ∈ chain cs c) :
    y < h.length := by
  refine (hok.2.1 y).mpr ⟨c, ?_, hy⟩
  refine Classical.byContradiction fun hc => ?_
  rw [chain_of_ge (by omega)] at hy; cases hy

theorem deps_eq_zero {H : List Nat} {c : Nat} (hc : H.getD c 0 < (chain cs c).length) :
    deps h cs H c = 0 ↔ ∀ d, d < cs.length → d ≠ c → FU h cs c (H.getD c 0) d ≤ H.getD d 0 := by
  unfold deps
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro hz d hd hdc
    have := hz d (List.mem_range.mpr hd)
    simp only [decide_eq_true_eq, not_and, Nat.not_lt] at this
    exact this hdc hc
  · intro hz d hd
    simp only [decide_eq_true_eq, not_and, Nat.not_lt]
    exact fun hdc _ => hz d (List.mem_range.mp hd) hdc

/-- The candidates are the heads with no dependency. -/
theorem cand_iff (hok : ChainsOk h cs) (hwf : CallLeRet h) {H B : List Nat} {y : Nat}
    (_hH : HeadsOk cs H) (hB : ∀ y, y ∈ B ↔ headsSet cs H y) :
    Cand h B y ↔ ∃ c, c < cs.length ∧ H.getD c 0 < (chain cs c).length ∧
      opAt cs c (H.getD c 0) = y ∧ deps h cs H c = 0 := by
  constructor
  · rintro ⟨hy, hyB, hpre⟩
    obtain ⟨c, hc, hyc⟩ := (hok.2.1 y).mp hy
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hyc
    have hk' : (chain cs c)[k]? = some y := by rw [List.getElem?_eq_getElem hk, hke]
    have hkH : H.getD c 0 ≤ k := by
      refine Nat.le_of_not_lt fun hlt => hyB ((hB y).mpr ⟨c, k, hlt, hk'⟩)
    have hHk : H.getD c 0 = k := by
      refine Nat.le_antisymm hkH (Nat.le_of_not_lt fun hlt => ?_)
      -- the head precedes `y`, so it is linearized: impossible
      have hp : Prec h (chain cs c)[H.getD c 0] y := by
        rw [← hke]
        exact List.pairwise_iff_getElem.mp (hok.1 c).2 _ k (by omega) hk hlt
      obtain ⟨c', k', hk'', he⟩ := (hB _).mp (hpre _ hp)
      obtain ⟨_, rfl⟩ := pos_unique hok he (List.getElem?_eq_getElem (by omega))
      rw [‹c' = c›] at hk''
      omega
    have hcl : H.getD c 0 < (chain cs c).length := by omega
    refine ⟨c, hc, hcl, ?_, ?_⟩
    · rw [opAt_eq hcl]; simp only [hHk, hke]
    rw [deps_eq_zero hcl]
    intro d hd hdc
    refine Nat.le_of_not_lt fun hlt => ?_
    have hdl : H.getD d 0 < (chain cs d).length := Nat.lt_of_lt_of_le hlt fu_le
    have hp := (fu_prefix hok hwf hdl).mp hlt
    rw [opAt_eq hcl] at hp
    simp only [hHk, hke] at hp
    obtain ⟨c', k', hk'', he⟩ := (hB _).mp (hpre _ hp)
    obtain ⟨rfl, rfl⟩ := pos_unique hok he (List.getElem?_eq_getElem hdl)
    omega
  · rintro ⟨c, hc, hcl, rfl, hdeps⟩
    rw [deps_eq_zero hcl] at hdeps
    have hyc : (chain cs c)[H.getD c 0]? = some (opAt cs c (H.getD c 0)) := by
      rw [opAt_eq hcl]; exact List.getElem?_eq_getElem hcl
    refine ⟨lt_length_of_mem hok (List.mem_of_getElem? hyc), fun hyB => ?_, fun z hz => ?_⟩
    · obtain ⟨c', k', hk', he⟩ := (hB _).mp hyB
      obtain ⟨rfl, rfl⟩ := pos_unique hok he hyc
      omega
    · have hzl : z < h.length := by
        obtain ⟨oz, _, hoz, _⟩ := hz; exact (List.getElem?_eq_some_iff.mp hoz).1
      obtain ⟨d, hd, hzd⟩ := (hok.2.1 z).mp hzl
      obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hzd
      have hi' : (chain cs d)[i]? = some z := by rw [List.getElem?_eq_getElem hi, hie]
      refine (hB z).mpr ⟨d, i, ?_, hi'⟩
      by_cases hdc : d = c
      · subst hdc
        refine Nat.lt_of_not_le fun hge => ?_
        rcases Nat.lt_or_eq_of_le hge with hgt | heq
        · -- the head precedes `z`, which precedes the head
          have hp : Prec h (chain cs d)[H.getD d 0] z := by
            rw [← hie]; exact List.pairwise_iff_getElem.mp (hok.1 d).2 _ i hcl hi hgt
          rw [opAt_eq hcl] at hz
          exact prec_irrefl hwf _ (prec_trans hwf hp hz)
        · subst heq
          rw [opAt_eq hcl, hie] at hz
          exact prec_irrefl hwf _ hz
      · have := (fu_prefix hok hwf hi).mpr (by rw [hie]; exact hz)
        exact Nat.lt_of_lt_of_le this (hdeps d hd hdc)

theorem count_split {p q : Nat → Bool} {i : Nat} :
    ∀ {l : List Nat}, l.Nodup → (∀ d ∈ l, d ≠ i → p d = q d) → (q i = true → p i = true) →
      (l.filter p).length = (l.filter q).length +
        (if i ∈ l ∧ p i = true ∧ q i = false then 1 else 0)
  | [], _, _, _ => by simp
  | a :: t, hnd, hag, hqp => by
    rw [List.nodup_cons] at hnd
    have ih := count_split hnd.2 (fun d hd => hag d (List.mem_cons_of_mem _ hd)) hqp
    by_cases hai : a = i
    · subst hai
      have hnt : a ∉ t := hnd.1
      have hif : (if a ∈ t ∧ p a = true ∧ q a = false then 1 else 0) = 0 := by simp [hnt]
      rw [hif] at ih
      cases hpa : p a <;> cases hqa : q a
      · simp [hpa, hqa, ih]
      · simp [hqa, hpa] at hqp
      · simp [hpa, hqa, ih]
      · simp [hpa, hqa, ih]
    · have hpq := hag a (List.mem_cons_self ..) hai
      have hmem : (i ∈ a :: t) ↔ i ∈ t := by
        simp only [List.mem_cons]; exact ⟨fun h => h.resolve_left (Ne.symm hai), Or.inr⟩
      simp only [hmem]
      cases hqa : q a
      · simp [hpq, hqa, ih]
      · simp [hpq, hqa, ih]; omega

/-- Lifting client `i`'s head changes another client's `deps` only through `i`: by one, exactly
when its `FU` on `i` was the new head. -/
theorem deps_lift {H : List Nat} {i j : Nat} (hij : j ≠ i) (hi : i < H.length) :
    deps h cs H j = deps h cs (H.set i (H.getD i 0 + 1)) j +
      (if H.getD j 0 < (chain cs j).length ∧ FU h cs j (H.getD j 0) i = H.getD i 0 + 1
       then 1 else 0) := by
  have hj : (H.set i (H.getD i 0 + 1)).getD j 0 = H.getD j 0 := by
    simp [List.getD_eq_getElem?_getD, Ne.symm hij]
  have hii : (H.set i (H.getD i 0 + 1)).getD i 0 = H.getD i 0 + 1 := by
    simp [List.getD_eq_getElem?_getD, hi]
  have hd : ∀ d, d ≠ i → (H.set i (H.getD i 0 + 1)).getD d 0 = H.getD d 0 := by
    intro d hdi
    simp [List.getD_eq_getElem?_getD, Ne.symm hdi]
  unfold deps
  rw [hj]
  rw [count_split (List.nodup_range) (i := i)]
  · congr 1
    by_cases hic : i < cs.length
    · have him : i ∈ List.range cs.length := List.mem_range.mpr hic
      simp only [him, true_and, hii, decide_eq_true_eq, decide_eq_false_iff_not]
      split <;> split <;> omega
    · have him : i ∉ List.range cs.length := fun h => hic (List.mem_range.mp h)
      have hF : FU h cs j (H.getD j 0) i = 0 := by
        unfold FU; rw [chain_of_ge (by omega)]; rfl
      simp only [him, false_and, ↓reduceIte]
      rw [if_neg (fun h' => by rw [hF] at h'; omega)]
  · intro d _ hdi
    rw [hd d hdi]
  · intro hq
    simp only [decide_eq_true_eq] at hq ⊢
    rw [hii] at hq
    exact ⟨hq.1, hq.2.1, by omega⟩

end lemmas

end Theory
end github_com.anishathalye.porcupine
end Perennial
