/-
Lean-first (no Rocq counterpart).

# The chains, in pure terms (2026-11-02)

PR #46's search keeps a partition's operations as one *chain* per client (`cs[c]`: client `c`'s
operation ids, in the order listed), linearized from the front: client `c`'s first `H[c]`
operations are linearized (`headsSet`), and its *head* is `opAt cs c H[c]`. For the head of `c`
and another client `d`, `FU h cs c k d` is the number of `d`'s operations preceding `c`'s `k`-th
in real time (`firstUnk[d]` holds `FUe`, below, once computed), and `deps h cs H c` the number of clients `d` with
preceding operations not all linearized (`nDeps`).

`ChainsOk h cs` is the PR's premise on a partition, in these terms (`ClientsOk` for a slice of
`Operation`s): the chains hold every operation once, and along each the returns do not decrease.
Under it the operations of a chain preceding an operation are a prefix of it (`fu_prefix`). The
search must respect real time and the chains' order (`Before`). `computeFirstUnk` starts from the
previous operation's bound, so what it computes is `FUe`, the largest `FU` so far along the chain
(`fue_search`); `FUe` over-counts only operations that precede an earlier operation of the chain,
which the operations linearized include whenever that earlier one is linearized, so the candidates
(`DagTheory.Cand` for `Before`) are exactly the heads with no dependency (`cand_iff`), in a set
closed under `Before`.
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

/-- Operation `a`'s return is at most `b`'s. -/
def RetLe (h : List (Op α)) (a b : Nat) : Prop :=
  ∃ oa ob, h[a]? = some oa ∧ h[b]? = some ob ∧ oa.ret ≤ ob.ret

/-- The chains hold every operation of `h` exactly once, and along each chain the returns do not
decrease. -/
def ChainsOk (h : List (Op α)) (cs : List (List Nat)) : Prop :=
  (∀ c, (chain cs c).Nodup ∧ (chain cs c).Pairwise (RetLe h)) ∧
  (∀ y, y < h.length ↔ ∃ c, c < cs.length ∧ y ∈ chain cs c) ∧
  (∀ y c c', y ∈ chain cs c → y ∈ chain cs c' → c = c')

/-- The chains' order: `a` is before `b` in one chain. -/
def chainOrder (cs : List (List Nat)) (a b : Nat) : Prop :=
  ∃ (c i j : Nat), i < j ∧ (chain cs c)[i]? = some a ∧ (chain cs c)[j]? = some b

/-- What the DAG search respects: real time and the chains' order. -/
def Before (h : List (Op α)) (cs : List (List Nat)) (a b : Nat) : Prop :=
  Prec h a b ∨ chainOrder cs a b

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

/-- What `computeFirstUnk` computes for client `c`'s `k`-th operation: the largest `FU` of the
chain's operations so far (it starts from the previous operation's bound). -/
def FUe (h : List (Op α)) (cs : List (List Nat)) (c d : Nat) : Nat → Nat
  | 0 => FU h cs c 0 d
  | k + 1 => max (FUe h cs c d k) (FU h cs c (k + 1) d)

/-- The number of other clients whose operations counted by `c`'s head's `FUe` are not all
linearized (`nDeps`). -/
def deps (h : List (Op α)) (cs : List (List Nat)) (H : List Nat) (c : Nat) : Nat :=
  ((List.range cs.length).filter
    (fun d => decide (d ≠ c ∧ H.getD c 0 < (chain cs c).length ∧
      H.getD d 0 < FUe h cs c d (H.getD c 0)))).length

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

/-- What precedes an operation, an operation returning no later precedes too. -/
theorem prec_of_retLe {a b x : Nat} (h1 : RetLe h a b) (h2 : Prec h b x) : Prec h a x := by
  obtain ⟨oa, ob, ha, hb, h1⟩ := h1
  obtain ⟨ob', ox, hb', hx, h2⟩ := h2
  rw [hb] at hb'; cases hb'
  exact ⟨oa, ox, ha, hx, by omega⟩

/-- The operations of a chain preceding an operation are a prefix of it. -/
theorem fu_prefix (hok : ChainsOk h cs) {c k d i : Nat}
    (hi : i < (chain cs d).length) :
    i < FU h cs c k d ↔ Prec h (chain cs d)[i] (opAt cs c k) := by
  unfold FU
  rw [filter_prefix (hok.1 d).2 (fun a b hab hb => by
    rw [precB_iff] at hb ⊢; exact prec_of_retLe hab hb) i hi, precB_iff]

theorem fu_le {c k d : Nat} : FU h cs c k d ≤ (chain cs d).length := List.length_filter_le _ _

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

theorem fu_le_fue {c d : Nat} : ∀ {k : Nat}, FU h cs c k d ≤ FUe h cs c d k
  | 0 => Nat.le_refl _
  | _ + 1 => Nat.le_max_right _ _

theorem fue_le_iff {c d m : Nat} : ∀ {k : Nat}, FUe h cs c d k ≤ m ↔ ∀ k', k' ≤ k → FU h cs c k' d ≤ m
  | 0 => ⟨fun hk k' hk' => by rw [Nat.le_zero.mp hk']; exact hk, fun hk => hk 0 (Nat.le_refl _)⟩
  | k + 1 => by
    simp only [FUe, Nat.max_le]
    rw [fue_le_iff]
    constructor
    · rintro ⟨h1, h2⟩ k' hk'
      rcases Nat.lt_or_eq_of_le hk' with hlt | rfl
      · exact h1 k' (by omega)
      · exact h2
    · intro hall
      exact ⟨fun k' hk' => hall k' (by omega), hall (k + 1) (Nat.le_refl _)⟩

theorem fue_le {c d k : Nat} : FUe h cs c d k ≤ (chain cs d).length :=
  fue_le_iff.mpr fun _ _ => fu_le

/-- `computeFirstUnk`'s searches, in pure terms: started at `start` (`0`, or the previous
operation's `FUe`), the first index from `start` on whose operation does not precede the head (or
the chain's end) is `max start FU`. -/
theorem fue_search (hok : ChainsOk h cs) {c k d start r : Nat}
    (hsr : start ≤ r) (hrl : r ≤ (chain cs d).length)
    (hpre : ∀ j (hj : j < (chain cs d).length), start ≤ j → j < r →
      Prec h (chain cs d)[j] (opAt cs c k))
    (hstop : ∀ (hr : r < (chain cs d).length), ¬ Prec h (chain cs d)[r] (opAt cs c k)) :
    r = max start (FU h cs c k d) := by
  have hF := @fu_le _ h cs c k d
  rcases Nat.lt_or_ge (FU h cs c k d) start with hlt | hge
  · rw [Nat.max_eq_left (by omega)]
    refine Nat.le_antisymm (Nat.le_of_not_lt fun hgt => ?_) hsr
    have hsl : start < (chain cs d).length := by omega
    exact absurd ((fu_prefix hok hsl).mpr (hpre start hsl (Nat.le_refl _) hgt)) (by omega)
  · rw [Nat.max_eq_right hge]
    rcases Nat.lt_trichotomy r (FU h cs c k d) with hlt | heq | hgt
    · have hrl' : r < (chain cs d).length := by omega
      exact absurd ((fu_prefix hok hrl').mp hlt) (hstop hrl')
    · exact heq
    · have hFl : FU h cs c k d < (chain cs d).length := by omega
      exact absurd ((fu_prefix hok hFl).mpr (hpre _ hFl hge hgt)) (by omega)

/-- `FUe` at the next operation, from the previous one's. -/
theorem fue_succ {c d k : Nat} : FUe h cs c d (k + 1) = max (FUe h cs c d k) (FU h cs c (k + 1) d) :=
  rfl

theorem deps_eq_zero {H : List Nat} {c : Nat} (hc : H.getD c 0 < (chain cs c).length) :
    deps h cs H c = 0 ↔ ∀ d, d < cs.length → d ≠ c → FUe h cs c d (H.getD c 0) ≤ H.getD d 0 := by
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

theorem before_irrefl (hok : ChainsOk h cs) (hwf : CallLeRet h) (y : Nat) : ¬ Before h cs y y := by
  rintro (hp | ⟨c, i, j, hij, hi, hj⟩)
  · exact prec_irrefl hwf y hp
  · exact absurd (pos_unique hok hi hj).2 (by omega)

theorem before_dom (hok : ChainsOk h cs) {a b : Nat} (hab : Before h cs a b) : a < h.length := by
  rcases hab with ⟨oa, _, ha, _⟩ | ⟨c, i, _, _, hi, _⟩
  · exact (List.getElem?_eq_some_iff.mp ha).1
  · exact lt_length_of_mem hok (List.mem_of_getElem? hi)

/-- If what precedes client `c`'s `k`-th operation is linearized, `FU` is at most the heads. -/
theorem fu_le_head (hok : ChainsOk h cs) {H B : List Nat} {c k d : Nat}
    (hB : ∀ y, y ∈ B ↔ headsSet cs H y)
    (hpre : ∀ z, Prec h z (opAt cs c k) → z ∈ B) : FU h cs c k d ≤ H.getD d 0 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hdl : H.getD d 0 < (chain cs d).length := Nat.lt_of_lt_of_le hlt fu_le
  obtain ⟨c', k', hk', he⟩ := (hB _).mp (hpre _ ((fu_prefix hok hdl).mp hlt))
  obtain ⟨rfl, rfl⟩ := pos_unique hok he (List.getElem?_eq_getElem hdl)
  omega

/-- The candidates (for `Before`) of a set of operations closed under `Before` are the heads with
no dependency. -/
theorem cand_iff (hok : ChainsOk h cs) (hwf : CallLeRet h) {H B : List Nat} {y : Nat}
    (hB : ∀ y, y ∈ B ↔ headsSet cs H y) (hdc : ∀ z w, w ∈ B → Before h cs z w → z ∈ B) :
    Cand h (Before h cs) B y ↔ ∃ c, c < cs.length ∧ H.getD c 0 < (chain cs c).length ∧
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
      -- the head is before `y` in the chain, so it is linearized: impossible
      have hp : Before h cs (chain cs c)[H.getD c 0] y :=
        Or.inr ⟨c, H.getD c 0, k, hlt, List.getElem?_eq_getElem (by omega), hk'⟩
      obtain ⟨c', k', hk'', he⟩ := (hB _).mp (hpre _ hp)
      obtain ⟨rfl, rfl⟩ := pos_unique hok he (List.getElem?_eq_getElem (by omega))
      omega
    have hcl : H.getD c 0 < (chain cs c).length := by omega
    have hop : opAt cs c (H.getD c 0) = y := by rw [opAt_eq hcl]; simp only [hHk, hke]
    refine ⟨c, hc, hcl, hop, ?_⟩
    rw [deps_eq_zero hcl]
    intro d hd hdc'
    refine fue_le_iff.mpr fun k' hk'' => fu_le_head hok hB fun z hz => ?_
    rcases Nat.lt_or_eq_of_le hk'' with hlt | rfl
    · -- an earlier operation of the chain is linearized, and with it what precedes it
      have hk'l : k' < (chain cs c).length := by omega
      have hin : opAt cs c k' ∈ B := (hB _).mpr ⟨c, k', hlt, by
        rw [opAt_eq hk'l]; exact List.getElem?_eq_getElem hk'l⟩
      exact hdc z _ hin (Or.inl hz)
    · rw [hop] at hz; exact hpre z (Or.inl hz)
  · rintro ⟨c, hc, hcl, rfl, hdeps⟩
    rw [deps_eq_zero hcl] at hdeps
    have hyc : (chain cs c)[H.getD c 0]? = some (opAt cs c (H.getD c 0)) := by
      rw [opAt_eq hcl]; exact List.getElem?_eq_getElem hcl
    refine ⟨lt_length_of_mem hok (List.mem_of_getElem? hyc), fun hyB => ?_, fun z hz => ?_⟩
    · obtain ⟨c', k', hk', he⟩ := (hB _).mp hyB
      obtain ⟨rfl, rfl⟩ := pos_unique hok he hyc
      omega
    · rcases hz with hz | ⟨c', i, j, hij, hi, hj⟩
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
          · -- the head returns no later than `z`, which precedes it
            have hr : RetLe h (chain cs d)[H.getD d 0] z := by
              rw [← hie]; exact List.pairwise_iff_getElem.mp (hok.1 d).2 _ i hcl hi hgt
            rw [opAt_eq hcl] at hz
            exact prec_irrefl hwf _ (prec_of_retLe hr hz)
          · subst heq
            rw [opAt_eq hcl, hie] at hz
            exact prec_irrefl hwf _ hz
        · have := (fu_prefix hok hi).mpr (by rw [hie]; exact hz)
          exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le this fu_le_fue) (hdeps d hd hdc)
      · obtain ⟨rfl, rfl⟩ := pos_unique hok hj hyc
        exact (hB z).mpr ⟨c', i, hij, hi⟩

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
when its `FUe` on `i` was the new head. -/
theorem deps_lift {H : List Nat} {i j : Nat} (hij : j ≠ i) (hi : i < H.length) :
    deps h cs H j = deps h cs (H.set i (H.getD i 0 + 1)) j +
      (if H.getD j 0 < (chain cs j).length ∧ FUe h cs j i (H.getD j 0) = H.getD i 0 + 1
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
      have hF : FUe h cs j i (H.getD j 0) = 0 := by
        have := @fue_le _ h cs j i (H.getD j 0); rw [chain_of_ge (by omega), List.length_nil] at this; omega
      simp only [him, false_and, ↓reduceIte]
      exact (ite_eq_right_of_eq_false _ _ (eq_false fun h0 => by rw [hF] at h0; omega)).symm
  · intro d _ hdi
    rw [hd d hdi]
  · intro hq
    simp only [decide_eq_true_eq] at hq ⊢
    rw [hii] at hq
    exact ⟨hq.1, hq.2.1, by omega⟩


/-! ## The heads of a stack -/

/-- The heads when the operations `B` are linearized: how many of each chain's are in `B` (the
code's `client.head`s, for the stack's ids). -/
def headsOf (cs : List (List Nat)) (B : List Nat) : List Nat :=
  (List.range cs.length).map fun c => ((chain cs c).filter (fun y => decide (y ∈ B))).length

/-- The operations of `B` are each chain's first `H[c]`, by position. -/
def PosOk (cs : List (List Nat)) (B H : List Nat) : Prop :=
  ∀ c i (hi : i < (chain cs c).length), ((chain cs c)[i] ∈ B ↔ i < H.getD c 0)

theorem headsOf_getD {B : List Nat} (c : Nat) :
    (headsOf cs B).getD c 0 = ((chain cs c).filter (fun y => decide (y ∈ B))).length := by
  unfold headsOf
  by_cases hc : c < cs.length
  · simp [List.getD_eq_getElem?_getD, hc]
  · rw [chain_of_ge (by omega)]
    simp [List.getD_eq_getElem?_getD, hc]

theorem headsOf_length {B : List Nat} : (headsOf cs B).length = cs.length := by
  simp [headsOf]

/-- A list whose members in `B` are exactly its first `m` has `m` of them. -/
theorem filter_prefix_count {B : List Nat} :
    ∀ {l : List Nat} {m : Nat}, m ≤ l.length →
      (∀ i (hi : i < l.length), (l[i] ∈ B ↔ i < m)) →
      (l.filter (fun y => decide (y ∈ B))).length = m
  | [], m, hm, _ => by simp at hm; simp [hm]
  | a :: t, 0, _, hall => by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro y hy hyB
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    exact absurd ((hall i hi).mp (by simpa using hyB)) (Nat.not_lt_zero _)
  | a :: t, m + 1, hm, hall => by
    have ha : a ∈ B := (hall 0 (by simp)).mpr (by omega)
    rw [List.filter_cons_of_pos (by simpa using ha), List.length_cons]
    congr 1
    refine filter_prefix_count (by simp at hm; omega) fun i hi => ?_
    have := hall (i + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    rw [this]; omega

/-- Heads given by position are `headsOf`. -/
theorem headsOf_eq {B H : List Nat} (hpos : PosOk cs B H) (hH : HeadsOk cs H) :
    headsOf cs B = H := by
  apply List.ext_getElem (by rw [headsOf_length, hH.1])
  intro c h1 h2
  have hg := headsOf_getD (cs := cs) (B := B) c
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at hg
  rw [hg, filter_prefix_count (hH.2 c) (hpos c)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem ids_iff_headsSet (hok : ChainsOk h cs) {B H : List Nat} (hpos : PosOk cs B H)
    (hlt : ∀ y ∈ B, y < h.length) : ∀ y, y ∈ B ↔ headsSet cs H y := by
  intro y
  constructor
  · intro hy
    obtain ⟨c, _, hyc⟩ := (hok.2.1 y).mp (hlt y hy)
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hyc
    refine ⟨c, i, (hpos c i hi).mp (hie ▸ hy), by rw [List.getElem?_eq_getElem hi, hie]⟩
  · rintro ⟨c, k, hk, he⟩
    obtain ⟨hv, rfl⟩ := List.getElem?_eq_some_iff.mp he
    exact (hpos c k hv).mpr hk

theorem posOk_nil : PosOk cs [] (List.replicate cs.length 0) := by
  intro c i hi
  simp only [List.not_mem_nil, false_iff, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

theorem headsOk_nil : HeadsOk cs (List.replicate cs.length 0) := by
  refine ⟨List.length_replicate, fun c => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

theorem set_getD {H : List Nat} {c c' v : Nat} (hc : c < H.length) :
    (H.set c v).getD c' 0 = if c' = c then v else H.getD c' 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h' : c' = c
  · subst h'; simp [hc]
  · simp [Ne.symm h', h']

/-- A candidate pushed: it is its client's head, and that head moves by one. -/
theorem posOk_push (hok : ChainsOk h cs) (hwf : CallLeRet h) {B H : List Nat} {y : Nat}
    (hpos : PosOk cs B H) (hH : HeadsOk cs H) (hlt : ∀ y ∈ B, y < h.length)
    (hdc : ∀ z w, w ∈ B → Before h cs z w → z ∈ B) (hcand : Cand h (Before h cs) B y) :
    ∃ c, c < cs.length ∧ H.getD c 0 < (chain cs c).length ∧ opAt cs c (H.getD c 0) = y ∧
      PosOk cs (y :: B) (H.set c (H.getD c 0 + 1)) ∧ HeadsOk cs (H.set c (H.getD c 0 + 1)) := by
  obtain ⟨c, hc, hcl, hop, _⟩ := (cand_iff hok hwf (ids_iff_headsSet hok hpos hlt) hdc).mp hcand
  have hcH : c < H.length := by rw [hH.1]; exact hc
  have hyc : (chain cs c)[H.getD c 0]? = some y := by
    rw [← hop, opAt_eq hcl]; exact List.getElem?_eq_getElem hcl
  refine ⟨c, hc, hcl, hop, fun c' i hi => ?_, ⟨by rw [List.length_set, hH.1], fun c' => ?_⟩⟩
  · rw [set_getD hcH, List.mem_cons, hpos c' i hi]
    constructor
    · rintro (he | hlt')
      · obtain ⟨rfl, rfl⟩ := pos_unique hok (List.getElem?_eq_getElem hi ▸ congrArg some he) hyc
        simp
      · by_cases hcc : c' = c
        · subst hcc; simp only [↓reduceIte]; omega
        · simp only [hcc, ↓reduceIte]; exact hlt'
    · intro hi'
      by_cases hcc : c' = c
      · subst hcc
        simp only [↓reduceIte] at hi'
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi') with h1 | h1
        · exact Or.inr h1
        · subst h1
          left
          have := List.getElem?_eq_getElem hi
          rw [hyc] at this
          exact (Option.some.inj this).symm
      · simp only [hcc, ↓reduceIte] at hi'
        exact Or.inr hi'
  · rw [set_getD hcH]
    split
    · rename_i h'; subst h'; omega
    · exact hH.2 c'

/-- On a stack of candidates (for `Before`), the operations linearized are each chain's first
`headsOf`, and the heads are within the chains. -/
theorem heads_ids {σ : Type} (hok : ChainsOk h cs) (hwf : CallLeRet h) :
    ∀ {fs : List (Frame σ)}, FramesStruct h cs (Before h cs) fs →
      PosOk cs (ids fs) (headsOf cs (ids fs)) ∧ HeadsOk cs (headsOf cs (ids fs))
  | [], _ => by
    rw [show ids ([] : List (Frame σ)) = [] from rfl, headsOf_eq posOk_nil headsOk_nil]
    exact ⟨posOk_nil, headsOk_nil⟩
  | f :: fs, hfs => by
    obtain ⟨hpos, hH⟩ := heads_ids hok hwf hfs.1
    obtain ⟨c, _, _, _, hpos', hH'⟩ := posOk_push hok hwf hpos hH (framesStruct_lt hfs.1)
      (fun z w hw hzw => framesStruct_below hfs.1 w hw z hzw) (framesStruct_cand hfs)
    have hids : ids (f :: fs) = f.id :: ids fs := rfl
    rw [hids, headsOf_eq hpos' hH']
    exact ⟨hpos', hH'⟩

/-- The newest frame lifted its client's head; the heads below move by one there. -/
theorem headsOf_cons {σ : Type} (hok : ChainsOk h cs) (hwf : CallLeRet h) {f : Frame σ}
    {fs : List (Frame σ)} (hfs : FramesStruct h cs (Before h cs) (f :: fs)) :
    ∃ c, c < cs.length ∧ (headsOf cs (ids fs)).getD c 0 < (chain cs c).length ∧
      opAt cs c ((headsOf cs (ids fs)).getD c 0) = f.id ∧
      headsOf cs (ids (f :: fs)) =
        (headsOf cs (ids fs)).set c ((headsOf cs (ids fs)).getD c 0 + 1) := by
  obtain ⟨hpos, hH⟩ := heads_ids hok hwf hfs.1
  obtain ⟨c, hc, hcl, hop, hpos', hH'⟩ := posOk_push hok hwf hpos hH (framesStruct_lt hfs.1)
    (fun z w hw hzw => framesStruct_below hfs.1 w hw z hzw) (framesStruct_cand hfs)
  exact ⟨c, hc, hcl, hop, headsOf_eq hpos' hH'⟩

end lemmas

end Theory
end github_com.anishathalye.porcupine
end Perennial
