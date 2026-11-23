/-
**`Clean` of its own output, and of a path with one more plain element** (bkarea, 2026-11-22):
`Clean(Clean(p)) = Clean(p)` (`cleanModel_idem`), `Clean(p + "/" + s) = Clean(p) ⊕ s` for a plain
`s` (`cleanModel_snoc`), so that `Join` in two steps is `Join` in one (`joinModel_pair`), and
`Clean(p)` is no longer than `p` (`cleanModel_length_le`). Lean-first; pure, over the model of
`Proof/path/Model.lean`, for any path (relative or rooted, with `.`, `..` and repeated slashes).

The main loop's state `(r, o, dotdot)` is followed whole (`cleanLoopS`), so that a run over `p ++ t`,
`t` empty or starting with `/`, is the run over `p` and then the run from its end (`cleanLoopS_app`).
The output's shape (`CInv`): the root's `/` if rooted, then elements joined by `/`, first `k` copies of
`..` (none if rooted), then clean elements (`cleanSeg`), with `dotdot` the length of the `..` prefix
(`1` if rooted). Every round keeps it (`cleanStep_inv`, the backtracking loop of a `..` removing the
last element, `backW_last`), and the loop over an output of that shape copies it unchanged
(`cleanLoopS_shape`).
-/
module

public import Proof.path.Segs
public import Proof.path.CleanFits

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace path

/-! ### The loop, with its whole state -/

/-- `Clean`'s main loop with fuel `f`, returning its whole state `(r, o, dotdot)`. -/
def cleanLoopSF (p : List w8) (rooted : Bool) : Nat → Nat → List w8 → Nat → Nat × List w8 × Nat
  | 0, r, o, dd => (r, o, dd)
  | f + 1, r, o, dd =>
    if r < p.length then
      let st := cleanStep p rooted r o dd
      cleanLoopSF p rooted f st.1 st.2.1 st.2.2
    else (r, o, dd)

/-- `Clean`'s main loop from `r`, returning its whole state. -/
def cleanLoopS (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat) :
    Nat × List w8 × Nat :=
  cleanLoopSF p rooted (p.length - r) r o dd

theorem cleanLoopSF_out (p : List w8) (rooted : Bool) (f r : Nat) (o : List w8) (dd : Nat) :
    (cleanLoopSF p rooted f r o dd).2.1 = cleanLoopF p rooted f r o dd := by
  induction f generalizing r o dd with
  | zero => rfl
  | succ f ih =>
    simp only [cleanLoopSF, cleanLoopF]
    split
    · exact ih _ _ _
    · rfl

theorem cleanLoop_eq_S (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat) :
    cleanLoop p rooted r o dd = (cleanLoopS p rooted r o dd).2.1 :=
  (cleanLoopSF_out p rooted _ r o dd).symm

theorem cleanLoopSF_fuel (p : List w8) (rooted : Bool) (f g r : Nat) (o : List w8) (dd : Nat)
    (hf : p.length - r ≤ f) (hg : p.length - r ≤ g) :
    cleanLoopSF p rooted f r o dd = cleanLoopSF p rooted g r o dd := by
  induction f generalizing g r o dd with
  | zero =>
    cases g with
    | zero => rfl
    | succ g => simp only [cleanLoopSF]; rw [if_neg (by omega)]
  | succ f ih =>
    cases g with
    | zero => simp only [cleanLoopSF]; rw [if_neg (by omega)]
    | succ g =>
      simp only [cleanLoopSF]
      split
      · next h =>
        have := cleanStep_fst_gt p rooted r o dd h
        exact ih g _ _ _ (by omega) (by omega)
      · rfl

/-- One round of the loop. -/
theorem cleanLoopS_step (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : r < p.length) :
    cleanLoopS p rooted r o dd =
      cleanLoopS p rooted (cleanStep p rooted r o dd).1 (cleanStep p rooted r o dd).2.1
        (cleanStep p rooted r o dd).2.2 := by
  unfold cleanLoopS
  obtain ⟨f, hf⟩ : ∃ f, p.length - r = f + 1 := ⟨p.length - r - 1, by omega⟩
  rw [hf, cleanLoopSF, if_pos h]
  have := cleanStep_fst_gt p rooted r o dd h
  exact cleanLoopSF_fuel p rooted _ _ _ _ _ (by omega) (by omega)

/-- The end of the loop. -/
theorem cleanLoopS_stop (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : ¬ r < p.length) : cleanLoopS p rooted r o dd = (r, o, dd) := by
  unfold cleanLoopS
  cases hf : p.length - r with
  | zero => rfl
  | succ f => rw [cleanLoopSF, if_neg h]

/-! ### Positions -/

/-- A round ends within the input. -/
theorem cleanStep_fst_le (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : r < p.length) : (cleanStep p rooted r o dd).1 ≤ p.length := by
  unfold cleanStep
  split
  · simp; omega
  split
  · simp; omega
  split
  · next h1 h2 h3 =>
    have : r + 2 ≤ p.length := by
      rcases h3.2.2 with h4 | h4
      · omega
      · have := getD_slash_lt h4; omega
    split
    · simp; omega
    split <;> simp <;> omega
  · exact copyElem_fst_le p r _ (by omega)

/-- **A run ends at the end of the input.** -/
theorem cleanLoopS_fst (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : r ≤ p.length) : (cleanLoopS p rooted r o dd).1 = p.length := by
  generalize hn : p.length - r = n
  induction n using Nat.strongRecOn generalizing r o dd with
  | _ n ih =>
    by_cases hr : r < p.length
    · rw [cleanLoopS_step _ _ _ _ _ hr]
      have h1 := cleanStep_fst_gt p rooted r o dd hr
      have h2 := cleanStep_fst_le p rooted r o dd hr
      exact ih _ (by omega) _ _ _ h2 rfl
    · rw [cleanLoopS_stop _ _ _ _ _ hr]; simp; omega

/-! ### A run over `p ++ t` -/

theorem getD_app_lt {p t : List w8} {i : Nat} (h : i < p.length) :
    (p ++ t).getD i 0 = p.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_len (p : List w8) : p.getD p.length 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem getD_app_len {p t : List w8} (ht : t = [] ∨ t.head? = some slash) :
    (p ++ t).getD p.length 0 = 0 ∨ (p ++ t).getD p.length 0 = slash := by
  rcases ht with rfl | ht
  · left; simpa using getD_len p
  · right
    cases t with
    | nil => simp at ht
    | cons x t =>
      simp at ht; subst ht
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp

/-- At `i ≤ len(p)`, "the end or a `/`" reads the same in `p ++ t` as in `p`. -/
theorem endOrSlash_app {p t : List w8} (ht : t = [] ∨ t.head? = some slash) {i : Nat}
    (hi : i ≤ p.length) :
    (i = (p ++ t).length ∨ (p ++ t).getD i 0 = slash) ↔ (i = p.length ∨ p.getD i 0 = slash) := by
  rcases Nat.lt_or_ge i p.length with h | h
  · rw [getD_app_lt h]
    have h1 : i ≠ (p ++ t).length := by simp; omega
    have h2 : i ≠ p.length := by omega
    constructor
    · rintro (h' | h')
      · exact absurd h' h1
      · exact Or.inr h'
    · rintro (h' | h')
      · exact absurd h' h2
      · exact Or.inr h'
  · have hi' : i = p.length := by omega
    subst hi'
    simp only [true_or, iff_true]
    rcases ht with rfl | ht
    · left; simp
    · right
      rcases getD_app_len (p := p) (Or.inr ht) with h0 | h0
      · cases t with
        | nil => simp at ht
        | cons x t =>
          simp at ht; subst ht
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at h0 ⊢; simp at h0 ⊢
      · exact h0

theorem not_dot_len {p t : List w8} (ht : t = [] ∨ t.head? = some slash) :
    (p ++ t).getD p.length 0 ≠ dot := by
  rcases getD_app_len (p := p) ht with h | h <;> rw [h] <;> decide

/-- The copy of an element reads the same in `p ++ t` as in `p`. -/
theorem copyElem_app {p t : List w8} (ht : t = [] ∨ t.head? = some slash) (r : Nat) (o : List w8)
    (hr : r ≤ p.length) : copyElem (p ++ t) r o = copyElem p r o := by
  generalize hn : p.length - r = n
  induction n generalizing r o with
  | zero =>
    have hr' : r = p.length := by omega
    subst hr'
    rw [copyElem_stop p p.length o (by omega)]
    rw [copyElem_stop]
    rintro ⟨h1, h2⟩
    rcases getD_app_len (p := p) ht with h | h
    · rcases ht with rfl | ht
      · simp at h1
      · cases t with
        | nil => simp at ht
        | cons x t =>
          simp at ht; subst ht
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at h; simp at h
    · exact h2 h
  | succ n ih =>
    have hr' : r < p.length := by omega
    by_cases hc : p.getD r 0 ≠ slash
    · rw [copyElem_step p r o hr' hc, copyElem_step (p ++ t) r o (by simp; omega)
        (by rw [getD_app_lt hr']; exact hc), getD_app_lt hr']
      exact ih (r + 1) _ (by omega) (by omega)
    · rw [copyElem_stop p r o (by rintro ⟨-, h⟩; exact hc h),
        copyElem_stop (p ++ t) r o (by rintro ⟨-, h⟩; rw [getD_app_lt hr'] at h; exact hc h)]

/-- **A round at `r < len(p)` reads the same in `p ++ t` as in `p`.** -/
theorem cleanStep_app {p t : List w8} (ht : t = [] ∨ t.head? = some slash) (rooted : Bool) (r : Nat)
    (o : List w8) (dd : Nat) (hr : r < p.length) :
    cleanStep (p ++ t) rooted r o dd = cleanStep p rooted r o dd := by
  have c0 := getD_app_lt (t := t) hr
  have c1 := endOrSlash_app (p := p) ht (i := r + 1) (by omega)
  have c2 : ((p ++ t).getD (r + 1) 0 = dot ∧ (r + 2 = (p ++ t).length ∨ (p ++ t).getD (r + 2) 0 = slash)) ↔
      (p.getD (r + 1) 0 = dot ∧ (r + 2 = p.length ∨ p.getD (r + 2) 0 = slash)) := by
    rcases Nat.lt_or_ge (r + 1) p.length with h | h
    · rw [getD_app_lt h, endOrSlash_app (p := p) ht (i := r + 2) (by omega)]
    · have he : r + 1 = p.length := by omega
      have h1 : (p ++ t).getD (r + 1) 0 ≠ dot := by rw [he]; exact not_dot_len ht
      have h2 : p.getD (r + 1) 0 ≠ dot := by rw [he, getD_len]; decide
      exact ⟨fun ⟨h3, _⟩ => absurd h3 h1, fun ⟨h3, _⟩ => absurd h3 h2⟩
  unfold cleanStep
  rw [c0]
  simp only [c1, c2, copyElem_app (p := p) ht r _ (by omega)]

/-- **A run over `p ++ t` (`t` empty or starting with `/`) from `r ≤ len(p)`** is the run over `p`,
then the run from the end of `p` at the state it left. -/
theorem cleanLoopS_app {p t : List w8} (ht : t = [] ∨ t.head? = some slash) (rooted : Bool)
    (r : Nat) (o : List w8) (dd : Nat) (hr : r ≤ p.length) :
    cleanLoopS (p ++ t) rooted r o dd =
      cleanLoopS (p ++ t) rooted p.length (cleanLoopS p rooted r o dd).2.1
        (cleanLoopS p rooted r o dd).2.2 := by
  generalize hn : p.length - r = n
  induction n using Nat.strongRecOn generalizing r o dd with
  | _ n ih =>
    by_cases h : r < p.length
    · rw [cleanLoopS_step (p ++ t) rooted r o dd (by simp; omega), cleanLoopS_step p rooted r o dd h,
        cleanStep_app ht _ _ _ _ h]
      have h1 := cleanStep_fst_gt p rooted r o dd h
      have h2 := cleanStep_fst_le p rooted r o dd h
      exact ih _ (by omega) _ _ _ h2 rfl
    · have hr' : r = p.length := by omega
      subst hr'
      rw [cleanLoopS_stop p _ _ _ _ h]

/-! ### The output's shape -/

/-- Elements joined by `/`. -/
def rend (es : List (List w8)) : List w8 := (segsPath es).tail

/-- `..`. -/
abbrev dd2 : List w8 := [dot, dot]

theorem rend_nil : rend [] = [] := rfl

theorem segsPath_ne_nil {es : List (List w8)} (h : es ≠ []) : ∃ rest, segsPath es = slash :: rest := by
  cases es with
  | nil => exact absurd rfl h
  | cons e es => exact segsPath_cons_ne e es

theorem segsPath_eq_slash_rend {es : List (List w8)} (h : es ≠ []) : segsPath es = slash :: rend es := by
  obtain ⟨rest, hr⟩ := segsPath_ne_nil h
  rw [rend, hr]; rfl

theorem rend_snoc (es : List (List w8)) (s : List w8) :
    rend (es ++ [s]) = if es = [] then s else rend es ++ [slash] ++ s := by
  unfold rend
  rw [segsPath_snoc]
  split
  · next h => subst h; rfl
  · next h =>
    obtain ⟨rest, hr⟩ := segsPath_ne_nil h
    rw [hr]; rfl

theorem rend_single (s : List w8) : rend [s] = s := by
  simpa using rend_snoc [] s

theorem rend_append {a b : List (List w8)} (ha : a ≠ []) (hb : b ≠ []) :
    rend (a ++ b) = rend a ++ [slash] ++ rend b := by
  unfold rend
  rw [segsPath_append, segsPath_eq_slash_rend hb]
  obtain ⟨rest, hr⟩ := segsPath_ne_nil ha
  rw [hr]; simp

/-- An element that is not empty. -/
def neSeg (s : List w8) : Prop := s ≠ []

theorem rend_eq_nil {es : List (List w8)} (h : ∀ s ∈ es, s ≠ []) : rend es = [] ↔ es = [] := by
  constructor
  · intro hr
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨es', e, rfl⟩ : ∃ es' e, es = es' ++ [e] := ⟨es.dropLast, es.getLast hne,
      (List.dropLast_concat_getLast hne).symm⟩
    have he : e ≠ [] := h e (by simp)
    rw [rend_snoc] at hr
    split at hr
    · exact he hr
    · simp [he] at hr
  · rintro rfl; rfl

/-- **The shape of the loop's output** (see the file header): the root's `/` if rooted, then `k`
copies of `..` (none if rooted) and clean elements, joined by `/`; `dotdot` the length of what
precedes the clean elements. -/
def CInv (rooted : Bool) (o : List w8) (dd : Nat) : Prop :=
  ∃ (k : Nat) (segs : List (List w8)), (∀ s ∈ segs, cleanSeg s) ∧ (rooted = true → k = 0) ∧
    o = (if rooted then [slash] else []) ++ rend (List.replicate k dd2 ++ segs) ∧
    dd = (if rooted then 1 else 0) + (rend (List.replicate k dd2)).length

theorem shape_ne {k : Nat} {segs : List (List w8)} (h : ∀ s ∈ segs, cleanSeg s) :
    ∀ s ∈ List.replicate k dd2 ++ segs, s ≠ [] := by
  intro s hs
  simp only [List.mem_append, List.mem_replicate] at hs
  rcases hs with ⟨-, rfl⟩ | hs
  · simp
  · exact (h s hs).1

theorem CInv_init (rooted : Bool) :
    CInv rooted (if rooted then [slash] else []) (if rooted then 1 else 0) :=
  ⟨0, [], by simp, fun _ => rfl, by simp [rend_nil], by simp [rend_nil]⟩

/-! ### The backtracking loop -/

theorem backW_run (o : List w8) (dd a : Nat) (hdd : dd ≤ a) :
    ∀ j, (∀ i, a < i → i ≤ a + j → o.getD i 0 ≠ slash) → backW o dd (a + j) = backW o dd a := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    rw [show a + (j + 1) = (a + j) + 1 by omega, backW_step o dd (a + j)
      ⟨by omega, h _ (by omega) (by omega)⟩]
    exact ih (fun i h1 h2 => h i h1 (by omega))

theorem backW_at (o : List w8) (dd a : Nat) (h : dd = a ∨ o.getD a 0 = slash) : backW o dd a = a := by
  apply backW_stop
  rintro ⟨h1, h2⟩
  rcases h with rfl | h
  · omega
  · exact h2 h

/-- **A `..` after clean elements removes the last one** (`o.take (backW …)`): of
`A ++ sep ++ s`, `s` the last element (non-empty, no `/`), `sep` the `/` before it or nothing when
`A` ends at `dotdot`, the loop stops at the end of `A`. -/
theorem backW_last (A sep s : List w8) (dd : Nat) (hs : s ≠ []) (hsl : ∀ c ∈ s, c ≠ slash)
    (hdd : dd ≤ A.length) (hsep : sep = [slash] ∨ (sep = [] ∧ A.length = dd)) :
    backW (A ++ sep ++ s) dd ((A ++ sep ++ s).length - 1) = A.length := by
  have hsl' : ∀ i, i < s.length → s.getD i 0 ≠ slash := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hsl _ (List.getElem_mem hi)
  rcases hsep with rfl | ⟨rfl, hA⟩
  · have hl : (A ++ [slash] ++ s).length - 1 = A.length + s.length := by simp
    rw [hl, backW_run _ dd A.length hdd s.length]
    · apply backW_at; right
      rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega)]
      (try simp)
    · intro i h1 h2
      rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega),
        show i - A.length = (i - A.length - 1) + 1 by omega]
      simp only [List.singleton_append, List.getElem?_cons_succ]
      have := hsl' (i - A.length - 1) (by omega)
      rw [List.getD_eq_getElem?_getD] at this
      simpa using this
  · have hs1 : 1 ≤ s.length := by cases s with | nil => exact absurd rfl hs | cons _ _ => simp
    have hl : (A ++ [] ++ s).length - 1 = A.length + (s.length - 1) := by simp; omega
    rw [hl, backW_run _ dd A.length hdd (s.length - 1)]
    · exact backW_at _ _ _ (Or.inl hA.symm)
    · intro i h1 h2
      rw [List.getD_eq_getElem?_getD, List.append_nil, List.getElem?_append_right (by omega)]
      have := hsl' (i - A.length) (by omega)
      rw [List.getD_eq_getElem?_getD] at this
      exact this

/-! ### Every round keeps the shape -/

theorem rend_len_le {R segs : List (List w8)} (h : ∀ s ∈ R ++ segs, s ≠ []) :
    (rend R).length ≤ (rend (R ++ segs)).length := by
  by_cases hR : R = []
  · subst hR; simp [rend_nil]
  by_cases hs : segs = []
  · subst hs; simp
  rw [rend_append hR hs]; simp

theorem rend_len_lt {R segs : List (List w8)} (h : ∀ s ∈ R ++ segs, s ≠ []) (hs : segs ≠ []) :
    (rend R).length < (rend (R ++ segs)).length := by
  have hne : rend segs ≠ [] := by
    rw [Ne, rend_eq_nil (fun s hs' => h s (by simp [hs']))]; exact hs
  have h0 : 0 < (rend segs).length := List.length_pos_iff.2 hne
  by_cases hR : R = []
  · subst hR; simpa [rend_nil] using h0
  rw [rend_append hR hs]; simp

theorem pre_len (rt : Bool) : (if rt then [slash] else [] : List w8).length = if rt then 1 else 0 := by
  cases rt <;> rfl

/-- The separator before a copied element: the output is neither empty nor the root exactly when it
has an element. -/
theorem sep_iff {rt : Bool} {k : Nat} {segs : List (List w8)} (hsegs : ∀ s ∈ segs, cleanSeg s)
    {o : List w8} (ho : o = (if rt then [slash] else []) ++ rend (List.replicate k dd2 ++ segs)) :
    ((rt = true ∧ o.length ≠ 1) ∨ ((!rt) = true ∧ o.length ≠ 0)) ↔
      List.replicate k dd2 ++ segs ≠ [] := by
  have hn := rend_eq_nil (shape_ne (k := k) hsegs)
  subst ho
  cases rt <;> simp [hn]

/-- **The element a round copies is clean**: not empty, no `/`, neither `.` nor `..`. -/
theorem copied_clean (p : List w8) (r k : Nat) (hr : r < p.length) (hs : p.getD r 0 ≠ slash)
    (h1 : ¬ (p.getD r 0 = dot ∧ (r + 1 = p.length ∨ p.getD (r + 1) 0 = slash)))
    (h2 : ¬ (p.getD r 0 = dot ∧ p.getD (r + 1) 0 = dot ∧ (r + 2 = p.length ∨ p.getD (r + 2) 0 = slash)))
    (hns : ∀ c ∈ (p.drop r).take k, c ≠ slash) (hend : r + k = p.length ∨ p.getD (r + k) 0 = slash)
    (hk : r + k ≤ p.length) :
    cleanSeg ((p.drop r).take k) := by
  have hget : ∀ i, i < k → ((p.drop r).take k)[i]? = some (p.getD (r + i) 0) := by
    intro i hi
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  have hlen : ((p.drop r).take k).length = k := by simp; omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    rcases hend with h | h
    · omega
    · exact hs (by simpa using h)
  refine ⟨?_, hns, ?_, ?_⟩
  · intro h; rw [h] at hlen; simp at hlen; omega
  · intro h
    have hk1 : k = 1 := by rw [h] at hlen; simp at hlen; omega
    subst hk1
    have := hget 0 (by omega); rw [h] at this; simp at this
    exact h1 ⟨this.symm, by simpa using hend⟩
  · intro h
    have hk2 : k = 2 := by rw [h] at hlen; simp at hlen; omega
    subst hk2
    have e0 := hget 0 (by omega); rw [h] at e0; simp at e0
    have e1 := hget 1 (by omega); rw [h] at e1; simp at e1
    exact h2 ⟨e0.symm, e1.symm, by simpa using hend⟩

/-- **A round keeps the output's shape.** -/
theorem cleanStep_inv (p : List w8) (rt : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (hr : r < p.length) (hI : CInv rt o dd) :
    CInv rt (cleanStep p rt r o dd).2.1 (cleanStep p rt r o dd).2.2 := by
  obtain ⟨k, segs, hsegs, hk, ho, hdd⟩ := hI
  have hne := shape_ne (k := k) hsegs
  unfold cleanStep
  split
  · exact ⟨k, segs, hsegs, hk, ho, hdd⟩
  split
  · exact ⟨k, segs, hsegs, hk, ho, hdd⟩
  split
  · split
    · next hlt =>
      -- a `..` after an element: the last one removed
      have hseg : segs ≠ [] := by
        rintro rfl
        rw [ho, hdd] at hlt
        cases rt <;> simp at hlt <;> omega
      obtain ⟨segs', e, rfl⟩ : ∃ segs' e, segs = segs' ++ [e] :=
        ⟨segs.dropLast, segs.getLast hseg, (List.dropLast_concat_getLast hseg).symm⟩
      have he := hsegs e (by simp)
      have hsegs' : ∀ s ∈ segs', cleanSeg s := fun s hs => hsegs s (by simp [hs])
      have hne' := shape_ne (k := k) hsegs'
      obtain ⟨A, hA⟩ : ∃ A : List w8,
          A = (if rt then [slash] else [] : List w8) ++ rend (List.replicate k dd2 ++ segs') := ⟨_, rfl⟩
      have hoA : o = A ++ (if List.replicate k dd2 ++ segs' = [] then [] else [slash]) ++ e := by
        rw [ho, hA, show List.replicate k dd2 ++ (segs' ++ [e]) = (List.replicate k dd2 ++ segs') ++ [e]
          by simp, rend_snoc]
        by_cases h0 : List.replicate k dd2 ++ segs' = []
        · rw [if_pos h0, if_pos h0, h0, rend_nil]; simp
        · rw [if_neg h0, if_neg h0]; simp
      have hddA : dd ≤ A.length := by
        rw [hdd, hA]; simp only [List.length_append, pre_len]
        have := rend_len_le (R := List.replicate k dd2) (segs := segs') hne'; omega
      have hsep : (if List.replicate k dd2 ++ segs' = [] then [] else [slash]) = [slash] ∨
          ((if List.replicate k dd2 ++ segs' = [] then [] else [slash] : List w8) = [] ∧
            A.length = dd) := by
        split
        · next h0 =>
          right; refine ⟨rfl, ?_⟩
          rw [hdd, hA]; simp only [List.length_append, pre_len, h0]
          simp at h0; rw [h0.1]; simp [rend_nil]
        · left; rfl
      have hb := backW_last A _ e dd he.1 he.2.1 hddA hsep
      rw [← hoA] at hb
      refine ⟨k, segs', hsegs', hk, ?_, hdd⟩
      show List.take (backW o dd (o.length - 1)) o = _
      rw [hb, hoA, List.append_assoc, List.take_left' rfl, hA]
    · split
      · next hlt hnr =>
        -- a `..` with no element to remove, not rooted: appended
        have hrt : rt = false := by simpa using hnr
        subst hrt
        simp only [Bool.false_eq_true, if_false, List.nil_append, Nat.zero_add] at ho hdd
        have hseg : segs = [] := by
          refine Classical.byContradiction fun hs => hlt ?_
          rw [ho, hdd]; exact rend_len_lt hne hs
        subst hseg
        simp only [List.append_nil] at ho
        have hrep : rend (List.replicate (k + 1) dd2) =
            (if 0 < o.length then o ++ [slash] else o) ++ [dot, dot] := by
          rw [List.replicate_succ', rend_snoc, ho]
          by_cases hk0 : k = 0
          · subst hk0; simp [rend_nil]
          · have : List.replicate k dd2 ≠ [] := by simpa using hk0
            have h0 : 0 < (rend (List.replicate k dd2)).length :=
              List.length_pos_iff.2 (fun h => this ((rend_eq_nil (by simp)).1 h))
            rw [if_pos h0, if_neg this]
        refine ⟨k + 1, [], by simp, by simp, ?_, ?_⟩
        · simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]; exact hrep.symm
        · simp only [Bool.false_eq_true, if_false, Nat.zero_add]; rw [hrep]
      · exact ⟨k, segs, hsegs, hk, ho, hdd⟩
  · next hs h1 h2 =>
    -- an element copied
    obtain ⟨k', hce, hkl, hns, hend⟩ := copyElem_shape p r
      (if (rt = true ∧ o.length ≠ 1) ∨ ((!rt) = true ∧ o.length ≠ 0) then o ++ [slash] else o)
      (by omega)
    have hc := copied_clean p r k' hr hs h1 h2 hns hend hkl
    simp only [hce]
    refine ⟨k, segs ++ [(p.drop r).take k'], ?_, hk, ?_, hdd⟩
    · intro s hs'
      simp only [List.mem_append, List.mem_singleton] at hs'
      rcases hs' with hs' | rfl
      · exact hsegs s hs'
      · exact hc
    · rw [show List.replicate k dd2 ++ (segs ++ [(p.drop r).take k']) =
          (List.replicate k dd2 ++ segs) ++ [(p.drop r).take k'] by simp, rend_snoc]
      have hsi := sep_iff hsegs ho
      by_cases h0 : List.replicate k dd2 ++ segs = []
      · rw [if_neg (fun h => (hsi.1 h) h0), if_pos h0, ho, h0]; simp [rend_nil]
      · rw [if_pos (hsi.2 h0), if_neg h0, ho]; simp

/-- **A run keeps the output's shape.** -/
theorem cleanLoopS_inv (p : List w8) (rt : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (hr : r ≤ p.length) (hI : CInv rt o dd) :
    CInv rt (cleanLoopS p rt r o dd).2.1 (cleanLoopS p rt r o dd).2.2 := by
  generalize hn : p.length - r = n
  induction n using Nat.strongRecOn generalizing r o dd with
  | _ n ih =>
    by_cases h : r < p.length
    · rw [cleanLoopS_step p rt r o dd h]
      have h1 := cleanStep_fst_gt p rt r o dd h
      have h2 := cleanStep_fst_le p rt r o dd h
      exact ih _ (by omega) _ _ _ h2 (cleanStep_inv p rt r o dd h hI) rfl
    · rw [cleanLoopS_stop p rt r o dd h]; exact hI

/-! ### Single rounds on known input -/

/-- A clean element at `pre.length` is copied, after a `/` unless the output is empty or the root. -/
theorem cleanStep_seg (pre s rest o : List w8) (rt : Bool) (dd : Nat) (hs : cleanSeg s)
    (hrest : rest = [] ∨ rest.head? = some slash) :
    cleanStep (pre ++ s ++ rest) rt pre.length o dd =
      (pre.length + s.length,
        (if (rt = true ∧ o.length ≠ 1) ∨ ((!rt) = true ∧ o.length ≠ 0) then o ++ [slash] else o) ++ s,
        dd) := by
  obtain ⟨hne, hcs', hn1, hn2⟩ := hs
  obtain ⟨c, s', rfl⟩ : ∃ c s', s = c :: s' := by
    cases s with | nil => exact absurd rfl hne | cons c s' => exact ⟨c, s', rfl⟩
  have hc : c ≠ slash := hcs' c (by simp)
  have hg : (pre ++ c :: s' ++ rest).getD pre.length 0 = c := by simp
  have hd1 : ¬ (c = dot ∧ (pre.length + 1 = (pre ++ c :: s' ++ rest).length ∨
      (pre ++ c :: s' ++ rest).getD (pre.length + 1) 0 = slash)) := by
    rintro ⟨rfl, h⟩
    cases s' with
    | nil => exact hn1 rfl
    | cons d s'' =>
      have hd : d ≠ slash := hcs' d (by simp)
      rcases h with h | h
      · simp at h
      · have e : (pre ++ dot :: d :: s'' ++ rest).getD (pre.length + 1) 0 = d := by
          rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega)]
          simp
        rw [e] at h; exact hd h
  have hd2 : ¬ (c = dot ∧ (pre ++ c :: s' ++ rest).getD (pre.length + 1) 0 = dot ∧
      (pre.length + 2 = (pre ++ c :: s' ++ rest).length ∨
        (pre ++ c :: s' ++ rest).getD (pre.length + 2) 0 = slash)) := by
    rintro ⟨rfl, h1, h⟩
    cases s' with
    | nil => exact hn1 rfl
    | cons d s'' =>
      have e1 : (pre ++ dot :: d :: s'' ++ rest).getD (pre.length + 1) 0 = d := by
        rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega)]
        simp
      rw [e1] at h1; subst h1
      cases s'' with
      | nil => exact hn2 rfl
      | cons e s3 =>
        have he : e ≠ slash := hcs' e (by simp)
        rcases h with h | h
        · simp at h
        · have e2 : (pre ++ dot :: dot :: e :: s3 ++ rest).getD (pre.length + 2) 0 = e := by
            rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega)]
            simp
          rw [e2] at h; exact he h
  have hce := copyElem_seg pre (c :: s') rest
    (if (rt = true ∧ o.length ≠ 1) ∨ ((!rt) = true ∧ o.length ≠ 0) then o ++ [slash] else o) hcs' hrest
  rw [cleanStep, if_neg (by rw [hg]; exact hc), if_neg (by rw [hg]; exact hd1),
    if_neg (by rw [hg]; intro h; exact hd2 h)]
  simp only [hce]

/-- A final `..`, not rooted, with no element to remove: appended. -/
theorem cleanStep_dd (pre o : List w8) (dd : Nat) (h : ¬ dd < o.length) :
    cleanStep (pre ++ dd2) false pre.length o dd =
      (pre.length + 2, (if 0 < o.length then o ++ [slash] else o) ++ [dot, dot],
        ((if 0 < o.length then o ++ [slash] else o) ++ [dot, dot]).length) := by
  have g0 : (pre ++ dd2).getD pre.length 0 = dot := by simp
  have g1 : (pre ++ dd2).getD (pre.length + 1) 0 = dot := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp
  have hl : (pre ++ dd2).length = pre.length + 2 := by simp
  unfold cleanStep
  simp [g0, g1, hl, h]

theorem cleanStep_slash (p : List w8) (rt : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : p.getD r 0 = slash) : cleanStep p rt r o dd = (r + 1, o, dd) := by
  rw [cleanStep, if_pos h]

/-! ### The loop over an output of the shape copies it -/

theorem rend_cons (e : List w8) (es : List (List w8)) : rend (e :: es) = e ++ segsPath es := by
  unfold rend; rw [segsPath_cons]; rfl

/-- One more element after an output the loop copies. -/
theorem shape_snoc (rt : Bool) (es : List (List w8)) (e : List w8) (D D' : Nat)
    (hne : ∀ s ∈ es, s ≠ [])
    (hIH : cleanLoopS ((if rt then [slash] else []) ++ rend es) rt (if rt then 1 else 0)
        (if rt then [slash] else []) (if rt then 1 else 0) =
      (((if rt then [slash] else []) ++ rend es).length, (if rt then [slash] else []) ++ rend es, D))
    (he : (cleanSeg e ∧ D' = D) ∨ (e = dd2 ∧ rt = false ∧ D = (rend es).length ∧
      D' = (rend (es ++ [e])).length)) :
    cleanLoopS ((if rt then [slash] else []) ++ rend (es ++ [e])) rt (if rt then 1 else 0)
        (if rt then [slash] else []) (if rt then 1 else 0) =
      (((if rt then [slash] else []) ++ rend (es ++ [e])).length,
        (if rt then [slash] else []) ++ rend (es ++ [e]), D') := by
  have hpl := pre_len rt
  generalize hpre : (if rt then [slash] else [] : List w8) = pre at hIH ⊢ hpl
  generalize hr0 : (if rt then 1 else 0) = r0 at hIH ⊢ hpl
  subst hpl
  rw [rend_snoc]
  by_cases hes : es = []
  · subst hes
    rw [if_pos rfl]
    have hD : D = pre.length := by
      rw [rend_nil, List.append_nil, cleanLoopS_stop _ _ _ _ _ (by omega)] at hIH
      simp at hIH; omega
    rcases he with ⟨hc, rfl⟩ | ⟨rfl, rfl, -, rfl⟩
    · have hst := cleanStep_seg pre e [] pre rt pre.length hc (Or.inl rfl)
      rw [List.append_nil] at hst
      have hlen : 0 < e.length := List.length_pos_iff.2 hc.1
      rw [cleanLoopS_step _ _ _ _ _ (by simp; omega), hst]
      have hsep : ¬ ((rt = true ∧ pre.length ≠ 1) ∨ ((!rt) = true ∧ pre.length ≠ 0)) := by
        subst hpre; cases rt <;> simp
      rw [if_neg hsep, cleanLoopS_stop _ _ _ _ _ (by simp), hD]
      simp
    · have hp : pre = [] := by subst hpre; rfl
      subst hp
      rw [cleanLoopS_step _ _ _ _ _ (by simp), cleanStep_dd [] [] [].length (by simp),
        cleanLoopS_stop _ _ _ _ _ (by simp)]
      simp [rend_single]
  · rw [if_neg hes]
    have hne' : rend es ≠ [] := fun h => hes ((rend_eq_nil hne).1 h)
    have hl0 : 0 < (rend es).length := List.length_pos_iff.2 hne'
    have happ := cleanLoopS_app (p := pre ++ rend es) (t := [slash] ++ e) (Or.inr rfl) rt pre.length pre pre.length
      (by simp)
    rw [hIH] at happ
    simp only at happ
    rw [show pre ++ (rend es ++ [slash] ++ e) = pre ++ rend es ++ ([slash] ++ e) by simp, happ]
    have hsl : (pre ++ rend es ++ ([slash] ++ e)).getD (pre ++ rend es).length 0 = slash := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp
    rw [cleanLoopS_step _ _ _ _ _ (by simp), cleanStep_slash _ _ _ _ _ hsl]
    simp only
    rw [show pre ++ rend es ++ ([slash] ++ e) = (pre ++ rend es ++ [slash]) ++ e ++ [] by simp,
      show (pre ++ rend es).length + 1 = (pre ++ rend es ++ [slash]).length by simp; omega]
    rcases he with ⟨hc, rfl⟩ | ⟨rfl, hrt, hD, rfl⟩
    · have hlen : 0 < e.length := List.length_pos_iff.2 hc.1
      rw [cleanLoopS_step _ _ _ _ _ (by simp; omega),
        cleanStep_seg _ e [] (pre ++ rend es) rt _ hc (Or.inl rfl)]
      have hsep : (rt = true ∧ (pre ++ rend es).length ≠ 1) ∨ ((!rt) = true ∧ (pre ++ rend es).length ≠ 0) := by
        subst hpre; cases rt <;> simp <;> omega
      rw [if_pos hsep, cleanLoopS_stop _ _ _ _ _ (by simp; omega)]
      simp; omega
    · subst hrt
      have hp : pre = [] := by subst hpre; rfl
      subst hp
      rw [List.append_nil]
      rw [cleanLoopS_step _ _ _ _ _ (by simp),
        cleanStep_dd ([] ++ rend es ++ [slash]) ([] ++ rend es) D (by simp; omega)]
      rw [cleanLoopS_stop _ _ _ _ _ (by simp)]
      simp only [List.nil_append, if_pos hl0]
      simp [rend_snoc, hes]

/-- **The loop over an output of the shape copies it**, ending at the shape's `dotdot`. -/
theorem cleanLoopS_shape (rt : Bool) (k : Nat) (segs : List (List w8))
    (hsegs : ∀ s ∈ segs, cleanSeg s) (hk : rt = true → k = 0) :
    cleanLoopS ((if rt then [slash] else []) ++ rend (List.replicate k dd2 ++ segs)) rt
        (if rt then 1 else 0) (if rt then [slash] else []) (if rt then 1 else 0) =
      (((if rt then [slash] else []) ++ rend (List.replicate k dd2 ++ segs)).length,
        (if rt then [slash] else []) ++ rend (List.replicate k dd2 ++ segs),
        (if rt then 1 else 0) + (rend (List.replicate k dd2)).length) := by
  suffices H : ∀ l : List (List w8), (∀ s ∈ l.reverse, cleanSeg s) →
      cleanLoopS ((if rt then [slash] else []) ++ rend (List.replicate k dd2 ++ l.reverse)) rt
        (if rt then 1 else 0) (if rt then [slash] else []) (if rt then 1 else 0) =
      (((if rt then [slash] else []) ++ rend (List.replicate k dd2 ++ l.reverse)).length,
        (if rt then [slash] else []) ++ rend (List.replicate k dd2 ++ l.reverse),
        (if rt then 1 else 0) + (rend (List.replicate k dd2)).length) by
    simpa using H segs.reverse (by simpa using hsegs)
  intro l
  induction l with
  | nil =>
    intro _
    simp only [List.reverse_nil, List.append_nil]
    induction k with
    | zero =>
      simp only [List.replicate_zero, rend_nil, List.append_nil, Nat.add_zero]
      rw [cleanLoopS_stop _ _ _ _ _ (by rw [pre_len]; omega), pre_len]
      simp
    | succ k ih =>
      have hrt : rt = false := by
        cases rt
        · rfl
        · exact absurd (hk rfl) (by omega)
      subst hrt
      have := shape_snoc false (List.replicate k dd2) dd2 (rend (List.replicate k dd2)).length
        (rend (List.replicate (k + 1) dd2)).length (by simp) (by simpa using ih (fun h => nomatch h))
        (Or.inr ⟨rfl, rfl, rfl, by rw [List.replicate_succ']⟩)
      rw [← List.replicate_succ'] at this
      simpa using this
  | cons e l ih =>
    intro hl
    simp only [List.reverse_cons] at hl ⊢
    have hs : ∀ s ∈ l.reverse, cleanSeg s := fun s hs => hl s (by simp at hs ⊢; simp [hs])
    have he : cleanSeg e := hl e (by simp)
    have := shape_snoc rt (List.replicate k dd2 ++ l.reverse) e _ _ (shape_ne hs) (ih hs)
      (Or.inl ⟨he, rfl⟩)
    simpa using this

/-! ### `Clean` of its output; `Clean` of one more element -/

theorem lit_dot : (go!"." : List w8) = [dot] := by decide

/-- The output of a run over a non-empty `p`: its shape. -/
theorem cleanModel_out (p : List w8) (hp : p ≠ []) (rt : Bool) :
    ∃ dd, CInv rt (cleanLoop p rt (if rt then 1 else 0) (if rt then [slash] else [])
      (if rt then 1 else 0)) dd := by
  have h0 : 0 < p.length := List.length_pos_iff.2 hp
  rw [cleanLoop_eq_S]
  exact ⟨_, cleanLoopS_inv _ _ _ _ _ (by split <;> omega) (CInv_init _)⟩

theorem CInv_getD0 {rt : Bool} {o : List w8} {dd : Nat} (h : CInv rt o dd) (ho : o ≠ []) :
    decide (o.getD 0 0 = slash) = rt := by
  obtain ⟨k, segs, hsegs, hk, rfl, -⟩ := h
  cases rt
  · simp only [Bool.false_eq_true, if_false, List.nil_append] at ho ⊢
    have hne : List.replicate k dd2 ++ segs ≠ [] := fun h => ho (by rw [h]; rfl)
    obtain ⟨e, es, he⟩ : ∃ e es, List.replicate k dd2 ++ segs = e :: es := by
      cases h : List.replicate k dd2 ++ segs with
      | nil => exact absurd h hne
      | cons e es => exact ⟨e, es, rfl⟩
    have hem : e ∈ List.replicate k dd2 ++ segs := by rw [he]; simp
    rw [he, rend_cons]
    simp only [List.mem_append, List.mem_replicate] at hem
    rcases hem with ⟨-, rfl⟩ | hem
    · simp
    · obtain ⟨hne, hns, -, -⟩ := hsegs e hem
      obtain ⟨c, e', rfl⟩ : ∃ c e', e = c :: e' := by
        cases e with | nil => exact absurd rfl hne | cons c e' => exact ⟨c, e', rfl⟩
      simpa using hns c (by simp)
  · simp

/-- **`Clean` of an output of the shape** is the output. -/
theorem cleanModel_of_CInv {rt : Bool} {o : List w8} {dd : Nat} (h : CInv rt o dd) (ho : o ≠ []) :
    cleanModel o = o := by
  have hrt := CInv_getD0 h ho
  obtain ⟨k, segs, hsegs, hk, hoe, -⟩ := h
  have hsh := cleanLoopS_shape rt k segs hsegs hk
  rw [← hoe] at hsh
  unfold cleanModel
  rw [if_neg ho]
  simp only
  rw [hrt, cleanLoop_eq_S, hsh]
  simp only
  rw [if_neg ho]

/-- **`Clean(Clean(p)) = Clean(p)`.** -/
theorem cleanModel_idem (p : List w8) : cleanModel (cleanModel p) = cleanModel p := by
  by_cases hp : p = []
  · subst hp; decide
  obtain ⟨dd, hI⟩ := cleanModel_out p hp (decide (p.getD 0 0 = slash))
  generalize hO : cleanLoop p (decide (p.getD 0 0 = slash)) _ _ _ = O at hI
  have hc : cleanModel p = if O = [] then go!"." else O := by
    rw [← hO]; unfold cleanModel; rw [if_neg hp]
  rw [hc]
  split
  · decide
  · next ho => exact cleanModel_of_CInv hI ho

/-- `c ⊕ s`: the element `s` after the cleaned path `c` (`.` gives `s`, the root `/s`). -/
def appSeg (c s : List w8) : List w8 :=
  if c = [dot] then s else if c = [slash] then slash :: s else c ++ [slash] ++ s

theorem CInv_ne_dot {rt : Bool} {o : List w8} {dd : Nat} (h : CInv rt o dd) : o ≠ [dot] := by
  obtain ⟨k, segs, hsegs, hk, rfl, -⟩ := h
  intro he
  cases rt
  · simp only [Bool.false_eq_true, if_false, List.nil_append] at he
    cases hes : List.replicate k dd2 ++ segs with
    | nil => rw [hes, rend_nil] at he; exact absurd he (by simp)
    | cons e es =>
      have hem : e ∈ List.replicate k dd2 ++ segs := by rw [hes]; simp
      rw [hes, rend_cons] at he
      cases es with
      | nil =>
        simp [segsPath] at he
        subst he
        simp only [List.mem_append, List.mem_replicate] at hem
        rcases hem with ⟨-, h⟩ | hem
        · exact absurd h (by decide)
        · exact (hsegs _ hem).2.2.1 rfl
      | cons f fs =>
        rw [segsPath_cons] at he
        have := congrArg List.length he
        have hen := List.length_pos_iff.2 (shape_ne hsegs e hem)
        simp only [List.length_append, List.length_cons, List.length_singleton] at this
        omega
  · simp at he

/-- The separator rule of a copy, in terms of the cleaned path. -/
theorem sep_appSeg {rt : Bool} {o : List w8} {dd : Nat} (h : CInv rt o dd) (s : List w8) :
    (if (rt = true ∧ o.length ≠ 1) ∨ ((!rt) = true ∧ o.length ≠ 0) then o ++ [slash] else o) ++ s =
      appSeg (if o = [] then go!"." else o) s := by
  have hnd := CInv_ne_dot h
  obtain ⟨k, segs, hsegs, hk, ho, hdd⟩ := h
  have hsi := sep_iff hsegs ho
  have hn := rend_eq_nil (shape_ne (k := k) hsegs)
  unfold appSeg
  by_cases h0 : List.replicate k dd2 ++ segs = []
  · rw [if_neg (fun h => (hsi.1 h) h0)]
    rw [h0, rend_nil, List.append_nil] at ho
    subst ho
    cases rt <;> simp [lit_dot]
  · rw [if_pos (hsi.2 h0)]
    have hr : rend (List.replicate k dd2 ++ segs) ≠ [] := fun h => h0 (hn.1 h)
    have hl : 0 < (rend (List.replicate k dd2 ++ segs)).length := List.length_pos_iff.2 hr
    have hone : o ≠ [] := by rw [ho]; simpa using fun _ => hr
    rw [if_neg hone, if_neg hnd]
    have hsl : o ≠ [slash] := by
      intro he
      cases rt
      · have := CInv_getD0 ⟨k, segs, hsegs, hk, ho, hdd⟩ hone
        rw [he] at this; simp at this
      · rw [ho] at he; simp at he; exact hr he
    rw [if_neg hsl]

/-- **`Clean(p + "/" + s) = Clean(p) ⊕ s`** for a non-empty `p` and a plain element `s`. -/
theorem cleanModel_snoc (p s : List w8) (hp : p ≠ []) (hs : plainSeg s) :
    cleanModel (p ++ [slash] ++ s) = appSeg (cleanModel p) s := by
  have h0 : 0 < p.length := List.length_pos_iff.2 hp
  have hcs := hs.toClean
  have hsl : 0 < s.length := List.length_pos_iff.2 hs.1
  obtain ⟨dd, hI⟩ := cleanModel_out p hp (decide (p.getD 0 0 = slash))
  have hg : (p ++ [slash] ++ s).getD 0 0 = p.getD 0 0 := by
    rw [List.append_assoc]; exact getD_app_lt h0
  generalize hrt : decide (p.getD 0 0 = slash) = rt at hI
  have hne : p ++ [slash] ++ s ≠ [] := by simp [hp]
  unfold cleanModel
  rw [if_neg hne, if_neg hp]
  simp only
  rw [hg, hrt, cleanLoop_eq_S, cleanLoop_eq_S]
  rw [cleanLoop_eq_S] at hI
  have happ := cleanLoopS_app (p := p) (t := [slash] ++ s) (Or.inr rfl) rt (if rt then 1 else 0)
    (if rt then [slash] else []) (if rt then 1 else 0) (by split <;> omega)
  rw [List.append_assoc, happ]
  generalize cleanLoopS p rt (if rt then 1 else 0) (if rt then [slash] else []) (if rt then 1 else 0) = st at hI ⊢
  obtain ⟨r1, o, d⟩ := st
  simp only at hI ⊢
  have hsl' : (p ++ ([slash] ++ s)).getD p.length 0 = slash := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp
  rw [cleanLoopS_step _ _ _ _ _ (by simp), cleanStep_slash _ _ _ _ _ hsl']
  simp only
  rw [show p ++ ([slash] ++ s) = (p ++ [slash]) ++ s ++ [] by simp,
    show p.length + 1 = (p ++ [slash]).length by simp]
  rw [cleanLoopS_step _ _ _ _ _ (by simp; omega), cleanStep_seg _ s [] o rt d hcs (Or.inl rfl),
    cleanLoopS_stop _ _ _ _ _ (by simp; omega)]
  simp only
  rw [if_neg (by simp [hs.1])]
  exact sep_appSeg hI s

/-! ### `Join` of two elements -/

theorem cleanModel_plain (s : List w8) (hs : plainSeg s) : cleanModel s = s :=
  cleanModel_of_CInv (rt := false) (dd := 0)
    ⟨0, [s], by simpa using hs.toClean, nofun, by simp [rend_single], by simp [rend_nil]⟩ hs.1

/-- **`Join(x, s)` of a plain element `s`** is `Clean(x) ⊕ s`. -/
theorem joinModel_pair (x s : List w8) (hs : plainSeg s) :
    joinModel [x, s] = appSeg (cleanModel x) s := by
  have hsl : 0 < s.length := List.length_pos_iff.2 hs.1
  unfold joinModel
  rw [if_neg (by simp [hs.1])]
  by_cases hx : x = []
  · subst hx
    simp [joinBuf, hs.1, cleanModel_plain s hs]
    unfold appSeg cleanModel; simp [lit_dot]
  · have hxl : 0 < x.length := List.length_pos_iff.2 hx
    have : joinBuf [x, s] [] = x ++ [slash] ++ s := by simp [joinBuf, hx, hxl]
    rw [this, cleanModel_snoc x s hx hs]

/-- `Clean(x) ⊕ s` is clean. -/
theorem cleanModel_appSeg (x s : List w8) (hs : plainSeg s) :
    cleanModel (appSeg (cleanModel x) s) = appSeg (cleanModel x) s := by
  rw [← joinModel_pair x s hs]
  unfold joinModel
  rw [if_neg (by simp [hs.1]), cleanModel_idem]

/-! ### `Clean` lengthens nothing -/

/-- A copy needs a separator. -/
def sepN (rt : Bool) (o : List w8) : Prop := (rt = true ∧ o.length ≠ 1) ∨ ((!rt) = true ∧ o.length ≠ 0)

/-- The length invariant: the output no longer than what was read, and shorter before an element
after a `/` that gets a separator (the `/` pays for it). -/
def LInv (p : List w8) (rt : Bool) (r : Nat) (o : List w8) : Prop :=
  (if rt then 1 else 0) ≤ r ∧ o.length ≤ r ∧ (r = (if rt then 1 else 0) → ¬ sepN rt o) ∧
    (0 < r → p.getD (r - 1) 0 = slash → sepN rt o → o.length < r) ∧
    (r < p.length → p.getD r 0 ≠ slash → r = (if rt then 1 else 0) ∨ (0 < r ∧ p.getD (r - 1) 0 = slash))

theorem cleanStep_len (p : List w8) (rt : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (hr : r < p.length) (hL : LInv p rt r o) :
    LInv p rt (cleanStep p rt r o dd).1 (cleanStep p rt r o dd).2.1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hL
  unfold cleanStep
  split
  · next hs =>
    refine ⟨by omega, by simp; omega, fun h => by simp at h; omega, fun _ _ _ => by simp; omega, ?_⟩
    intro _ _; right; simpa using hs
  split
  · next hs hd =>
    refine ⟨by simp; omega, by simp; omega, fun h => by simp at h; omega, ?_, ?_⟩
    · intro _ h; rw [show r + 1 - 1 = r by omega] at h; exact absurd (hd.1.symm.trans h) (by decide)
    · intro hl h; simp at hl h
      rcases hd.2 with h' | h'
      · omega
      · exact absurd h' h
  split
  · next hs hd1 hd2 =>
    have hdot1 : p.getD (r + 2 - 1) 0 ≠ slash := by
      rw [show r + 2 - 1 = r + 1 by omega, hd2.2.1]; decide
    have hend : ∀ (hl : r + 2 < p.length), p.getD (r + 2) 0 ≠ slash → False := by
      intro hl h; rcases hd2.2.2 with h' | h'
      · omega
      · exact h h'
    split
    · refine ⟨by simp; omega, ?_, fun h => by simp at h; omega, fun _ h => absurd h hdot1, ?_⟩
      · simp only [List.length_take]; omega
      · intro hl h; exact absurd (hend hl h) id
    split
    · next hlt hnr =>
      refine ⟨by simp; omega, ?_, fun h => by simp at h; omega, fun _ h => absurd h hdot1, ?_⟩
      · by_cases ho : o = []
        · subst ho; simp
        · have hsep : sepN rt o := Or.inr ⟨hnr, by simpa using ho⟩
          have hlt' : o.length < r := by
            rcases h4 hr hs with h' | ⟨h'1, h'2⟩
            · exact absurd h' (h2 · hsep)
            · exact h3 h'1 h'2 hsep
          have : 0 < o.length := List.length_pos_iff.2 ho
          simp [this]; omega
      · intro hl h; exact absurd (hend hl h) id
    · refine ⟨by simp; omega, by simp; omega, fun h => by simp at h; omega, fun _ h => absurd h hdot1, ?_⟩
      intro hl h; exact absurd (hend hl h) id
  · next hs hd1 hd2 =>
    obtain ⟨k', hce, hkl, hns, hend⟩ := copyElem_shape p r
      (if (rt = true ∧ o.length ≠ 1) ∨ ((!rt) = true ∧ o.length ≠ 0) then o ++ [slash] else o)
      (by omega)
    have hc := copied_clean p r k' hr hs hd1 hd2 hns hend hkl
    have hk1 : 0 < k' := by
      have := List.length_pos_iff.2 hc.1; simp at this; omega
    simp only [hce]
    have hlast : p.getD (r + k' - 1) 0 ≠ slash := by
      have hg : ((p.drop r).take k')[k' - 1]? = some (p.getD (r + k' - 1) 0) := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, show r + (k' - 1) = r + k' - 1 by omega,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h := by omega)]
        rfl
      exact hns _ (List.mem_of_getElem? hg)
    refine ⟨by omega, ?_, fun h => by omega, fun _ h => absurd h hlast, ?_⟩
    · simp only [List.length_append, List.length_take, List.length_drop]
      split
      · next hsep =>
        have hlt' : o.length < r := by
          rcases h4 hr hs with h' | ⟨h'1, h'2⟩
          · exact absurd h' (h2 · hsep)
          · exact h3 h'1 h'2 hsep
        simp; omega
      · omega
    · intro hl h
      rcases hend with h' | h'
      · omega
      · exact absurd h' h

theorem cleanLoopS_len (p : List w8) (rt : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (hr : r ≤ p.length) (hL : LInv p rt r o) :
    (cleanLoopS p rt r o dd).2.1.length ≤ p.length := by
  generalize hn : p.length - r = n
  induction n using Nat.strongRecOn generalizing r o dd with
  | _ n ih =>
    by_cases h : r < p.length
    · rw [cleanLoopS_step p rt r o dd h]
      have h1 := cleanStep_fst_gt p rt r o dd h
      have h2 := cleanStep_fst_le p rt r o dd h
      exact ih _ (by omega) _ _ _ h2 (cleanStep_len p rt r o dd h hL) rfl
    · rw [cleanLoopS_stop p rt r o dd h]; exact Nat.le_trans hL.2.1 hr

/-- **`Clean(p)` of a non-empty `p` is no longer than `p`.** -/
theorem cleanModel_length_le (p : List w8) (hp : p ≠ []) : (cleanModel p).length ≤ p.length := by
  have h0 : 0 < p.length := List.length_pos_iff.2 hp
  unfold cleanModel
  rw [if_neg hp]
  simp only
  generalize decide (p.getD 0 0 = slash) = rt
  rw [cleanLoop_eq_S]
  have hL := cleanLoopS_len p rt (if rt then 1 else 0) (if rt then [slash] else []) (if rt then 1 else 0)
    (by split <;> omega)
    ⟨Nat.le_refl _, by split <;> simp, fun _ => by cases rt <;> simp [sepN],
      fun h _ hsep => by cases rt <;> simp [sepN] at h hsep, fun _ _ => Or.inl rfl⟩
  generalize (cleanLoopS p rt (if rt then 1 else 0) (if rt then [slash] else [])
    (if rt then 1 else 0)).2.1 = O at hL ⊢
  split
  · simp [lit_dot]; omega
  · exact hL

theorem appSeg_length_le (c s : List w8) : (appSeg c s).length ≤ c.length + 1 + s.length := by
  unfold appSeg; split
  · omega
  split <;> simp <;> omega

/-- `Join(x, s)` is at most one byte longer than `x` and `s` (`.` for an empty `x`). -/
theorem joinModel_pair_length (x s : List w8) (hs : plainSeg s) :
    (joinModel [x, s]).length ≤ x.length + 2 + s.length := by
  rw [joinModel_pair x s hs]
  have h1 := appSeg_length_le (cleanModel x) s
  by_cases hx : x = []
  · subst hx; have : (cleanModel []).length = 1 := by decide
    omega
  · have := cleanModel_length_le x hx; omega

/-! ### `Join` in steps -/

theorem appSeg_length_ge (c s : List w8) : s.length ≤ (appSeg c s).length := by
  unfold appSeg; split
  · omega
  split <;> simp <;> omega

/-- `Join` of elements not all empty is clean. -/
theorem cleanModel_joinModel (es : List (List w8)) (h : (es.map List.length).sum ≠ 0) :
    cleanModel (joinModel es) = joinModel es := by
  unfold joinModel; rw [if_neg h, cleanModel_idem]

/-- **`Join(Join(d, a), b) = Join(d, a, b)`** for plain `a`, `b`. -/
theorem joinModel_triple (d a b : List w8) (ha : plainSeg a) (hb : plainSeg b) :
    joinModel [joinModel [d, a], b] = joinModel [d, a, b] := by
  have hal : 0 < a.length := List.length_pos_iff.2 ha.1
  rw [joinModel_pair _ b hb, cleanModel_joinModel _ (by simp [ha.1]), joinModel_pair d a ha]
  unfold joinModel
  rw [if_neg (by simp [ha.1])]
  by_cases hd : d = []
  · subst hd
    have : joinBuf [[], a, b] [] = a ++ [slash] ++ b := by simp [joinBuf, ha.1, hal]
    rw [this, cleanModel_snoc a b ha.1 hb, cleanModel_plain a ha]
    congr 1
  · have hdl : 0 < d.length := List.length_pos_iff.2 hd
    have : joinBuf [d, a, b] [] = (d ++ [slash] ++ a) ++ [slash] ++ b := by
      simp [joinBuf, hd, hdl, hb.1, show 0 < d.length + (a.length + 1) by omega]
    rw [this, cleanModel_snoc _ b (by simp) hb, cleanModel_snoc d a hd ha]

/-- **`Join(Join(d, a, b), c) = Join(d, a, b) + "/" + c`** for plain `a`, `b`, `c`: the path ends in the
element `b`, neither `.` nor the root. -/
theorem joinModel_triple_snoc (d a b c : List w8) (ha : plainSeg a) (hb : plainSeg b)
    (hc : plainSeg c) (hb2 : 2 ≤ b.length) :
    joinModel [joinModel [d, a, b], c] = joinModel [d, a, b] ++ [slash] ++ c := by
  rw [joinModel_pair _ c hc, cleanModel_joinModel _ (by simp [ha.1])]
  have hl : b.length ≤ (joinModel [d, a, b]).length := by
    rw [← joinModel_triple d a b ha hb, joinModel_pair _ b hb]; exact appSeg_length_ge _ _
  unfold appSeg
  rw [if_neg (by intro h; rw [h] at hl; simp at hl; omega),
    if_neg (by intro h; rw [h] at hl; simp at hl; omega)]

/-- `Join(d, a, b)` is at most a few bytes longer than its elements. -/
theorem joinModel_triple_length (d a b : List w8) (ha : plainSeg a) (hb : plainSeg b) :
    (joinModel [d, a, b]).length ≤ d.length + a.length + b.length + 4 := by
  rw [← joinModel_triple d a b ha hb]
  have h1 := joinModel_pair_length (joinModel [d, a]) b hb
  have h2 := joinModel_pair_length d a ha
  omega

end path
end EtcdGrove
end Perennial
