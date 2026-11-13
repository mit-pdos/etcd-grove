/-
U6 (`notes/bbolt-proof-plan.md`): `rStackAt_prev` (`Model/Cursor`), corrected and proved as
`rStackAt_prev'`. The shared statement is false, as `rStackAt_next` was (U6's findings, item 1):
its `sLast` on the dropped stacks `els'.drop j` computes the new leaf's bounds from the dropped
path alone (`(none, none)` at the leaf: it demands the new leaf index be `es.length - 1`), and
`sPred` says nothing of the old stack below the moving depth `d`. Counterexample: a root branch
over leaves `L0 = {a, b}`, `L1 = {c, d}`; the old stack `[root 1, L1 1]` is at position 3; the new
`[root 0, L0 3]` satisfies `sPred` (at `d = 0`), and is at position 3, not 2. (`prev`'s real move,
`[root 0, L0 1]`, at position 2, does not satisfy it; and from `[root 1, L1 1]` `prev` moves at
the leaf, not at the root: a move at `d` with the old stack not first below `d` is off by the old
leaf index.) The corrected
premises are `prev`'s move literally (`sPrev`: `els' = els.take d ++ e' :: R'`, `e'` one before
`els[d]`, `R'` last over the whole new path) and what its upward loop found (`sStartBelow`: the
old indices below `d` are `0`, the old leaf index at most its leaf's entries), with
`hlen : d + 1 < els.length ↔ d + 1 < els'.length` (`c.last()` descends iff `d` is a branch).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Cursor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Prev

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section prev
variable [GooseExts]

/-! ## Helpers (`Model/Cursor`'s private ones, copied) -/

theorem len_filter_sum (es : List BoltEnt) (f g h : BoltEnt → Bool)
    (hpt : ∀ e ∈ es, (if f e then 1 else 0) + (if g e then 1 else 0) = (if h e then 1 else 0)) :
    (es.filter f).length + (es.filter g).length = (es.filter h).length := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    have ha := hpt a (List.mem_cons_self ..)
    have ht := ih (fun e he => hpt e (List.mem_cons_of_mem _ he))
    simp only [List.filter_cons]
    split <;> split <;> split <;> simp_all <;> omega

theorem keyGe_lt {lo : Option (List w8)} {e k : List w8} (hk : keyGe lo k)
    (he : ¬ keyGe lo e) : go.GoStringLt e k := by
  cases lo with
  | none => exact absurd (fun _ h => nomatch h) he
  | some l =>
  have hel : go.GoStringLt e l := Classical.byContradiction fun h => he (fun l' hl => by
    cases hl; exact h)
  have := hk l rfl
  rcases Classical.em (go.GoStringLt l k) with h | h
  · exact go.goStringLt_trans hel h
  · rw [go.goStringLt_eq_of_not_lt this h]; exact hel

theorem pathBndFrom_first (v : View) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    (∀ e ∈ els, e.index'.toNat = 0) → (pathBndFrom v b pids els).1 = b.1
  | e :: e' :: es, pid :: pid' :: ps, b, hf => by
    simp only [pathBndFrom]
    rw [pathBndFrom_first v (e' :: es) (pid' :: ps) _ (fun x hx => hf x (List.mem_cons_of_mem _ hx))]
    simp [entryBnd, childLo, hf e (List.mem_cons_self ..)]
  | [], _, _, _ => by cases ‹List Nat› <;> simp [pathBndFrom]
  | [_], [], _, _ => by simp [pathBndFrom]
  | [_], [_], _, _ => by simp [pathBndFrom]
  | [e], _ :: _ :: _, _, hf => by simp [pathBndFrom, entryBnd, childLo, hf e (by simp)]
  | _ :: _ :: _, [], _, _ => by simp [pathBndFrom]
  | _ :: _ :: _, [_], _, _ => by simp [pathBndFrom]

theorem pathBndFrom_last (v : View) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    pids.length = els.length →
    (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
      e.index'.toNat + 1 = (pidKeys v pid).length) → (pathBndFrom v b pids els).2 = b.2
  | e :: e' :: es, pid :: pid' :: ps, b, hl, hr => by
    simp only [pathBndFrom]
    rw [pathBndFrom_last v (e' :: es) (pid' :: ps) _ (by simpa using hl)
      (fun j p x hp hx hj => hr (j + 1) p x (by simpa using hp) (by simpa using hx)
        (by simp at hj ⊢; omega))]
    have := hr 0 pid e rfl rfl (by simp)
    simp [entryBnd, childHi, this]
  | [], _, _, _, _ => by cases ‹List Nat› <;> simp [pathBndFrom]
  | [_], [], _, _, _ => by simp [pathBndFrom]
  | [_], [_], _, _, _ => by simp [pathBndFrom]
  | [_], _ :: _ :: _, _, hl, _ => by simp at hl
  | _ :: _ :: _, [], _, _, _ => by simp [pathBndFrom]
  | _ :: _ :: _, [_], _, _, _ => by simp [pathBndFrom]


theorem pathBndFrom_cons (v : View) (b : Option (List w8) × Option (List w8)) (p : Nat)
    (xs : List Nat) (e : elemRef) (es : List elemRef) (hx : xs ≠ []) :
    pathBndFrom v b (p :: xs) (e :: es) =
      pathBndFrom v (entryBnd b (pidKeys v p) e.index'.toNat) xs es := by
  cases xs with
  | nil => exact absurd rfl hx
  | cons x xs => simp [pathBndFrom]

/-- The bounds of a path, split after a prefix: the prefix's bounds, then the rest's. -/
theorem pathBndFrom_append (v : View) :
    ∀ (E : List elemRef) (P : List Nat) (b : Option (List w8) × Option (List w8))
      (x0 : Nat) (X : List Nat) (Y : List elemRef), P.length = E.length →
    pathBndFrom v b (P ++ x0 :: X) (E ++ Y) =
      pathBndFrom v (pathBndFrom v b (P ++ [x0]) E) (x0 :: X) Y
  | [], [], b, x0, X, Y, _ => by simp [pathBndFrom]
  | e :: E, p :: P, b, x0, X, Y, hl => by
    simp only [List.cons_append]
    rw [pathBndFrom_cons v b p _ e _ (by simp), pathBndFrom_cons v b p _ e _ (by simp)]
    exact pathBndFrom_append v E P _ x0 X Y (by simpa using hl)
  | [], _ :: _, _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, _, hl => by simp at hl

theorem leafIdx_append (E R : List elemRef) (hR : R ≠ []) : leafIdx (E ++ R) = leafIdx R := by
  unfold leafIdx; rw [List.getLast?_append]
  cases h : R.getLast? with
  | none => simp at h; exact absurd h hR
  | some x => simp


theorem split_at {α : Type} (l : List α) (d : Nat) (h : d < l.length) :
    ∃ P x Q, l = P ++ x :: Q ∧ P.length = d ∧ l[d]? = some x := by
  refine ⟨l.take d, l[d], l.drop (d + 1), ?_, by simp; omega, by simp [h]⟩
  rw [← List.drop_eq_getElem_cons h, List.take_append_drop]

theorem pidKeys_length (v : View) (pid : Nat) (pg : List w8)
    (h : v.pages !! pid = some pg) : (pidKeys v pid).length = pageCount pg := by
  simp [pidKeys, h]


theorem len_filter_disj (es : List BoltEnt) (f g : BoltEnt → Bool)
    (h : ∀ e ∈ es, ¬ (f e = true ∧ g e = true)) :
    (es.filter f).length + (es.filter g).length ≤ es.length := by
  induction es with
  | nil => simp
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [List.filter_cons]
    cases hf : f a <;> cases hg : g a <;> simp_all <;> omega

/-! ## `prev`'s move -/

/-- **`prev`'s move at depth `d`** (`Cursor.prev`: `elem.index--` at `d`, then `c.last()`): `els'`
keeps `els` above `d`, is one before at `d`, and last below (its branch indices the last, its leaf
index its leaf's last entry, over the whole new path's bounds). -/
def sPrev (v : View) (es : List BoltEnt) (pids' : List Nat) (d : Nat) (els els' : List elemRef) :
    Prop :=
  ∃ e e' R', els[d]? = some e ∧ els' = els.take d ++ e' :: R' ∧
    e'.index'.toNat + 1 = e.index'.toNat ∧
    (∀ j pid x, pids'[j]? = some pid → els'[j]? = some x → d < j → j + 1 < els'.length →
      x.index'.toNat + 1 = (pidKeys v pid).length) ∧
    (d + 1 < els'.length → leafIdx els' + 1 = (entsIn es (pathBnd v pids' els')).length)

/-- **The old stack is at the start below `d`** (what `prev`'s upward loop found: every level
below `d` at index `0`), its leaf index at most its leaf's entries. -/
def sStartBelow (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (d : Nat) :
    Prop :=
  (∀ j x, els[j]? = some x → d < j → x.index'.toNat = 0) ∧
  leafIdx els ≤ (entsIn es (pathBnd v pids els)).length

open Classical in
/-- A position is within the entries when its leaf index is within its leaf's. -/
theorem stackPos_le (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (h : leafIdx els ≤ (entsIn es (pathBnd v pids els)).length) :
    stackPos v es pids els ≤ es.length := by
  unfold stackPos
  have := len_filter_disj es (fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1))
    (fun e => decide (keyIn (pathBnd v pids els).1 (pathBnd v pids els).2 e.1))
    (by intro e _ ⟨h1, h2⟩; simp only [decide_eq_true_eq] at h1 h2; exact h1 h2.1)
  unfold entsIn at h
  omega

/-- **`prev`'s position at the leaf**: the leaf index one before. -/
theorem stackPos_pred_leaf (v : View) (es : List BoltEnt) (P : List Nat) (E : List elemRef)
    (p : Nat) (e e' : elemRef) (hPE : P.length = E.length)
    (hidx : e'.index'.toNat + 1 = e.index'.toNat) :
    stackPos v es (P ++ [p]) (E ++ [e']) + 1 = stackPos v es (P ++ [p]) (E ++ [e]) := by
  have h : ∀ x, pathBnd v (P ++ [p]) (E ++ [x]) = pathBndFrom v (none, none) (P ++ [p]) E := by
    intro x; unfold pathBnd
    rw [pathBndFrom_append v E P _ p [] [x] hPE]; simp [pathBndFrom]
  unfold stackPos
  rw [h, h, leafIdx_append _ _ (by simp), leafIdx_append _ _ (by simp)]
  simp [leafIdx, ← hidx]; omega

open Classical in
/-- **`prev`'s position, one level up** (`d` above the leaf): the old stack first below `d`, the
new one one before at `d` and last below: the new position is one before the old. -/
theorem stackPos_pred_up (v : View) (es : List BoltEnt) (P : List Nat) (E : List elemRef)
    (p : Nat) (Q Q' : List Nat) (e e' : elemRef) (R R' : List elemRef)
    (hPE : P.length = E.length) (hQR : Q.length = R.length) (hQR' : Q'.length = R'.length)
    (hR : R ≠ []) (hR' : R' ≠ [])
    (hidx : e'.index'.toNat + 1 = e.index'.toNat)
    (hlt : e.index'.toNat < (pidKeys v p).length)
    (hfirst : ∀ x ∈ R, x.index'.toNat = 0)
    (hlast : ∀ j pid x, Q'[j]? = some pid → R'[j]? = some x → j + 1 < R'.length →
      x.index'.toNat + 1 = (pidKeys v pid).length)
    (hleaf : leafIdx (E ++ e' :: R') + 1 =
      (entsIn es (pathBnd v (P ++ p :: Q') (E ++ e' :: R'))).length) :
    stackPos v es (P ++ p :: Q') (E ++ e' :: R') + 1 = stackPos v es (P ++ p :: Q) (E ++ e :: R) := by
  obtain ⟨q0, Q0, rfl⟩ : ∃ q0 Q0, Q = q0 :: Q0 := by
    cases Q with
    | nil => cases R with | nil => exact absurd rfl hR | cons _ _ => simp at hQR
    | cons q0 Q0 => exact ⟨q0, Q0, rfl⟩
  obtain ⟨q0', Q0', rfl⟩ : ∃ q0 Q0, Q' = q0 :: Q0 := by
    cases Q' with
    | nil => cases R' with | nil => exact absurd rfl hR' | cons _ _ => simp at hQR'
    | cons q0 Q0 => exact ⟨q0, Q0, rfl⟩
  have hold : pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R) =
      pathBndFrom v (entryBnd (pathBndFrom v (none, none) (P ++ [p]) E) (pidKeys v p)
        e.index'.toNat) (q0 :: Q0) R := by
    unfold pathBnd
    rw [pathBndFrom_append v E P _ p _ _ hPE, pathBndFrom_cons v _ p _ e _ (by simp)]
  have hnew : pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R') =
      pathBndFrom v (entryBnd (pathBndFrom v (none, none) (P ++ [p]) E) (pidKeys v p)
        e'.index'.toNat) (q0' :: Q0') R' := by
    unfold pathBnd
    rw [pathBndFrom_append v E P _ p _ _ hPE, pathBndFrom_cons v _ p _ e' _ (by simp)]
  have hlo : (pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R)).1 =
      some ((pidKeys v p).getD e.index'.toNat []) := by
    rw [hold, pathBndFrom_first v R (q0 :: Q0) _ hfirst]
    simp only [entryBnd, childLo]
    rw [if_neg (by omega)]
  have hhi : (pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R')).2 =
      some ((pidKeys v p).getD e.index'.toNat []) := by
    rw [hnew, pathBndFrom_last v R' (q0' :: Q0') _ hQR' hlast]
    simp only [entryBnd, childHi]
    rw [if_pos (by omega), hidx]
  have hli : leafIdx (E ++ e :: R) = 0 := by
    rw [show E ++ e :: R = (E ++ [e]) ++ R by simp, leafIdx_append _ _ hR]
    unfold leafIdx
    cases h : R.getLast? with
    | none => rfl
    | some x => simp [hfirst x (List.mem_of_getLast? h)]
  unfold stackPos
  rw [hli, hlo]
  generalize hK : (pidKeys v p).getD e.index'.toNat [] = K at hhi hlo
  generalize hlo' : (pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R')).1 = lo
  have hb : pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R') = (lo, some K) := by
    rw [← hhi, ← hlo']
  rw [hb] at hleaf
  unfold entsIn at hleaf
  simp only at hleaf ⊢
  -- the new leaf is not empty, so its lower bound is below `K`
  have hlK : keyGe lo K := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ es.filter (fun e => decide (keyIn lo (some K) e.1)) :=
      List.exists_mem_of_length_pos (by omega)
    rw [List.mem_filter, decide_eq_true_iff] at hx
    obtain ⟨-, hge, hlt⟩ := hx
    intro L hL hKL
    exact hge L hL (go.goStringLt_trans (hlt K rfl) hKL)
  have hcount := len_filter_sum es (fun x => decide (¬ keyGe lo x.1))
    (fun x => decide (keyIn lo (some K) x.1)) (fun x => decide (¬ keyGe (some K) x.1))
    (by
      intro x _
      by_cases hg : keyGe lo x.1
      · by_cases hk : go.GoStringLt x.1 K
        · have : ¬ keyGe (some K) x.1 := fun h => h K rfl hk
          simp [hg, keyIn, keyLt, hk, this]
        · have : keyGe (some K) x.1 := by intro l hl; cases hl; exact hk
          simp [hg, keyIn, keyLt, hk, this]
      · have hk := keyGe_lt hlK hg
        have : ¬ keyGe (some K) x.1 := fun h => h K rfl hk
        simp [hg, keyIn, this])
  omega

/-- **`prev`'s positions**: the new position is one before the old. -/
theorem stackPos_prev (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (n : GoString) (els els' : List elemRef) (pids pids' : List Nat) (d : Nat)
    (hp : sPath nl v b n els pids) (hp' : sPath nl v b n els' pids')
    (hs : sPrev v es pids' d els els')
    (hlen : d + 1 < els.length ↔ d + 1 < els'.length)
    (hbelow : sStartBelow v es pids els d) :
    stackPos v es pids' els' + 1 = stackPos v es pids els := by
  obtain ⟨e, e', R', he, rfl, hidx, hlast, hleaf⟩ := hs
  have hd : d < els.length := by
    rcases Nat.lt_or_ge d els.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at he
  obtain ⟨E, e0, R, rfl, hE, he0⟩ := split_at els d hd
  rw [he] at he0; cases he0
  have htk : (E ++ e :: R).take d = E := by
    rw [← hE]; simp
  rw [htk] at hp' hlen hlast hleaf ⊢
  have hpl := hp.2.1
  have hpl' := hp'.2.1
  simp only [List.length_append, List.length_cons] at hpl hpl' hlen
  obtain ⟨P, p, Q, rfl, hP, -⟩ := split_at pids d (by omega)
  obtain ⟨P', p', Q', rfl, hP', -⟩ := split_at pids' d (by omega)
  simp only [List.length_append, List.length_cons] at hpl hpl'
  -- the paths agree up to `d`
  have hpre : ∀ j, j ≤ d → (P' ++ p' :: Q')[j]? = (P ++ p :: Q)[j]? := by
    intro j
    induction j with
    | zero =>
      intro _
      have h1 := hp.2.2.1
      have h2 := hp'.2.2.1
      rw [List.head?_eq_getElem?] at h1 h2
      rw [h1, h2]
    | succ j ih =>
      intro hj
      have hjE : j < E.length := by omega
      obtain ⟨pid, hpid⟩ : ∃ pid, (P ++ p :: Q)[j]? = some pid :=
        Option.isSome_iff_exists.mp (by simp; omega)
      have hx : (E ++ e :: R)[j]? = some E[j] := by
        rw [List.getElem?_append_left hjE]; simp
      have hx' : (E ++ e' :: R')[j]? = some E[j] := by
        rw [List.getElem?_append_left hjE]; simp
      obtain ⟨pg, hpg, -, -, hnx⟩ :=
        (hp.2.2.2 j _ pid hx hpid).2.2.1 (by simp; omega)
      obtain ⟨pg', hpg', -, -, hnx'⟩ :=
        (hp'.2.2.2 j _ pid hx' (by rw [ih (by omega)]; exact hpid)).2.2.1 (by simp; omega)
      rw [hpg] at hpg'; cases hpg'
      rw [hnx, hnx']
  have hPP : P = P' := by
    apply List.ext_getElem?
    intro j
    rcases Nat.lt_or_ge j d with h | h
    · have := hpre j (by omega)
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)] at this
      exact this.symm
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  subst hPP
  have hpp : p = p' := by
    have := hpre d (Nat.le_refl _)
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)] at this
    simpa [hP, hP'] using this.symm
  subst hpp
  have hPE : P.length = E.length := by omega
  by_cases hl : d + 1 < E.length + (R.length + 1)
  · have hl' := hlen.1 hl
    have hRne : R ≠ [] := fun h => by subst h; simp at hl; omega
    have hRne' : R' ≠ [] := fun h => by subst h; simp at hl'; omega
    obtain ⟨pg, hpg, -, hlt, -⟩ :=
      (hp.2.2.2 d e p (by rw [List.getElem?_append_right (by omega)]; simp [hE])
        (by rw [List.getElem?_append_right (by omega)]; simp [hP])).2.2.1 (by simp; omega)
    refine stackPos_pred_up v es P E p Q Q' e e' R R' hPE (by omega) (by omega) hRne hRne' hidx
      (by rw [pidKeys_length v p pg hpg]; exact hlt) ?_ ?_ (hleaf (by simpa using hl'))
    · intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      refine hbelow.1 (d + 1 + j) x ?_ (by omega)
      rw [List.getElem?_append_right (by omega)]
      simpa [hE, show d + 1 + j - d = j + 1 by omega] using hj
    · intro j pid x hq hr hj
      refine hlast (d + 1 + j) pid x ?_ ?_ (by omega) (by simp; omega)
      · rw [List.getElem?_append_right (by omega)]
        simpa [hP, show d + 1 + j - d = j + 1 by omega] using hq
      · rw [List.getElem?_append_right (by omega)]
        simpa [hE, show d + 1 + j - d = j + 1 by omega] using hr
  · -- at the leaf: `R`, `R'`, `Q`, `Q'` are empty
    have hR : R = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hR' : R' = [] := List.eq_nil_of_length_eq_zero (by
      have : ¬ d + 1 < E.length + (R'.length + 1) := fun h => hl (hlen.2 h)
      omega)
    subst hR hR'
    have hQ : Q = [] := List.eq_nil_of_length_eq_zero (by simp at hpl; omega)
    have hQ' : Q' = [] := List.eq_nil_of_length_eq_zero (by simp at hpl'; omega)
    subst hQ hQ'
    exact stackPos_pred_leaf v es P E p e e' hPE hidx

end prev

end Prev

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Prev in
/-- **`rStackAt_prev`** (`Model/Cursor`), corrected (`prev`'s move `sPrev` and what its upward
loop found, `sStartBelow`, in place of `sPred`) and proved: the new stack is one position before
the old. -/
theorem rStackAt_prev' [GooseExts] (v : View) (n : GoString) (els els' : List elemRef)
    (pids pids' : List Nat) (d : Nat) (hp : sPath (fun _ => none) v null n els pids)
    (hp' : sPath (fun _ => none) v null n els' pids') (hnode : ∀ e ∈ els', e.node' = null)
    (hs : sPrev v (bktEnts ((v.data !! n).getD ∅)) pids' d els els')
    (hlen : d + 1 < els.length ↔ d + 1 < els'.length)
    (hbelow : sStartBelow v (bktEnts ((v.data !! n).getD ∅)) pids els d) :
    let es := bktEnts ((v.data !! n).getD ∅)
    rStackAt v n els (some (stackPos v es pids els)) ∧ 0 < stackPos v es pids els ∧
    rStackAt v n els' (some (stackPos v es pids els - 1)) := by
  intro es
  simp only [es]
  have hpos := stackPos_prev _ v (bktEnts ((v.data !! n).getD ∅)) null n els els' pids pids' d
    hp hp' hs hlen hbelow
  have hle := stackPos_le v (bktEnts ((v.data !! n).getD ∅)) pids els hbelow.2
  have hnode0 : ∀ e ∈ els, e.node' = null := by
    intro e he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
    have hj' : j < pids.length := by
      rw [hp.2.1]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hpid : pids[j]? = some pids[j] := List.getElem?_eq_getElem hj'
    apply Classical.byContradiction
    intro hne
    have := ((hp.2.2.2 j e _ hj hpid).1 hne)
    cases this
  refine ⟨⟨⟨pids, hp, by omega⟩, hnode0⟩, by omega, ⟨⟨pids', hp', by omega⟩, hnode⟩⟩
