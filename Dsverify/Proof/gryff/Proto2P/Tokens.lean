/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Tokens.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): the receive tokens' bookkeeping (`consumedTo`): picking a stream's
messages by index, and a token's message is in flight (`token_inflight`).
-/
module

public import Dsverify.Proof.gryff.Proto2P.Run

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure

/-! ## Sums over the three replica ids -/

/-- The sum of `f` over the three replica ids. -/
def sum3 (f : Fin 3 → Nat) : Nat := ((List.finRange 3).map f).sum

theorem sumN_gNet (f : Fin 3 → Nat) : sumN gNet f = sum3 f := rfl

theorem sum3_add (f g : Fin 3 → Nat) : sum3 (fun k => f k + g k) = sum3 f + sum3 g :=
  sumL_add f g _

theorem sum3_ite (i : Fin 3) (a : Nat) : sum3 (fun k => if k = i then a else 0) = a :=
  sumL_ite i a _ (List.nodup_finRange _) (List.mem_finRange i)

theorem sum3_le {f g : Fin 3 → Nat} (h : ∀ k, f k ≤ g k) : sum3 f ≤ sum3 g := sumL_le h _

theorem sum3_congr {f g : Fin 3 → Nat} (h : ∀ k, f k = g k) : sum3 f = sum3 g := by
  unfold sum3; congr 1; exact List.map_congr_left (fun k _ => h k)

/-- `sentCount` (Kahn's) at the model: a sum over the replica ids. -/
theorem sentCount_eq (T : Traces gNet) (p : kahn.Pos gNet) (j : Fin 3) (m : Msg) :
    sentCount T p j m = sum3 (fun i => (sentTo gNet j (kahn.outsAt T i (p i))).count m) := by
  unfold sentCount sum3
  show List.foldr _ 0 (List.finRange 3) = _
  rw [List.sum_eq_foldr, List.foldr_map]
  rfl

/-! ## Picking a stream's messages by index -/

/-- The messages of `s` at the indices below `c` that satisfy `P`, in order. -/
def pickL {α : Type} (s : List α) (c : Nat) (P : Nat → Bool) : List α :=
  ((List.range c).filter P).filterMap (fun n => s[n]?)

theorem pickL_zero {α : Type} (s : List α) (P : Nat → Bool) : pickL s 0 P = [] := rfl

theorem pickL_nil {α : Type} (c : Nat) (P : Nat → Bool) : pickL ([] : List α) c P = [] := by
  unfold pickL
  apply List.filterMap_eq_nil_iff.2
  intro n _; rfl

theorem pickL_cons {α : Type} (x : α) (s : List α) (c : Nat) (P : Nat → Bool) :
    pickL (x :: s) (c + 1) P = (if P 0 then [x] else []) ++ pickL s c (fun n => P (n + 1)) := by
  unfold pickL
  rw [List.range_succ_eq_map, List.filter_cons]
  have h : ∀ L : List Nat, List.filterMap (fun n => (x :: s)[n]?)
      (List.filter P (List.map Nat.succ L)) =
      List.filterMap (fun n => s[n]?) (List.filter (fun n => P (n + 1)) L) := by
    intro L
    rw [List.filter_map, List.filterMap_map]
    rfl
  by_cases h0 : P 0
  · simp only [h0, ↓reduceIte, List.filterMap_cons, List.getElem?_cons_zero, List.singleton_append]
    rw [h]
  · simp only [h0, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact h _

theorem pickL_sublist {α : Type} : ∀ (s : List α) (c : Nat) (P : Nat → Bool), (pickL s c P).Sublist s
  | [], c, P => by rw [pickL_nil]; exact List.Sublist.slnil
  | x :: s, 0, P => by rw [pickL_zero]; exact List.nil_sublist _
  | x :: s, c + 1, P => by
    rw [pickL_cons]
    by_cases h0 : P 0
    · simp only [h0, ↓reduceIte, List.singleton_append]
      exact (pickL_sublist s c _).cons_cons x
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      exact (pickL_sublist s c _).cons x

theorem filterMap_filter_or_count {α : Type} [BEq α] (g : Nat → Option α) (P Q : Nat → Bool)
    (hd : ∀ n, P n = true → Q n = true → False) (m : α) :
    ∀ R : List Nat, ((R.filter (fun n => P n || Q n)).filterMap g).count m =
      ((R.filter P).filterMap g).count m + ((R.filter Q).filterMap g).count m
  | [] => rfl
  | n :: R => by
    have ih := filterMap_filter_or_count g P Q hd m R
    simp only [List.filter_cons]
    by_cases hp : P n
    · have hq : Q n = false := by
        cases h : Q n
        · rfl
        · exact absurd (hd n hp h) id
      simp only [hp, hq, Bool.true_or, ↓reduceIte, Bool.false_eq_true]
      cases hgn : g n with
      | none => simp [hgn, ih]
      | some b => simp only [List.filterMap_cons, hgn, List.count_cons, ih]; omega
    · simp only [Bool.not_eq_true] at hp
      by_cases hq : Q n
      · simp only [hp, hq, Bool.or_true, ↓reduceIte, Bool.false_eq_true]
        cases hgn : g n with
        | none => simp [hgn, ih]
        | some b => simp only [List.filterMap_cons, hgn, List.count_cons, ih]; omega
      · simp only [Bool.not_eq_true] at hq
        simp only [hp, hq, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        exact ih

theorem pickL_or_count {α : Type} [BEq α] (s : List α) (c : Nat) (P Q : Nat → Bool)
    (hd : ∀ n, P n = true → Q n = true → False) (m : α) :
    (pickL s c (fun n => P n || Q n)).count m = (pickL s c P).count m + (pickL s c Q).count m :=
  filterMap_filter_or_count _ P Q hd m _

theorem filter_eq_single (n : Nat) :
    ∀ R : List Nat, R.Nodup → n ∈ R → R.filter (fun j => j == n) = [n]
  | [], _, h => absurd h List.not_mem_nil
  | x :: R, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.filter_cons]
    by_cases hx : x = n
    · subst hx
      simp only [beq_self_eq_true, ↓reduceIte, List.cons.injEq, true_and]
      apply List.filter_eq_nil_iff.2
      intro a ha; simp only [beq_iff_eq]; intro e; subst e; exact hnd.1 ha
    · have : (x == n) = false := by simp [hx]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact filter_eq_single n R hnd.2
        (by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hx; exact h)

theorem pickL_single {α : Type} (s : List α) (c n : Nat) (hn : n < c) :
    pickL s c (fun j => j == n) = s[n]?.toList := by
  unfold pickL
  rw [filter_eq_single n _ List.nodup_range (List.mem_range.2 hn)]
  simp only [List.filterMap_cons, List.filterMap_nil]
  cases s[n]? <;> rfl

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {L : List α}, (∀ x ∈ L, f x = g x) → L.filterMap f = L.filterMap g
  | [], _ => rfl
  | x :: L, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x (List.mem_cons_self ..),
      filterMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem pickL_congr {α : Type} {s s' : List α} {c : Nat} {P P' : Nat → Bool}
    (h : ∀ n, n < c → P n = P' n ∧ (P n = true → s[n]? = s'[n]?)) :
    pickL s c P = pickL s' c P' := by
  unfold pickL
  have hf : (List.range c).filter P = (List.range c).filter P' :=
    List.filter_congr (fun n hn => (h n (List.mem_range.1 hn)).1)
  rw [← hf]
  apply filterMap_congr'
  intro n hn
  rw [List.mem_filter] at hn
  exact (h n (List.mem_range.1 hn.1)).2 hn.2

theorem pickL_succ_false {α : Type} (s : List α) (c : Nat) (P : Nat → Bool) (h : P c = false) :
    pickL s (c + 1) P = pickL s c P := by
  unfold pickL
  rw [List.range_succ, List.filter_append]
  simp [h]

/-! ## Tokens -/

/-- `consumedTo` as a `flatMap` of picks. -/
theorem consumedTo_eq (T : Fin 3 → List Ev) (cur : GMap (Nat × Nat) Nat)
    (rx : GMap (Nat × Nat × Nat) Msg) (q : Fin 3) :
    consumedTo T cur rx q = (List.finRange 3).flatMap fun k =>
      pickL (streamOf k q (T k)) ((cur.lookup (k.val, q.val)).getD 0)
        (fun n => (rx.lookup (k.val, q.val, n)).isNone) := rfl

theorem consumedTo_count (T : Fin 3 → List Ev) (cur : GMap (Nat × Nat) Nat)
    (rx : GMap (Nat × Nat × Nat) Msg) (q : Fin 3) (m : Msg) :
    (consumedTo T cur rx q).count m = sum3 (fun k =>
      (pickL (streamOf k q (T k)) ((cur.lookup (k.val, q.val)).getD 0)
        (fun n => (rx.lookup (k.val, q.val, n)).isNone)).count m) := by
  rw [consumedTo_eq, List.count_flatMap]; rfl

/-- **A token's message is in flight**: with an unconsumed token of message `n` of `k'`'s stream
to `q`, `q` consumed fewer copies of it than were sent to it. -/
theorem token_count_lt {S : Inv2St} (hf : Inv2Facts S) {k' q : Fin 3} {n : Nat} {m : Msg}
    (hrx : S.rx.lookup (k'.val, q.val, n) = some m) :
    (recvd gNet (S.T q)).count m < sum3 (fun k => (streamOf k q (S.T k)).count m) := by
  obtain ⟨k'', q'', hk, hq, hn, hm⟩ := hf.rxOk _ _ _ _ hrx
  have hk2 : k'' = k' := Fin.ext hk
  have hq2 : q'' = q := Fin.ext hq
  subst hk2 hq2
  have hperm := (List.perm_iff_count.1 (hf.recvdOk q'')) m
  have hc : (recvd gNet (S.T q'')).count m = (consumedTo S.T S.cur S.rx q'').count m := hperm
  rw [hc, consumedTo_count]
  -- the picks plus the token's index are within each stream
  have key : ∀ k : Fin 3,
      (pickL (streamOf k q'' (S.T k)) ((S.cur.lookup (k.val, q''.val)).getD 0)
        (fun j => (S.rx.lookup (k.val, q''.val, j)).isNone)).count m +
        (if k = k'' then 1 else 0) ≤ (streamOf k q'' (S.T k)).count m := by
    intro k
    by_cases hk : k = k''
    · subst hk
      simp only [↓reduceIte]
      have hd : ∀ j, (S.rx.lookup (k.val, q''.val, j)).isNone = true → (j == n) = true → False := by
        intro j h1 h2
        simp only [beq_iff_eq] at h2; subst h2
        rw [hrx] at h1; cases h1
      have h1 := pickL_or_count (streamOf k q'' (S.T k)) ((S.cur.lookup (k.val, q''.val)).getD 0)
        _ _ hd m
      rw [pickL_single _ _ _ hn, hm] at h1
      have h2 := (pickL_sublist (streamOf k q'' (S.T k)) ((S.cur.lookup (k.val, q''.val)).getD 0)
        (fun j => (S.rx.lookup (k.val, q''.val, j)).isNone || j == n)).count_le m
      simp only [Option.toList_some, List.count_singleton_self] at h1
      omega
    · simp only [hk, ↓reduceIte, Nat.add_zero]
      exact (pickL_sublist _ _ _).count_le m
  have := sum3_le key
  rw [sum3_add, sum3_ite] at this
  omega

end Perennial.gryff.p2
