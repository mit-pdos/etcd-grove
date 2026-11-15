/-
`Cursor.prev` of a writer's cursor in `Last`'s loop (U6aa, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"; U6y's F4): the pure facts of `Cursor.prev_w`'s proof. Every entry was below
the old (empty) leaf's lower bound, the key of the level found; the new leaf, one before at that
level and last below, has that key as its upper bound, so every entry after it is in it
(`tail_up`). At the root with every index `0`, the old leaf's lower bound is none: the bucket is
empty (`tail_root`), and `first`'s stack is `Last`'s invariant (`lastInv_first`). `last`'s new stack,
at its leaf's last index, is too (`lastInv_new`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WNextPure
public import Proof.go_etcd_io.bbolt.Read.WCur

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace WPrev

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write WBridge WGoFirst

section pure
variable [GooseExts]

/-- A branch index the up-loop passed (signed at most `0`, below its page's count) is `0`. -/
theorem idx_zero (x : w64) (h1 : x.toNat < 2 ^ 16) (h2 : sint.Z x ≤ 0) : x.toNat = 0 := by
  have : sint.Z x = (x.toNat : Int) := by
    show x.toInt = _; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  omega

/-- The level found (signed above `0`, below its page's count), one back. -/
theorem idx_pred (x : w64) (h1 : x.toNat < 2 ^ 16) (h2 : 0 < sint.Z x) :
    (x - W64 1).toNat + 1 = x.toNat := by
  have : sint.Z x = (x.toNat : Int) := by
    show x.toInt = _; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have h3 : 1 ≤ x.toNat := by omega
  rw [BitVec.toNat_sub]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  simp only [show (W64 1).toNat = 1 from rfl]
  rw [show 2 ^ 64 - 1 + x.toNat = (x.toNat - 1) + 1 * 2 ^ 64 by omega, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by omega)]
  omega


theorem take_set_last {α : Type} (l : List α) (n : Nat) (x : α) (hn : n < l.length) :
    (l.take (n + 1)).set n x = l.take n ++ [x] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn]
  have : (l.take n).length = n := by simp; omega
  simp only [Option.toList_some]
  rw [List.set_append_right _ _ (by omega), this, Nat.sub_self]
  rfl

theorem mem_dropLast_idx {α : Type} (l : List α) (x : α) (h : x ∈ l.dropLast) :
    ∃ j, j + 1 < l.length ∧ l[j]? = some x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
  refine ⟨j, by simp at hj; omega, ?_⟩
  rw [List.getElem_dropLast]; exact List.getElem?_eq_getElem _

/-- **The levels the up-loop passed** (signed at most `0`) are at `0`, but for the leaf. -/
theorem below_zero (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (els : List elemRef) (pids : List Nat) (hp : sPathR nl v b rt els pids) (k : Nat)
    (hall : ∀ j x, k ≤ j → els[j]? = some x → sint.Z x.index' ≤ 0) :
    ∀ j x, k ≤ j → j + 1 < els.length → els[j]? = some x → x.index'.toNat = 0 := by
  intro j x hk hj hx
  obtain ⟨pid, hpid⟩ : ∃ pid, pids[j]? = some pid :=
    ⟨_, List.getElem?_eq_getElem (by rw [hp.2.1]; omega)⟩
  obtain ⟨pg, -, -, hlt, -⟩ := (hp.2.2.2 j x pid hx hpid).2.2.1 hj
  have : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
  exact idx_zero _ (by omega) (hall j x hk hx)

open Classical in
/-- **Every entry after the new leaf is in it** (`prev`'s move at the level of `p`: the old stack
at `0` below it and its leaf empty, the new one one before at it and last below). -/
theorem tail_up (v : View) (es : List BoltEnt) (E : List elemRef) (P : List Nat) (p : Nat)
    (e e' lf : elemRef) (T0 R : List elemRef) (U Q : List Nat)
    (hPE : P.length = E.length) (hUT : U.length = T0.length + 1) (hQR : Q.length = R.length)
    (hR : R ≠ [])
    (hidx : e'.index'.toNat + 1 = e.index'.toNat) (hlt : e.index'.toNat < (pidKeys v p).length)
    (h0 : ∀ x ∈ T0, x.index'.toNat = 0)
    (hlast : ∀ j pid x, Q[j]? = some pid → R[j]? = some x → j + 1 < R.length →
      x.index'.toNat + 1 = (pidKeys v pid).length)
    (hold : sTailEmpty v es (P ++ p :: U) (E ++ e :: (T0 ++ [lf])))
    (hc0 : leafCnt v es (P ++ p :: U) (E ++ e :: (T0 ++ [lf])) = 0) :
    sTailEmpty v es (P ++ p :: Q) (E ++ e' :: R) := by
  obtain ⟨q0, Q0, rfl⟩ : ∃ q0 Q0, Q = q0 :: Q0 := by
    cases Q with
    | nil => cases R with | nil => exact absurd rfl hR | cons _ _ => simp at hQR
    | cons q0 Q0 => exact ⟨q0, Q0, rfl⟩
  obtain ⟨u0, U0, rfl⟩ : ∃ u0 U0, U = u0 :: U0 := by
    cases U with
    | nil => simp at hUT
    | cons u0 U0 => exact ⟨u0, U0, rfl⟩
  obtain ⟨lf0, hlf0⟩ : ∃ lf0 : elemRef, lf0 = { lf with index' := W64 0 } := ⟨_, rfl⟩
  have hsn : pathBnd v (P ++ p :: u0 :: U0) (E ++ e :: (T0 ++ [lf])) =
      pathBnd v (P ++ p :: u0 :: U0) (E ++ e :: (T0 ++ [lf0])) := by
    have := WNext.pathBnd_snoc v (E ++ e :: T0) (P ++ p :: u0 :: U0) lf lf0
      (by simp at hUT ⊢; omega)
    simpa using this
  have hf : ∀ x ∈ T0 ++ [lf0], x.index'.toNat = 0 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact h0 x h
    · rw [List.mem_singleton] at h; subst h; rw [hlf0]; rfl
  have hlo : (pathBnd v (P ++ p :: u0 :: U0) (E ++ e :: (T0 ++ [lf0]))).1 =
      some ((pidKeys v p).getD e.index'.toNat []) := by
    unfold pathBnd
    rw [Prev.pathBndFrom_append v E P _ p _ _ hPE, Prev.pathBndFrom_cons v _ p _ e _ (by simp),
      Prev.pathBndFrom_first v _ (u0 :: U0) _ hf]
    simp only [entryBnd, childLo]
    rw [if_neg (by omega)]
  have hhi : (pathBnd v (P ++ p :: q0 :: Q0) (E ++ e' :: R)).2 =
      some ((pidKeys v p).getD e.index'.toNat []) := by
    unfold pathBnd
    rw [Prev.pathBndFrom_append v E P _ p _ _ hPE, Prev.pathBndFrom_cons v _ p _ e' _ (by simp),
      Prev.pathBndFrom_last v R (q0 :: Q0) _ hQR hlast]
    simp only [entryBnd, childHi]
    rw [if_pos (by omega), hidx]
  unfold sTailEmpty at hold ⊢
  unfold leafCnt entsIn at hold hc0 ⊢
  rw [hsn] at hold hc0
  generalize (pidKeys v p).getD e.index'.toNat [] = K at hlo hhi
  generalize hb0 : pathBnd v (P ++ p :: u0 :: U0) (E ++ e :: (T0 ++ [lf0])) = b0 at hold hc0 hlo
  obtain ⟨lo0, hi0⟩ := b0
  simp only at hlo hold hc0; subst hlo
  rw [hc0, Nat.add_zero, List.length_filter_eq_length_iff] at hold
  generalize hbn : pathBnd v (P ++ p :: q0 :: Q0) (E ++ e' :: R) = bn at hhi ⊢
  obtain ⟨lo, hi⟩ := bn
  simp only at hhi ⊢; subst hhi
  have hcount := Prev.len_filter_sum es (fun x => decide (¬ keyGe lo x.1))
    (fun x => decide (keyIn lo (some K) x.1)) (fun _ => true)
    (by
      intro x hx
      have hk : go.GoStringLt x.1 K := by
        have := hold x hx
        simp only [decide_eq_true_eq] at this
        exact Classical.byContradiction fun h => this (fun l hl => by cases hl; exact h)
      by_cases hg : keyGe lo x.1
      · simp [hg, keyIn, keyLt, hk]
      · simp [hg, keyIn])
  rw [show (es.filter fun _ => true) = es from List.filter_eq_self.2 (by simp)] at hcount
  exact hcount

open Classical in
/-- **At the root with every index `0`, an empty leaf with every entry after it in it: the bucket
is empty.** -/
theorem tail_root (v : View) (es : List BoltEnt) (E : List elemRef) (lf : elemRef)
    (pids : List Nat) (hl : pids.length = E.length + 1) (h0 : ∀ x ∈ E, x.index'.toNat = 0)
    (hold : sTailEmpty v es pids (E ++ [lf])) (hc0 : leafCnt v es pids (E ++ [lf]) = 0) :
    es = [] := by
  obtain ⟨lf0, hlf0⟩ : ∃ lf0 : elemRef, lf0 = { lf with index' := W64 0 } := ⟨_, rfl⟩
  have hsn := WNext.pathBnd_snoc v E pids lf lf0 hl
  have hf : ∀ x ∈ E ++ [lf0], x.index'.toNat = 0 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact h0 x h
    · rw [List.mem_singleton] at h; subst h; rw [hlf0]; rfl
  have hlo : (pathBnd v pids (E ++ [lf0])).1 = none := Prev.pathBndFrom_first v _ pids _ hf
  unfold sTailEmpty at hold
  rw [hc0, Nat.add_zero, hsn, hlo] at hold
  have : (es.filter fun e => decide (¬ keyGe none e.1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x _
    simp only [decide_eq_true_eq, Classical.not_not]
    intro l hl; cases hl
  rw [this] at hold
  exact List.eq_nil_of_length_eq_zero hold.symm

/-- **`first`'s stack on an empty bucket is `Last`'s invariant.** -/
theorem lastInv_first (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (ipg : List w8) (els : List elemRef) (h : wCurAt nl v [] b rt ipg els (some 0)) :
    ∃ pids, wLastInv nl v [] b rt ipg els pids := by
  obtain ⟨pids, hp, hlo, hc⟩ := h
  have hc0 : leafCnt v [] pids els = 0 := by simp [leafCnt, entsIn]
  refine ⟨pids, hp, hlo, by simp [sTailEmpty, leafCnt, entsIn], ?_⟩
  rcases hc with ⟨hlt, -⟩ | ⟨⟨-, e, hl, hi⟩, -⟩
  · omega
  · refine ⟨e, hl, Or.inl ⟨hc0, ?_⟩⟩
    rw [hc0] at hi
    rcases hi with hi | ⟨-, hi⟩
    · exact Or.inl hi
    · exact Or.inr hi

/-- **`last`'s new stack is `Last`'s invariant**: a path whose leaf holds its bounds' entries,
every entry after it in it, at its leaf's last index. -/
theorem lastInv_new (nl : Loc → Option (Loc × Nat)) (v : View) (hv : viewWF v) (es : List BoltEnt)
    (b : Loc) (rt : Nat) (ipg : List w8) (els : List elemRef) (pids : List Nat)
    (hp : sPathR nl v b rt els pids) (hlo : sLeafOK v ipg es pids els)
    (ht : sTailEmpty v es pids els) (htop : sTopLast v es pids els)
    (hcnt : leafCnt v es pids els < 2 ^ 63) :
    wLastInv nl v es b rt ipg els pids := by
  refine ⟨hp, hlo, ht, ?_⟩
  obtain ⟨e, he⟩ := WNext.getLast_some els hp.1
  obtain ⟨pid, hpid⟩ : ∃ pid, pids.getLast? = some pid := by
    cases h : pids.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at h
      have := hp.2.1; rw [h] at this; simp at this
      exact absurd (List.eq_nil_of_length_eq_zero this.symm) hp.1
    | some p => exact ⟨p, rfl⟩
  refine ⟨e, he, ?_⟩
  rcases htop e pid he hpid with ⟨pg, hpg, hf, -⟩ | ⟨-, hi⟩
  · exfalso
    have hj := hp.2.2.2 (els.length - 1) e pid (getLast_idx els e he)
      (by rw [← hp.2.1]; exact getLast_idx pids pid hpid)
    have hpos : 0 < els.length := List.length_pos_iff.2 hp.1
    exact WNext.leaf_not_branch v hv pid pg hpg hf (hj.2.2.2 (by omega))
  · by_cases h0 : leafCnt v es pids els = 0
    · refine Or.inl ⟨h0, Or.inr ?_⟩
      rw [hi, h0]; rfl
    · refine Or.inr ⟨by omega, ?_⟩
      rw [hi]
      have : ((leafCnt v es pids els : Int) - 1) = ((leafCnt v es pids els - 1 : Nat) : Int) := by
        omega
      rw [this]
      have h2 : (W64 ((leafCnt v es pids els - 1 : Nat) : Int)).toNat = leafCnt v es pids els - 1 := by
        simp; omega
      omega

end pure

end WPrev

end bbolt
end EtcdGrove
end Perennial
