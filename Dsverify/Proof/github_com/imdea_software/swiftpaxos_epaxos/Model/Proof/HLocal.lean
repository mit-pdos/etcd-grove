/-
Local facts the handler proofs share: words (`slt`/`zz`, `toN (W32 r)`), ballot ownership
(different makers make different ballots), positions in lists with at most one matching
element, `getOrDefault`, `bumpCrt`, statuses.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Safe

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace HLocal

open SafeProof

/-! ## Words -/

theorem slt_iff (a b : w32) : a.slt b = true ↔ zz a < zz b := by
  simp only [zz, sint.Z]; exact BitVec.slt_iff_toInt_lt

theorem slt_false (a b : w32) : a.slt b = false ↔ zz b ≤ zz a := by
  have := slt_iff a b
  cases h : a.slt b <;> simp_all <;> omega

theorem toN_W32 (r : Nat) (hr : r < nR) : toN (W32 r) = r := by
  simp only [toN]; rw [show sint.Z (W32 (r : Int)) = (r : Int) from zz_W32 r (by omega)
    (by simp [nR] at hr; omega)]
  simp

theorem toN_of_zz (b : w32) (h : 0 ≤ zz b) : ((toN b : Nat) : Int) = zz b := by
  simp only [toN, zz] at *; omega

/-- A real ballot is nonnegative. -/
theorem zz_nonneg_of_make (S : Sys) (hown : Inv.ballotOwner S) {r : Nat} {x : InstId} {b : w32}
    (h : S.ev r (.makeBallot x b)) : (0 : Int) ≤ zz b := by
  rcases (hown.1 r x b h).1 with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; omega
  · simp [nR] at h1; omega

/-- Two makers of one ballot of an instance are the same replica. -/
theorem maker_eq (S : Sys) (hown : Inv.ballotOwner S) {r r' : Nat} {x : InstId} {b : w32}
    (hxq : x.q < nR) (h : S.ev r (.makeBallot x b)) (h' : S.ev r' (.makeBallot x b)) :
    r = r' := by
  simp only [nR] at hxq
  rcases (hown.1 r x b h).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases (hown.1 r' x b h').1 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · rw [h2, h2']
  · simp [nR] at h1'; omega
  · simp [nR] at h1; omega
  · rw [← h2, ← h2']

/-! ## Positions -/

theorem pos_unique {α : Type} (l : List α) (p : α → Bool) (h : (l.filter p).length ≤ 1)
    {n n' : Nat} {a b : α} (ha : l[n]? = some a) (hpa : p a = true) (hb : l[n']? = some b)
    (hpb : p b = true) : n = n' := by
  induction l generalizing n n' with
  | nil => simp at ha
  | cons c l ih =>
    cases n with
    | zero =>
      cases n' with
      | zero => rfl
      | succ n' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha; subst ha
        simp only [List.getElem?_cons_succ] at hb
        have : 1 ≤ (l.filter p).length := by
          have := List.mem_filter.mpr ⟨List.mem_of_getElem? hb, hpb⟩
          exact List.length_pos_of_mem this
        rw [List.filter_cons_of_pos hpa, List.length_cons] at h; omega
    | succ n =>
      cases n' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb; subst hb
        simp only [List.getElem?_cons_succ] at ha
        have : 1 ≤ (l.filter p).length := by
          have := List.mem_filter.mpr ⟨List.mem_of_getElem? ha, hpa⟩
          exact List.length_pos_of_mem this
        rw [List.filter_cons_of_pos hpb, List.length_cons] at h; omega
      | succ n' =>
        simp only [List.getElem?_cons_succ] at ha hb
        have h' : (l.filter p).length ≤ 1 := by
          have := (List.filter_sublist (p := p) (l := l)).length_le
          rw [List.filter_cons] at h; split at h
          · rw [List.length_cons] at h; omega
          · exact h
        rw [ih h' ha hb]

/-- A message at a position of `sent` is at that position of `msgs`. -/
theorem msgs_of_sent (S : Sys) {fr to n : Nat} {m : Msg} (h : (S.sent fr to)[n]? = some m) :
    (S.msgs fr to)[n]? = some m := by
  simp only [Sys.msgs, List.append_assoc]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1, h]

theorem mem_msgs_of_sent (S : Sys) {fr to n : Nat} {m : Msg} (h : (S.sent fr to)[n]? = some m) :
    m ∈ S.msgs fr to := List.mem_of_getElem? (msgs_of_sent S h)

/-! ## Records -/

/-- The record `getOrDefault` returns. -/
def recOr (σ : RState) (x : InstId) : InstRec := (σ.inst x).getD (newInstanceDefault x)

theorem setInst_self (σ : RState) (x : InstId) (w : InstRec) (h : σ.inst x = some w) :
    σ.setInst x w = σ := by
  cases σ; simp only [RState.setInst, RState.mk.injEq, and_true, true_and]
  funext y; simp only [upd_apply]; split <;> simp_all

theorem getOrDefault_eq (σ : RState) (x : InstId) :
    getOrDefault σ x = (σ.setInst x (recOr σ x), recOr σ x) := by
  unfold getOrDefault recOr
  split
  · rename_i w hw; simp only [hw, Option.getD_some, setInst_self σ x w hw]
  · rename_i hw; simp [hw]

@[simp] theorem setInst_inst (σ : RState) (x : InstId) (w : InstRec) (y : InstId) :
    (σ.setInst x w).inst y = if y = x then some w else σ.inst y := by
  simp [RState.setInst, upd_apply]

@[simp] theorem setInst_setInst (σ : RState) (x : InstId) (w w' : InstRec) :
    (σ.setInst x w).setInst x w' = σ.setInst x w' := by
  simp [RState.setInst]

theorem recOr_of (σ : RState) (x : InstId) :
    σ.inst x = some (recOr σ x) ∨ (σ.inst x = none ∧ recOr σ x = newInstanceDefault x) := by
  unfold recOr; cases h : σ.inst x <;> simp

/-! ## Statuses -/

theorem stGe_comm_of {s : w8} (hr : s = stNONE ∨ isPA s ∨ s = stACCEPTED ∨ isCommitted s)
    (h : stGe s stCOMMITTED = true) : isCommitted s := by
  rcases hr with rfl | (rfl | rfl) | rfl | h1
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact h1

theorem not_comm_of {s : w8} (h : stGe s stCOMMITTED = false) : ¬ isCommitted s := by
  rintro (rfl | rfl) <;> exact absurd h (by decide)

theorem comm_stGe {s : w8} (h : isCommitted s) : stGe s stCOMMITTED = true := by
  rcases h with rfl | rfl <;> decide

theorem comm_stGeAcc {s : w8} (h : isCommitted s) : stGe s stACCEPTED = true := by
  rcases h with rfl | rfl <;> decide

theorem acc_ne_none : stACCEPTED ≠ stNONE := by decide
theorem acc_not_pa : ¬ isPA stACCEPTED := by rintro (h | h) <;> exact absurd h (by decide)
theorem acc_not_comm : ¬ isCommitted stACCEPTED := by rintro (h | h) <;> exact absurd h (by decide)
theorem comm_not_pa {s : w8} (h : isCommitted s) : ¬ isPA s := by
  rcases h with rfl | rfl <;> rintro (h | h) <;> exact absurd h (by decide)
theorem none_not_comm : ¬ isCommitted stNONE := by rintro (h | h) <;> exact absurd h (by decide)
theorem none_not_pa : ¬ isPA stNONE := by rintro (h | h) <;> exact absurd h (by decide)

/-! ## `crtInstance` -/

theorem bumpCrt_crt' (σ : RState) (q : Nat) (n : w32) (q' : Nat) :
    (bumpCrt σ q n).crtInstance q' =
      if q' = q ∧ zz (σ.crtInstance q) < zz n then n else σ.crtInstance q' := by
  unfold bumpCrt
  by_cases h : (σ.crtInstance q).slt n = true
  · rw [if_pos h]; have := (slt_iff _ _).mp h
    by_cases hq : q' = q
    · subst hq; simp [this]
    · simp [upd_apply, hq]
  · rw [if_neg h]
    have : ¬ zz (σ.crtInstance q) < zz n := fun h' => h ((slt_iff _ _).mpr h')
    simp [this]

theorem zz_bumpCrt (σ : RState) (q : Nat) (n : w32) (q' : Nat) :
    zz ((bumpCrt σ q n).crtInstance q') =
      if q' = q then max (zz (σ.crtInstance q)) (zz n) else zz (σ.crtInstance q') := by
  rw [bumpCrt_crt']
  by_cases hq : q' = q
  · subst hq; by_cases h : zz (σ.crtInstance q') < zz n
    · simp [h]; omega
    · simp [h]; omega
  · simp [hq]

@[simp] theorem bumpCrt_inst (σ : RState) (q : Nat) (n : w32) : (bumpCrt σ q n).inst = σ.inst := by
  unfold bumpCrt; split <;> rfl
@[simp] theorem bumpCrt_id (σ : RState) (q : Nat) (n : w32) : (bumpCrt σ q n).id = σ.id := by
  unfold bumpCrt; split <;> rfl
@[simp] theorem bumpCrt_peer (σ : RState) (q : Nat) (n : w32) :
    (bumpCrt σ q n).peerOrder = σ.peerOrder := by unfold bumpCrt; split <;> rfl
@[simp] theorem bumpCrt_conf (σ : RState) (q : Nat) (n : w32) :
    (bumpCrt σ q n).conflicts = σ.conflicts := by unfold bumpCrt; split <;> rfl
@[simp] theorem bumpCrt_exe (σ : RState) (q : Nat) (n : w32) :
    (bumpCrt σ q n).execedUpTo = σ.execedUpTo := by unfold bumpCrt; split <;> rfl
@[simp] theorem bumpCrt_store (σ : RState) (q : Nat) (n : w32) :
    (bumpCrt σ q n).store = σ.store := by unfold bumpCrt; split <;> rfl
@[simp] theorem bumpRB_inst (σ : RState) (b : w32) : (bumpRecvBallot σ b).inst = σ.inst := by
  unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRB_id (σ : RState) (b : w32) : (bumpRecvBallot σ b).id = σ.id := by
  unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRB_peer (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).peerOrder = σ.peerOrder := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRB_crt (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).crtInstance = σ.crtInstance := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRB_conf (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).conflicts = σ.conflicts := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRB_exe (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).execedUpTo = σ.execedUpTo := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRB_store (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).store = σ.store := by unfold bumpRecvBallot; split <;> rfl

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem slotsOn_congr (σ σ' : RState) (xs : List InstId) (k : w64)
    (h : ∀ y ∈ xs, σ'.inst y = σ.inst y) : Sys.slotsOn σ' xs k = Sys.slotsOn σ xs k := by
  simp only [Sys.slotsOn]
  exact flatMap_congr' (fun y hy => by rw [h y hy])

end HLocal

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
