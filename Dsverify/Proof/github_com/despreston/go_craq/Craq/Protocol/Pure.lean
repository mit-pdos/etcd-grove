/-
Pure lemmas about `cvOf`, `kvOfPuts`, `absOf` (the protocol's laws, package `laws`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

/-- One step of `cvOf`'s fold. -/
def cvStep (k : GoString) (m : w64) (e : GoString × w64) : w64 :=
  if e.1 = k ∧ uint.Z m < uint.Z e.2 then e.2 else m

theorem cvOf_eq (L : CLog) (k : GoString) : cvOf L k = L.foldl (cvStep k) (W64 0) := rfl

theorem foldl_cvStep_ge (k : GoString) (t : CLog) :
    ∀ m : w64, uint.Z m ≤ uint.Z (t.foldl (cvStep k) m) := by
  induction t with
  | nil => intro m; simp
  | cons e t ih =>
    intro m
    simp only [List.foldl_cons]
    refine Int.le_trans ?_ (ih _)
    unfold cvStep
    split
    · next h => exact Int.le_of_lt h.2
    · exact Int.le_refl _

theorem cvOf_append_gen (L t : CLog) (k : GoString) :
    cvOf (L ++ t) k = t.foldl (cvStep k) (cvOf L k) := by
  simp only [cvOf_eq, List.foldl_append]

/-- `cvOf` is monotone along prefixes. -/
theorem cvOf_prefix {L0 L : CLog} (h : L0 <+: L) (k : GoString) :
    uint.Z (cvOf L0 k) ≤ uint.Z (cvOf L k) := by
  obtain ⟨t, rfl⟩ := h
  rw [cvOf_append_gen]
  exact foldl_cvStep_ge k t _

theorem cvOf_nil (k : GoString) : cvOf [] k = W64 0 := rfl

theorem cvOf_append_one (L : CLog) (k k' : GoString) (v : w64) :
    cvOf (L ++ [(k, v)]) k' =
      if k' = k ∧ uint.Z (cvOf L k) < uint.Z v then v else cvOf L k' := by
  rw [cvOf_append_gen]
  simp only [List.foldl_cons, List.foldl_nil, cvStep]
  by_cases hk : k' = k
  · subst hk; simp
  · have : ¬ k = k' := fun h => hk h.symm
    simp [hk, this]

theorem cvOf_append.wp_proof : cvOf_append.spec := cvOf_append_one

theorem cvOf_commit.wp_proof : cvOf_commit.spec := by
  intro L k k' v
  by_cases h : uint.Z (cvOf L k) < uint.Z v
  · simp only [h, ↓reduceIte, and_true]; rw [cvOf_append_one]; simp [h]
  · simp [h]

/-- The commit's new log. -/
theorem cvOf_commit_self (L : CLog) (k : GoString) (v : w64)
    (h : uint.Z (cvOf L k) < uint.Z v) : cvOf (L ++ [(k, v)]) k = v := by
  rw [cvOf_append_one]; simp [h]

theorem cvOf_commit_ne (L : CLog) (k k' : GoString) (v : w64) (h : k' ≠ k) :
    cvOf (L ++ [(k, v)]) k' = cvOf L k' := by
  rw [cvOf_append_one]; simp [h]

theorem kvOfPuts_nil : kvOfPuts [] = KvM.init := by
  funext k; rfl

theorem kvOfPuts_cons (k x : GoString) (l : List (GoString × GoString)) (k' : GoString) :
    kvOfPuts ((k, x) :: l) k' = if k' = k then some x else kvOfPuts l k' := by
  unfold kvOfPuts
  by_cases h : k' = k
  · subst h; simp
  · have : ¬ k = k' := fun h' => h h'.symm
    simp [this, h]

/-- A put's step from `kvOfPuts l`. -/
theorem kvOfPuts_put_step (k x : GoString) (l : List (GoString × GoString)) :
    KvM.step (kvOfPuts l) (.put k x) (kvOfPuts ((k, x) :: l)) .done := by
  show ((fun k' => if k' = k then some x else kvOfPuts l k'), KvOutput.done) = _
  congr 1
  funext k'
  rw [kvOfPuts_cons]

/-- A put's step from `kvOfPuts l`, as a function. -/
theorem kvOfPuts_put_stepF (k x : GoString) (l : List (GoString × GoString)) :
    KvM.stepF (.put k x) (kvOfPuts l) = (kvOfPuts ((k, x) :: l), .done) :=
  kvOfPuts_put_step k x l

theorem kvOfPuts_get_step (k : GoString) (σ : KvM.State) :
    KvM.step σ (.get k) σ (.got (σ k)) := rfl

end github_com.despreston.go_craq

end Perennial
