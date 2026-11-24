/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Init.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): the invariant's initial state (`inv0`) and its facts (`facts_init`).
-/
module

public import Dsverify.Proof.gryff.Proto2P.Facts
public import Dsverify.Proof.gryff.StartInit

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure dsverify_lab.harness

/-- The invariant's state at the start (the client ids' turns and connections as allocated). -/
def inv0 (mt : GMap Int (Int × Bool)) (mc : GMap w32 (Option Nat)) : Inv2St :=
  ⟨fun _ => [], [], preds0, preds0, ∅, budget0, W64 0, [], ∅, mt, mc, ∅, ∅, cur0, ∅, ∅⟩

theorem foldr_insert_lookup {K V : Type} [DecidableEq K] (f : K → V) :
    ∀ (L : List K) (k : K), (L.foldr (fun x m => GMap.insert x (f x) m) ∅).lookup k =
      if k ∈ L then some (f k) else none
  | [], k => by simp
  | x :: L, k => by
    show (if x = k then some (f x) else _) = _
    rw [foldr_insert_lookup f L k]
    by_cases h : x = k
    · subst h; simp
    · simp [h, Ne.symm h]

theorem preds0_eq : preds0 = [0, 1, 2].foldr (fun x m => GMap.insert x (none : Option (List w64)) m) ∅ := rfl
theorem claims0_eq : claims0 = [0, 1, 2].foldr (fun x m => GMap.insert x () m) ∅ := rfl

theorem preds0_lookup (k : Fin 3) : preds0.lookup k.val = some none := by
  rw [preds0_eq, foldr_insert_lookup (fun _ => (none : Option (List w64)))]
  have := k.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rw [if_pos (by omega)]

theorem cur0_lookup (k q : Fin 3) : cur0.lookup (k.val, q.val) = some 0 := by
  unfold cur0
  rw [foldr_insert_lookup (fun _ => (0 : Nat))]
  rw [if_pos]
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  exact ⟨k.val, k.isLt, q.val, q.isLt, rfl, rfl⟩

theorem frontVal_nil : frontVal [] 0 = W64 0 := by
  unfold frontVal
  have h : ∀ r : Fin 3, (cutSt [] 0 r).val = W64 0 := fun r => rfl
  split
  · exact h 0
  · split
    · exact h 1
    · exact h 2

theorem facts_init (mt : GMap Int (Int × Bool)) (mc : GMap w32 (Option Nat)) :
    Inv2Facts (inv0 mt mc) := by
  have hops : ops (inv0 mt mc).l1 = [] := rfl
  exact {
    run := ⟨_, .nil _⟩
    proj := fun r => rfl
    predKeys := fun k => by show (preds0.lookup k.val).isSome; rw [preds0_lookup]; rfl
    predPrefix := fun k ws h => by
      have h' : preds0.lookup k.val = some (some ws) := h
      rw [preds0_lookup] at h'; cases h'
    predNode := fun i ws h => by
      have h' : preds0.lookup i = some (some ws) := h
      rw [preds0_eq, foldr_insert_lookup] at h'
      split at h' <;> cases h'
    unset := fun _ => ⟨rfl, rfl⟩
    closure := fun ws h => by
      have h' : preds0.lookup (0 : Fin 3).val = some (some (ws 0)) := h 0
      rw [preds0_lookup] at h'; cases h'
    val := frontVal_nil.symm
    wb := ⟨(fun o ho => by rw [hops] at ho; cases ho),
      (fun o ho => by rw [hops] at ho; cases ho)⟩
    linNodup := List.nodup_nil
    reg := fun o ho => by rw [hops] at ho; cases ho
    reqReg := fun id k i h => by cases h
    reqFresh := fun id ki h => by cases h
    binding := fun id k h => by
      rcases h with ⟨i, h⟩ | ⟨o, ho, -⟩
      · cases h
      · rw [hops] at ho; cases ho
    repSet := fun conn k h => by cases h
    turnsReg := fun id h => by cases h
    turnsIdle := fun cid n _ r h => by cases h
    turnsBusy := fun cid n _ r _ h => by cases h
    order := fun cid r1 r2 _ h => by cases h
    budgetKeys := fun u h => by
      have h' : (budget0.lookup u).isSome := h
      unfold budget0 at h'
      rw [foldr_insert_lookup (fun _ => ())] at h'
      split at h'
      · rename_i hu; exact List.mem_range.1 hu
      · cases h'
    budgetSpent := ⟨fun _ => 0, ⟨(fun id h => by cases h), (fun id1 id2 h => by cases h)⟩⟩
    reqBudget := fun id k i h => by cases h
    curOk := fun k q => ⟨0, cur0_lookup k q, Nat.zero_le _⟩
    rxOk := fun k q n m h => by cases h
    recvdOk := fun q => by
      show (recvd gNet []).Perm (consumedTo (fun _ => []) cur0 ∅ q)
      have : consumedTo (fun _ => []) cur0 ∅ q = [] := by
        rw [consumedTo_eq]
        apply List.flatMap_eq_nil_iff.2
        intro k _
        have hs : streamOf k q [] = [] := rfl
        rw [hs, pickL_nil]
      rw [this]; exact List.Perm.nil }

end Perennial.gryff.p2
