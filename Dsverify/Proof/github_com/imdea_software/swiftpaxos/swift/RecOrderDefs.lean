/-
The definitions, specs and lemmas of `RecOrder.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecReachesDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

theorem find?_idx {α : Type} (l : List α) (q : α → Bool) (i : Nat) (hi : i < l.length)
    (hq : q l[i] = true) (hpre : ∀ j (hj : j < i), q (l[j]'(by omega)) = false) :
    l.find? q = some l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp at hq; simp [List.find?_cons, hq]
    | succ i =>
      have ha := hpre 0 (by omega)
      simp only [List.getElem_cons_zero] at ha
      rw [List.find?_cons, ha]
      exact ih i (by simp at hi; omega) hq (fun j hj => by
        have := hpre (j + 1) (by omega); simpa using this)

/-- `recOrder`'s readiness test of `c` against the placed list `P`. -/
def readyIn (k : Kept) (P : List CmdId) (c : CmdId) : Bool :=
  ((k.get c).map RecEntry.dep).getD [] |>.all (fun d => (k.get d).isNone || d ∈ P)

/-- The step when the first ready unplaced id is `ids[i]`. -/
theorem recOrderStep_readyI (k : Kept) (ids P : List CmdId) (i : Nat) (hi : i < ids.length)
    (hP : ids[i] ∉ P) (hr : readyIn k P ids[i] = true)
    (hpre : ∀ j (hj : j < i), ids[j]'(by omega) ∈ P ∨ readyIn k P (ids[j]'(by omega)) = false) :
    recOrderStep k ids P = P ++ [ids[i]] := by
  have hf : (ids.filter (· ∉ P)).find? (readyIn k P) = some ids[i] := by
    rw [List.find?_filter]
    apply find?_idx ids _ i hi
    · simp [hP]; exact hr
    · intro j hj
      rcases hpre j hj with h | h
      · simp [h]
      · simp [h]
  unfold recOrderStep
  simp only
  have : (List.find? (fun c => (((k.get c).map RecEntry.dep).getD []).all
      (fun d => (k.get d).isNone || decide (d ∈ P))) (ids.filter (· ∉ P))) = some ids[i] := hf
  rw [this]

/-- The step when no unplaced id is ready and the first unplaced one is `ids[i]`. -/
theorem recOrderStep_first (k : Kept) (ids P : List CmdId) (i : Nat) (hi : i < ids.length)
    (hnone : ∀ j (hj : j < ids.length), ids[j] ∈ P ∨ readyIn k P ids[j] = false)
    (hP : ids[i] ∉ P) (hpre : ∀ j (hj : j < i), ids[j]'(by omega) ∈ P) :
    recOrderStep k ids P = P ++ [ids[i]] := by
  have hf : (ids.filter (· ∉ P)).find? (readyIn k P) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx.1
    rcases hnone j hj with h | h
    · simp [h] at hx
    · simp [h]
  have hh : (ids.filter (· ∉ P)).head? = some ids[i] := by
    rw [List.head?_filter]
    apply find?_idx ids _ i hi
    · simp [hP]
    · intro j hj; simp [hpre j hj]
  unfold recOrderStep
  simp only
  have : (List.find? (fun c => (((k.get c).map RecEntry.dep).getD []).all
      (fun d => (k.get d).isNone || decide (d ∈ P))) (ids.filter (· ∉ P))) = none := hf
  rw [this, hh]

/-- The placed list after `n ≤ |ids|` rounds: `n` distinct ids. -/
theorem recOrder_iter_len (k : Kept) (ids : List CmdId) (hnd : ids.Nodup) :
    ∀ n ≤ ids.length, (iter (recOrderStep k ids) n []).length = n ∧
      (iter (recOrderStep k ids) n []).Nodup ∧ ∀ c ∈ iter (recOrderStep k ids) n [], c ∈ ids := by
  intro n
  induction n with
  | zero => intro _; simp [iter]
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [iter_succ']
    generalize iter (recOrderStep k ids) n [] = P at h1 h2 h3
    have hex : ∃ c ∈ ids, c ∉ P := by
      apply Classical.byContradiction
      intro hno
      simp only [not_exists, not_and, Classical.not_not] at hno
      have := (List.subperm_of_subset hnd hno).length_le
      omega
    obtain ⟨c0, hc0, hc0P⟩ := hex
    have hrest : c0 ∈ ids.filter (· ∉ P) := by simp [hc0, hc0P]
    have key : ∃ c ∈ ids.filter (· ∉ P), recOrderStep k ids P = P ++ [c] := by
      unfold recOrderStep
      simp only
      cases hf : (ids.filter (· ∉ P)).find? (fun c => (((k.get c).map RecEntry.dep).getD []).all
          (fun d => (k.get d).isNone || decide (d ∈ P))) with
      | some c => exact ⟨c, List.mem_of_find?_eq_some hf, rfl⟩
      | none =>
        cases hh : (ids.filter (· ∉ P)).head? with
        | none => rw [List.head?_eq_none_iff] at hh; rw [hh] at hrest; simp at hrest
        | some c => exact ⟨c, List.mem_of_mem_head? hh, rfl⟩
    obtain ⟨c, hc, he⟩ := key
    rw [List.mem_filter] at hc
    simp only [decide_eq_true_eq] at hc
    rw [he]
    refine ⟨by simp [h1], ?_, ?_⟩
    · rw [List.nodup_append]; refine ⟨h2, by simp, ?_⟩
      intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact hc.2 ha
    · intro a ha; simp at ha; rcases ha with ha | rfl
      · exact h3 a ha
      · exact hc.1

end sp

/-- After `recOrder`'s search for a ready id: none (`next = -1`, every unplaced id blocked),
or the step's id at `next`. -/
def swift.findOk (k : sp.Kept) (ids : List swift.CommandId) (P : List sp.CmdId) (nx : w64) : Prop :=
  (sint.Z nx = -1 ∧ ∀ j (hj : j < ids.length), toCmdId ids[j] ∈ P ∨
      sp.readyIn k P (toCmdId ids[j]) = false) ∨
  (∃ i0, ∃ h : i0 < ids.length, sint.Z nx = i0 ∧
    sp.recOrderStep k (ids.map toCmdId) P = P ++ [toCmdId ids[i0]])

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions]

end proof

end Perennial.github_com.imdea_software.swiftpaxos
