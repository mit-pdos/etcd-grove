/-
The definitions, specs and lemmas of `RecReaches.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## `recReaches`' search, pure -/

/-- The reachability relation of the kept dependencies (model ids). -/
abbrev swift.reachRel (k : sp.Kept) : sp.CmdId → sp.CmdId → Prop := fun y d => d ∈ sp.kdeps k y

/-- `recReaches`' search state: every node of `pend` (the stack, and the node being expanded)
is `src` or reachable from it; every seen node is reachable; `src` and every seen node is
pending or has its dependencies seen, none of them `dst`. -/
def swift.dfsOk (k : sp.Kept) (src dst : swift.CommandId) (pend : List swift.CommandId)
    (sm : GMap swift.CommandId Bool) : Prop :=
  (∀ y ∈ pend, y = src ∨ Relation.TransGen (swift.reachRel k) (toCmdId src) (toCmdId y)) ∧
  (∀ y v, sm !! y = some v → v = true ∧
    Relation.TransGen (swift.reachRel k) (toCmdId src) (toCmdId y)) ∧
  (∀ z, (z = src ∨ (sm !! z).isSome) → z ∈ pend ∨
    ∀ d ∈ sp.kdeps k (toCmdId z), d ≠ toCmdId dst ∧ (sm !! ofCmdId d).isSome)

theorem swift.dfs_init (k : sp.Kept) (src dst : swift.CommandId) :
    swift.dfsOk k src dst [src] ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  intro z hz
  left
  rcases hz with rfl | hz
  · simp
  · simp at hz

theorem swift.dfs_reach_of {k : sp.Kept} {src dst : swift.CommandId} {pend : List swift.CommandId}
    {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst pend sm) {x : swift.CommandId}
    (hx : x ∈ pend) {d : sp.CmdId} (hd : d ∈ sp.kdeps k (toCmdId x)) :
    Relation.TransGen (swift.reachRel k) (toCmdId src) d := by
  rcases H.1 x hx with rfl | h
  · exact Relation.TransGen.single hd
  · exact Relation.TransGen.tail h hd

/-- A dependency `y` of the expanded `x`, not yet seen: seen and pushed. -/
theorem swift.dfs_push {k : sp.Kept} {src dst : swift.CommandId} {s : List swift.CommandId}
    {x : swift.CommandId} {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst (s ++ [x]) sm)
    {y : swift.CommandId} (hy : toCmdId y ∈ sp.kdeps k (toCmdId x)) :
    swift.dfsOk k src dst ((s ++ [y]) ++ [x]) (<[y := true]> sm) := by
  have hr := swift.dfs_reach_of H (by simp) hy
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | rfl) | rfl
    · exact h1 z (by simp [hz])
    · exact Or.inr hr
    · exact h1 z (by simp)
  · intro z v hz
    by_cases e : z = y
    · subst e; rw [GMap.lookup_insert_eq] at hz; cases hz; exact ⟨rfl, hr⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hz; exact h2 z v hz
  · intro z hz
    by_cases e : z = y
    · subst e; left; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hz
      rcases h3 z hz with hz | hz
      · left; simp only [List.mem_append, List.mem_singleton] at hz ⊢
        rcases hz with hz | hz
        · exact Or.inl (Or.inl hz)
        · exact Or.inr hz
      · right; intro d hd
        obtain ⟨hd1, hd2⟩ := hz d hd
        refine ⟨hd1, ?_⟩
        by_cases e' : ofCmdId d = y
        · rw [e', GMap.lookup_insert_eq]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e')]; exact hd2

/-- The expanded `x` done (its dependencies seen, none `dst`). -/
theorem swift.dfs_done {k : sp.Kept} {src dst : swift.CommandId} {s : List swift.CommandId}
    {x : swift.CommandId} {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst (s ++ [x]) sm)
    (hx : ∀ d ∈ sp.kdeps k (toCmdId x), d ≠ toCmdId dst ∧ (sm !! ofCmdId d).isSome) :
    swift.dfsOk k src dst s sm := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨fun y hy => h1 y (by simp [hy]), h2, ?_⟩
  intro z hz
  rcases h3 z hz with hz' | hz'
  · simp only [List.mem_append, List.mem_singleton] at hz'
    rcases hz' with hz' | rfl
    · exact Or.inl hz'
    · exact Or.inr hx
  · exact Or.inr hz'

/-- `dst` found among the dependencies of the expanded `x`. -/
theorem swift.dfs_found {k : sp.Kept} {src dst : swift.CommandId} {s : List swift.CommandId}
    {x : swift.CommandId} {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst (s ++ [x]) sm)
    (hd : toCmdId dst ∈ sp.kdeps k (toCmdId x)) :
    sp.recReaches k (toCmdId src) (toCmdId dst) = true :=
  (sp.recReaches_iff k _ _).2 (swift.dfs_reach_of H (by simp) hd)

/-- The stack empty: `dst` is not reachable. -/
theorem swift.dfs_exit {k : sp.Kept} {src dst : swift.CommandId} {sm : GMap swift.CommandId Bool}
    (H : swift.dfsOk k src dst [] sm) : sp.recReaches k (toCmdId src) (toCmdId dst) = false := by
  obtain ⟨-, -, h3⟩ := H
  have closed : ∀ z, (z = src ∨ (sm !! z).isSome) →
      ∀ d ∈ sp.kdeps k (toCmdId z), d ≠ toCmdId dst ∧ (sm !! ofCmdId d).isSome := by
    intro z hz
    rcases h3 z hz with hz | hz
    · simp at hz
    · exact hz
  have key : ∀ y, Relation.TransGen (swift.reachRel k) (toCmdId src) y →
      y ≠ toCmdId dst ∧ (sm !! ofCmdId y).isSome := by
    intro y hy
    induction hy with
    | single h => exact closed src (Or.inl rfl) _ h
    | tail _ hbc ih =>
      have := closed (ofCmdId _) (Or.inr ih.2) _ (by simpa using hbc)
      exact this
  cases h : sp.recReaches k (toCmdId src) (toCmdId dst)
  · rfl
  · exact absurd rfl (key _ ((sp.recReaches_iff k _ _).1 h)).1

section rd
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- A read of an entry's dependency slice, owned or read-only. -/
theorem swift.depRead (o : Bool) (dsl : GoSlice) (l : List swift.CommandId) :
    (if o then iprop(dsl ↦* l ∗ ownSliceCap swift.CommandId dsl (DFrac.own 1))
      else iprop(dsl ↦*□ l) : IProp netDistGF) ⊢
    ∃ dq, dsl ↦*{dq} l ∗ (dsl ↦*{dq} l -∗ (if o then iprop(dsl ↦* l ∗
      ownSliceCap swift.CommandId dsl (DFrac.own 1)) else iprop(dsl ↦*□ l))) := by
  cases o
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro #H
    iexists DFrac.discard
    isplitr
    · iexact H
    · iintro -; iexact H
  · simp only [↓reduceIte]
    iintro ⟨H, Hc⟩
    iexists DFrac.own 1
    iframe H
    iintro H; iframe

end rd

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions]

end proof
end Perennial.github_com.imdea_software.swiftpaxos
