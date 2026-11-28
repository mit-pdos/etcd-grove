/-
Lean-first (no Rocq counterpart).

# Parity B2: the binding's commits raised to the in-memory ones (`liftC`)

A node's announced, unwritten commit (`MemCommit`, B 139: its last queued `mem`'s) is what a B1
lemma reads as the node's commit while other nodes have writes queued (`-parallel`). `liftC` is the
binding's state with each node's commit raised to it; with no `mem` queued it is the state itself
(`liftC_self`). Moved out of `B1Carry` so that the `Ready` contexts (`LdCtx`) can name it
(#33 parity B2, Sim round 10).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.GC

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

/-- With no `mem` queued, the in-memory commit is the disk's. -/
theorem memCommit_nil {S : AntCheck.State} {i : Nat} (hq : S.queue[i]! = []) :
    S.memCommit i = .ok (S.commitIndex[i]!) := by
  unfold AntCheck.State.memCommit; rw [hq]; rfl

/-- The binding's commits raised to the in-memory ones (`MemCommit`: the last queued `mem`'s) where
these are above: the state a B1 lemma reads `LeadCommitMsgOk` in while some node has an announced,
unwritten commit (a `-parallel` leader's requests are sent before their write). -/
def liftC (S : AntCheck.State) : AntCheck.State :=
  { S with commitIndex := S.commitIndex.mapIdx (fun i x =>
      match S.memCommit i with
      | .ok c => max x c
      | .error _ => x) }

theorem liftC_get (S : AntCheck.State) {i : Nat} (h : i < S.commitIndex.length) :
    (liftC S).commitIndex[i]! =
      match S.memCommit i with
      | .ok c => max (S.commitIndex[i]!) c
      | .error _ => S.commitIndex[i]! := by
  simp only [liftC, getElem!_pos (S.commitIndex.mapIdx _) i (by simpa using h),
    getElem!_pos S.commitIndex i h, List.getElem_mapIdx]

theorem le_liftC (S : AntCheck.State) (i : Nat) : S.commitIndex[i]! ≤ (liftC S).commitIndex[i]! := by
  by_cases h : i < S.commitIndex.length
  · rw [liftC_get S h]
    cases S.memCommit i
    · exact Int.le_refl _
    · exact Int.le_max_left _ _
  · have h' : ¬ i < (liftC S).commitIndex.length := by simpa [liftC] using h
    rw [getElem!_neg S.commitIndex i h, getElem!_neg _ i h']
    exact Int.le_refl _

theorem liftC_nil {S : AntCheck.State} {i : Nat} (hq : S.queue[i]! = []) :
    (liftC S).commitIndex[i]! = S.commitIndex[i]! := by
  by_cases h : i < S.commitIndex.length
  · rw [liftC_get S h, memCommit_nil hq]; simp
  · have h' : ¬ i < (liftC S).commitIndex.length := by simpa [liftC] using h
    rw [getElem!_neg S.commitIndex i h, getElem!_neg _ i h']

/-- With no `mem` queued anywhere, `liftC` is the state itself. -/
theorem liftC_self {S : AntCheck.State} (hq : ∀ i < S.commitIndex.length, S.queue[i]! = []) :
    liftC S = S := by
  have e : S.commitIndex.mapIdx (fun i x =>
      match S.memCommit i with
      | .ok c => max x c
      | .error _ => x) = S.commitIndex := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rw [List.getElem_mapIdx]
    have hc := memCommit_nil (hq i h2)
    rw [getElem!_pos S.commitIndex i h2] at hc
    rw [hc]; simp
  unfold liftC; rw [e]

end AntSim
end EtcdGrove
end Perennial
