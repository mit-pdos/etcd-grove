/-
`handleCommit`'s well-formedness facts (`CommitWf`) from what the delivery's ghost step knows of
the pre-state (`deliverPre`, `ep_deliverB`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandleCommit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostDeliver

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem commitWf_of_pre [GooseExts] [GoGlobalContext] {fr i n : Nat} {σ : RState} {m : Commit}
    (h : deliverPre fr i n (.commit m) σ) : CommitWf i σ m := by
  obtain ⟨S, hS, hi, hfr, hidle, hσ, hm, hnd, -⟩ := h
  have hmem : Msg.commit m ∈ S.msgs fr i := by
    unfold Sys.msgs; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? hm))
  have hraw := (hS.1.2.1 fr i _ hmem).1 m.replica m.inst rfl
  refine ⟨?_, hraw.1, hraw.2.1, hraw.2.2.1, hraw.2.2.2, ?_, ?_⟩
  · rw [← hσ]; exact hS.1.1.1 i hi
  · -- the commands of a sent Commit are not empty (MODEL-REQUEST epaxos-2, `InvAux.cmdsNe`)
    exact hS.commit_cmds_ne hmem
  · -- an own instance a Commit names exists with its bookkeeping: if it did not, `hCommit`
    -- would create it without bookkeeping, and the post-state's `Inv.wf` (own instances have
    -- `lb`, `inv_step_deliver`) would fail
    intro hq
    cases hsome : (commitW0 σ m).lb with
    | some lb => show ((commitW0 σ m).lb).isSome = true; rw [hsome]; rfl
    | none =>
      exfalso
      have hS' := inv_step_deliver S fr i n _ hS hi hfr hidle hm hnd
      have hrep' : (S.deliver fr i n (.commit m)).rep i = (hCommit σ m).1 := by
        show (Sys.applyStep _ i ((hMsg (S.rep i) (.commit m)).1, (hMsg (S.rep i) (.commit m)).2)).rep i = _
        simp [hσ, hMsg]
      have hpost : ∃ w', (hCommit σ m).1.inst ⟨toN m.replica, toN m.inst⟩ = some w' ∧
          w'.lb = none := by
        by_cases h1 : stGe (commitW0 σ m).status stCOMMITTED = true ∨
            m.ballot.slt (commitW0 σ m).bal = true
        · rw [hCommit_early σ m h1]; exact ⟨commitW0 σ m, by simp [commitPre], hsome⟩
        · have h1a : stGe (commitW0 σ m).status stCOMMITTED = false := by
            cases h : stGe (commitW0 σ m).status stCOMMITTED <;> simp_all
          have h1b : m.ballot.slt (commitW0 σ m).bal = false := by
            cases h : m.ballot.slt (commitW0 σ m).bal <;> simp_all
          rw [hCommit_main σ m h1a h1b]
          refine ⟨commitInst σ m, ?_, ?_⟩
          · rw [updateCommitted_eq]; simp only []; rw [updateConflicts_eq]
            simp [RState.setInst]
          · unfold commitInst commitRp; rw [hsome]; split <;> simp [hsome]
      obtain ⟨w', hw', hlb'⟩ := hpost
      have hw'' : ((S.deliver fr i n (.commit m)).rep i).inst ⟨toN m.replica, toN m.inst⟩ =
          some w' := by rw [hrep']; exact hw'
      exact (hS'.1.1.2.1 i hi _ w' hw'').2.2.2.2.2.1 hq hlb'

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
