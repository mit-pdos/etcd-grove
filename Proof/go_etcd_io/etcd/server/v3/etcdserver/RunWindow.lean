/-
**A restarted member's first batch enters the replay window** (R2d probe, 2026-11-06; DRAFT, the
fragment of `run`'s proof for the first batch after a restart, `notes/restart-plan.md`, R2d-5).
Lean-first (no Rocq counterpart).

At a restart the backend's ghost log `A` runs to its consistent index, past Go's applied index `ai`
(the WAL snapshot's), and raft hands its first batch `ce` from `ai + 1`. Both are prefixes of the
cluster's committed log (`srvRLogLb`), so one extends the other (`srvRLogLb_prefix`): either the
batch lies inside the window (its entries the ghost log's next ones, no new entry) or it runs past
it (the ghost log Go's log and the replays, then the new entries). In both cases the batch starts
with the pending replays `A.drop ai` (`winOk A [] (A.drop ai) ce`, `applyAll.specBatch`'s window
premise, `D = []` at the restart) and the ghost log after it is committed
(`srvRLogLb γ (A ++ winNew …)`, `kvBatchW`'s first row): `run_firstBatch_window`. What is left of
`run_job_body`'s restart form needs R2d-2's `applyResC` at the restart (not drafted).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyWindow
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lists
variable [GooseExts]

/-- A batch inside the pending replays agrees with them. -/
theorem winAgree_of_prefix_l : ∀ (W ms : List EntryModel), ms <+: W → winAgree W ms
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | w :: W, m :: ms, h => by
      obtain ⟨h1, h2⟩ := List.cons_prefix_cons.1 h
      exact ⟨h1.symm, winAgree_of_prefix_l W ms h2⟩

/-- A batch past the pending replays agrees with them. -/
theorem winAgree_of_prefix_r : ∀ (W ms : List EntryModel), W <+: ms → winAgree W ms
  | [], _, _ => trivial
  | _ :: _, [], h => by simp at h
  | w :: W, m :: ms, h => by
      obtain ⟨h1, h2⟩ := List.cons_prefix_cons.1 h
      exact ⟨h1, winAgree_of_prefix_r W ms h2⟩

/-- A batch inside the pending replays has no new entry. -/
theorem winNew_of_prefix_l {α : Type} : ∀ (W ms : List α), ms <+: W → winNew W ms = []
  | [], ms, h => by simpa [winNew] using List.eq_nil_of_prefix_nil h
  | _ :: _, [], _ => rfl
  | _ :: W, _ :: ms, h => winNew_of_prefix_l W ms (List.cons_prefix_cons.1 h).2

/-- A batch past the pending replays: they and its new entries. -/
theorem winNew_of_prefix_r {α : Type} : ∀ (W ms : List α), W <+: ms → W ++ winNew W ms = ms
  | [], ms, _ => rfl
  | _ :: _, [], h => by simp at h
  | w :: W, m :: ms, h => by
      obtain ⟨h1, h2⟩ := List.cons_prefix_cons.1 h
      show w :: (W ++ winNew W ms) = m :: ms
      rw [h1, winNew_of_prefix_r W ms h2]

/-- The ghost index at the restart: Go's index and the pending replays, the ghost log's length. -/
theorem winGhost_restart (ai : w64) (A : List EntryModel) (hle : uint.nat ai ≤ A.length)
    (hA : (A.length : Int) < 2 ^ 64) :
    uint.Z (winGhost ai (A.drop (uint.nat ai))) = A.length := by
  have hn := uint_nat_eq ai
  cases hd : A.drop (uint.nat ai) with
  | nil =>
    have := List.length_drop (i := uint.nat ai) (l := A)
    rw [hd, List.length_nil] at this
    simp only [winGhost]; omega
  | cons d D' =>
    have := List.length_drop (i := uint.nat ai) (l := A)
    rw [hd] at this
    simp only [winGhost]
    rw [show ((d :: D').length : Int) = A.length - uint.nat ai by omega]
    word

end lists

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A restarted member's first batch in its window** (the R2d probe's `run` fragment): from the
backend's ghost log `A` and raft's handed log at Go's index (`A.take ai ++ ce`), both committed, the
batch starts with the pending replays `A.drop ai` (`winOk`, no replay done yet) and the ghost log
after it is committed. -/
theorem run_firstBatch_window (γ : ServerRaftNames) (ai : w64) (A ce : List EntryModel)
    (hle : uint.nat ai ≤ A.length) :
    srvRLogLb (GF := GF) γ A ∗ srvRLogLb γ (A.take (uint.nat ai) ++ ce) ⊢
      ⌜winOk A [] (A.drop (uint.nat ai)) ce⌝ ∗ srvRLogLb γ (A ++ winNew (A.drop (uint.nat ai)) ce) := by
  iintro ⟨#HA, #HL⟩
  ihave %Hp := srvRLogLb_prefix γ A (A.take (uint.nat ai) ++ ce) $$ [HA HL]
  · iframe HA HL
  have hsuf : ([] ++ A.drop (uint.nat ai)) <:+ A := by
    rw [List.nil_append]; exact List.drop_suffix _ _
  rcases Hp.symm with hp | hp
  · -- the batch inside the window
    have hce : ce <+: A.drop (uint.nat ai) := by
      have hp2 : A.take (uint.nat ai) ++ ce <+: A.take (uint.nat ai) ++ A.drop (uint.nat ai) := by
        rw [List.take_append_drop]; exact hp
      exact (List.prefix_append_right_inj _).1 hp2
    rw [winNew_of_prefix_l _ _ hce, List.append_nil]
    iframe HA
    ipureintro; exact ⟨hsuf, winAgree_of_prefix_l _ _ hce⟩
  · -- the batch past the window
    have hW : A.drop (uint.nat ai) <+: ce := by
      have hp2 : A.take (uint.nat ai) ++ A.drop (uint.nat ai) <+: A.take (uint.nat ai) ++ ce := by
        rw [List.take_append_drop]; exact hp
      exact (List.prefix_append_right_inj _).1 hp2
    have hG : A ++ winNew (A.drop (uint.nat ai)) ce = A.take (uint.nat ai) ++ ce :=
      calc A ++ winNew (A.drop (uint.nat ai)) ce
          = (A.take (uint.nat ai) ++ A.drop (uint.nat ai)) ++ winNew (A.drop (uint.nat ai)) ce := by
            rw [List.take_append_drop]
        _ = A.take (uint.nat ai) ++ ce := by rw [List.append_assoc, winNew_of_prefix_r _ _ hW]
    rw [hG]
    iframe HL
    ipureintro; exact ⟨hsuf, winAgree_of_prefix_r _ _ hW⟩

end laws

end EtcdGrove
end Perennial
