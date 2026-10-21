/-
A leader's subterm is below its log's last index (2026-10-20, witness support).

`PSubOk ps`: at a leader, `uint.Z ps.sub < plogLastIndexZ ps.base ps.log`. Every protocol step
keeps it (`StepC.psubOk`, `StepR.psubOk`): a leader wins with the entry of subterm `0` appended
(`win`), and every new subterm comes with its entry (`newSub`); only a leader's log grows.
It is what `StepC.newSub`'s premise `uint.Z s.sub + 1 < 2 ^ 64` needs, from the log's bound.
It holds between steps only: inside `maybeStartNewSubterm` the new subterm is installed before
its entry is appended, and inside `becomeLeader` the node leads at its previous epoch, so it is
carried at the step boundaries (`ghostRest`, `StepGhostMode.lean`), not in the struct's
predicate.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.StepR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section psub
variable [FfiSyntax]

/-- A leader's subterm is below its log's last index. -/
def PSubOk (s : PState) : Prop :=
  s.role = .leader → uint.Z s.sub < plogLastIndexZ s.base s.log

theorem preadRespondAll_psub (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).role = s.role ∧ (preadRespondAll id s qs).sub = s.sub ∧
      (preadRespondAll id s qs).base = s.base ∧ (preadRespondAll id s qs).log = s.log := by
  obtain ⟨o, r, h⟩ := preadRespondAll_eq id s qs
  rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem StepC.psubOk {c : CfgM} {id : w64} {B : Int} {s : PState} {r : List Msg} {s' : PState}
    (H : StepC c id B s r s') : PSubOk s → PSubOk s' := by
  induction H
  case refl => exact fun h => h
  case trans ih1 ih2 => exact fun h => ih2 (ih1 h)
  all_goals
    intro h hl
    simp_all [PSubOk, psendMsgs, pappend, pwinState, pbecomeLeader, pbecomeFollower,
      pbecomeCandidate, padoptLeader, plogLastIndexZ, (preadRespondAll_psub _ _ _).1,
      (preadRespondAll_psub _ _ _).2.1, (preadRespondAll_psub _ _ _).2.2.1,
      (preadRespondAll_psub _ _ _).2.2.2]
  all_goals word

theorem StepR.psubOk {Adm : List EntryM → CCState → Prop} {dec : CCDec} {id : w64} {B : Int}
    {r : RState} {ms : List Msg} {r' : RState}
    (H : StepR Adm dec id B r ms r') : PSubOk r.p → PSubOk r'.p := by
  induction H
  case refl => exact fun h => h
  case trans ih1 ih2 => exact fun h => ih2 (ih1 h)
  all_goals
    intro h hl
    simp_all [PSubOk, psendMsgs, pappend, pwinState, pbecomeLeader, pbecomeFollower,
      pbecomeCandidate, padoptLeader, plogLastIndexZ, (preadRespondAll_psub _ _ _).1,
      (preadRespondAll_psub _ _ _).2.1, (preadRespondAll_psub _ _ _).2.2.1,
      (preadRespondAll_psub _ _ _).2.2.2]
  all_goals word

end psub

end EtcdGrove
end Perennial
