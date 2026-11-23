/-
A replay, on the model's handlers (which mirror `epaxos.go`), of the schedule of finding G1
(questions.md): `handlePrepareReply` finishes a recovery at ballot 6 after its replica promised
ballot 7 to another recovery; instance 0.0 is committed with a PUT at replica 1 and with a no-op
at replica 2. Messages are passed by hand (the broadcasts' `alive` reads as the schedule says).

With fix R-PROM mirrored in `hPrepareReply` (the recovery ends when `inst.bal > lastTriedBallot`),
the same schedule no longer commits the PUT at replica 1: its replies of ballot 6 arrive after
its promise of 7, so step 8 ends its recovery (status NONE, `bal` 7); only replica 2 commits.
(Without the fix the result was "replica 1: status 4 bal 6 cmds [1]; replica 2: status 4 bal 7
cmds [0]", the agreement violation.)
-/


import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.State

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model.G1

open Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

/-- The direct sends of a handler's outputs. -/
def sends (os : List Out) : List (Nat × Msg) :=
  os.filterMap (fun o => match o with | .send to m => some (to, m) | _ => none)

/-- The pending broadcast's message. -/
def bmsg (os : List Out) : Msg :=
  (os.filterMap (fun o => match o with | .bcast b => some b.m | _ => none)).headD default

def firstSend (os : List Out) : Msg := ((sends os).headD default).2

def put : Proposal := ⟨1, ⟨opPUT, 0, [7]⟩⟩
def other : Proposal := ⟨2, ⟨opPUT, 1, [8]⟩⟩
def x00 : InstId := ⟨0, 0⟩

def r0a := RState.init 0
-- 1. replica 0 proposes 0.0 = PUT (its PreAccepts: every alive read false, nothing sent)
def p1 := hPropose r0a [put]
-- 2. replica 0 proposes 0.1; its PreAccept reaches 1 and 2 (they learn crtInstance[0] = 1)
def p2 := hPropose p1.1 [other]
def r1a := (hMsg (RState.init 1) (bmsg p2.2)).1
def r2a := (hMsg (RState.init 2) (bmsg p2.2)).1
-- 3. replica 1 recovers 0.0 (ballot 6), 4. replica 2 recovers 0.0 (ballot 7)
def rec1 := hRecover r1a x00
def rec2 := hRecover r2a x00
-- 5. replica 1 handles Prepare(7) from 2: promises 7, replies NONE
def h5 := hMsg rec1.1 (bmsg rec2.2)
-- 6. replica 0 handles Prepare(6) (reports its PA vote at 0); 7. replica 4 handles Prepare(6)
def h6 := hMsg p2.1 (bmsg rec1.2)
def h7 := hMsg (RState.init 4) (bmsg rec1.2)
-- 8. replica 1 handles both replies: sub-case 5, Phase 1 at 6 (although it promised 7)
def h8a := hMsg h5.1 (firstSend h6.2)
def h8 := hMsg h8a.1 (firstSend h7.2)
-- 9. replicas 4 and 0 pre-accept at 6
def h9a := hMsg h7.1 (bmsg h8.2)
def h9b := hMsg h6.1 (bmsg h8.2)
-- 10. replica 1: slow path (Accept to 4 and 0)
def h10a := hMsg h8.1 (firstSend h9a.2)
def h10 := hMsg h10a.1 (firstSend h9b.2)
-- 11. 4 and 0 accept; 12. replica 1 commits
def h11a := hMsg h9a.1 (bmsg h10.2)
def h11b := hMsg h9b.1 (bmsg h10.2)
def h12a := hMsg h10.1 (firstSend h11a.2)
def h12 := hMsg h12a.1 (firstSend h11b.2)
-- 13. replica 3 handles Prepare(7)
def h13 := hMsg (RState.init 3) (bmsg rec2.2)
-- 14. replica 2 gets the replies of 1 and 3: sub-case 6, Phase 1 for a no-op at 7
def h14a := hMsg rec2.1 (firstSend h5.2)
def h14 := hMsg h14a.1 (firstSend h13.2)
-- 15. replicas 3 and 4 handle PreAccept(7)
def h15a := hMsg h13.1 (bmsg h14.2)
def h15b := hMsg h11a.1 (bmsg h14.2)
-- 16. replica 2: slow path; 3 and 4 accept; replica 2 commits
def h16a := hMsg h14.1 (firstSend h15a.2)
def h16 := hMsg h16a.1 (firstSend h15b.2)
def h17a := hMsg h15a.1 (bmsg h16.2)
def h17b := hMsg h15b.1 (bmsg h16.2)
def h18a := hMsg h16.1 (firstSend h17a.2)
def h18 := hMsg h18a.1 (firstSend h17b.2)

def summary (σ : RState) : String :=
  match σ.inst x00 with
  | some w => s!"status {w.status.toNat} bal {(sint.Z w.bal)} cmds {(w.cmds.getD []).map (fun c => c.op.toNat)}"
  | none => "none"

/-- info: "replica 1: status 0 bal 7 cmds []; replica 2: status 4 bal 7 cmds [0]" -/
#guard_msgs in
#eval s!"replica 1: {summary h12.1}; replica 2: {summary h18.1}"

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model.G1
