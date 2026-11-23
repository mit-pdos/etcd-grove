/-
Lean-first (no Rocq counterpart).

# The abstractions on a concrete schedule (#33 S3c step 5 / S4, smoke test)

The stream the harness (`examples/raft/antithesis/harness.go`) reports for one small honest schedule
of three nodes, built with `Abs.lean`'s report functions from the protocol data raft (v3.7, the
harness's configuration: `ElectionTick 10`, `HeartbeatTick 1`, pre-vote and check-quorum off,
synchronous storage) produces on it, and checked with the transcription (`AntCheck.run`): it must be
ACCEPTED (`smoke_accepts`). A test of the abstractions (field by field, the harness's order of
reports) against the binding before any proof uses them.

The schedule (each node's input, then its `drain`; a message not listed as received was dropped):
1. the three `boot`s (a fresh node's first `HasReady` is false: no `Ready`);
2. node 1's election timeout: `campaign` at term 1 (`ready` as candidate, two vote requests; its
   self-vote is stepped at `Advance`);
3. nodes 2 and 3 receive the requests: each adopts term 1, grants (`ready` with vote `raft1`, the
   grant sent after the write);
4. node 1 receives node 2's grant: wins (`ready` as leader with its empty entry at index 1, an
   append to each follower; the self-acknowledgement at `Advance`); node 3's grant then changes
   nothing (no report);
5. nodes 2 and 3 accept the append (`ready` with the entry, an acknowledgement of index 1);
6. node 1 receives node 2's acknowledgement: commits 1 (`ready` with commit 1, an empty append
   carrying it to node 2, `apply` of entry 1); then node 3's: node 3 leaves probing, a `send` of an
   empty append (no `ready`: nothing written);
7. node 2 receives the empty append: commits 1, acknowledges, applies;
8. a proposal `v1` at node 2 (a follower): forwarded to node 1 (`send` of a `prop`, term 0);
9. node 1 receives it: appends it at index 2 (`ready`), sends it to both followers;
10. node 1 ticks: heartbeats (commit `min(Match, committed)` = 1 for both);
11. node 3 receives its heartbeat: commits 1 (`CommitBeyondConfirmed`: within its acknowledgement
    of index 1 in term 1), answers, applies;
12. node 2 accepts entry 2 and acknowledges; node 1 receives it: commits 2, appends carrying the
    commit to both, applies entry 2.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Abs

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim
namespace Smoke

/-- No extension: the protocol data's types take the list as a parameter only. -/
local instance : GooseExts := ⟨[]⟩

def i1 : w64 := W64 1
def i2 : w64 := W64 2
def i3 : w64 := W64 3

/-- Node 1's empty entry of term 1 at index 1 (`pleaderEntry`), and the proposal `v1` as proposed
(`RawNode.Propose`: term and index 0) and as appended at index 2. -/
def e1 : EntryM := EntryM.mk (W64 1) (W64 1) (W32 0) []
def p1 : EntryM := EntryM.mk (W64 0) (W64 0) (W32 0) go!"v1"
def e2 : EntryM := EntryM.mk (W64 1) (W64 2) (W32 0) go!"v1"

/-- `campaign`'s requests (`Index: lastIndex 0, LogTerm 0`). -/
def vote12 : Msg := Msg.mk .vote i1 i2 (W64 1) false (W64 0) (W64 0) (W64 0) (W64 0) []
def vote13 : Msg := Msg.mk .vote i1 i3 (W64 1) false (W64 0) (W64 0) (W64 0) (W64 0) []
/-- The grants (`Term: m.Term`). -/
def vr21 : Msg := Msg.plain .voteResp i2 i1 (W64 1) false
def vr31 : Msg := Msg.plain .voteResp i3 i1 (W64 1) false
/-- The new leader's first appends (`Next` 1: `Index 0, LogTerm 0`, entry 1, commit 0). -/
def app12a : Msg := Msg.mk .app i1 i2 (W64 1) false (W64 0) (W64 0) (W64 0) (W64 0) [e1]
def app13a : Msg := Msg.mk .app i1 i3 (W64 1) false (W64 0) (W64 0) (W64 0) (W64 0) [e1]
/-- The acknowledgements (`Index: lastnewi`). -/
def ar21 : Msg := Msg.mk .appResp i2 i1 (W64 1) false (W64 1) (W64 0) (W64 0) (W64 0) []
def ar31 : Msg := Msg.mk .appResp i3 i1 (W64 1) false (W64 1) (W64 0) (W64 0) (W64 0) []
/-- The empty appends carrying commit 1 (`Index 1, LogTerm 1`). -/
def app12b : Msg := Msg.mk .app i1 i2 (W64 1) false (W64 1) (W64 1) (W64 1) (W64 0) []
def app13b : Msg := Msg.mk .app i1 i3 (W64 1) false (W64 1) (W64 1) (W64 1) (W64 0) []
def ar21b : Msg := Msg.mk .appResp i2 i1 (W64 1) false (W64 1) (W64 0) (W64 0) (W64 0) []
/-- The forwarded proposal (`stepFollower`: `To` the leader, term 0). -/
def prop21 : Msg := Msg.mk .propose i2 i1 (W64 0) false (W64 0) (W64 0) (W64 0) (W64 0) [p1]
/-- The appends of entry 2 (`Index 1, LogTerm 1`, commit 1). -/
def app12c : Msg := Msg.mk .app i1 i2 (W64 1) false (W64 1) (W64 1) (W64 1) (W64 0) [e2]
def app13c : Msg := Msg.mk .app i1 i3 (W64 1) false (W64 1) (W64 1) (W64 1) (W64 0) [e2]
/-- The heartbeats (`Commit: min(Match, committed)` = 1). -/
def hb12 : Msg := Msg.mk .heartbeat i1 i2 (W64 1) false (W64 0) (W64 0) (W64 1) (W64 0) []
def hb13 : Msg := Msg.mk .heartbeat i1 i3 (W64 1) false (W64 0) (W64 0) (W64 1) (W64 0) []
def hr31 : Msg := Msg.plain .heartbeatResp i3 i1 (W64 1) false
def ar21c : Msg := Msg.mk .appResp i2 i1 (W64 1) false (W64 2) (W64 0) (W64 0) (W64 0) []
/-- The empty appends carrying commit 2 (`Index 2, LogTerm 1`). -/
def app12d : Msg := Msg.mk .app i1 i2 (W64 1) false (W64 2) (W64 1) (W64 2) (W64 0) []
def app13d : Msg := Msg.mk .app i1 i3 (W64 1) false (W64 2) (W64 1) (W64 2) (W64 0) []

def tick : AntCheck.Str := go!"tick"
def recv : AntCheck.Str := go!"recv"
def propose : AntCheck.Str := go!"propose"
def w0 : w64 := W64 0
def w1 : w64 := W64 1
def w2 : w64 := W64 2

/-- The stream, in the order the harness records it. -/
def stream : List AntCheck.Event :=
  [ evBoot i1, evBoot i2, evBoot i3,
    -- 2. node 1 campaigns
    evReady i1 tick .candidate w1 i1 w0 [], evSend i1 tick vote12, evSend i1 tick vote13,
    -- 3. the grants
    evRecv i2 vote12, evReady i2 recv .follower w1 i1 w0 [], evSend i2 recv vr21,
    evRecv i3 vote13, evReady i3 recv .follower w1 i1 w0 [], evSend i3 recv vr31,
    -- 4. node 1 wins
    evRecv i1 vr21, evReady i1 recv .leader w1 i1 w0 [e1], evSend i1 recv app12a,
    evSend i1 recv app13a,
    -- 5. the followers accept
    evRecv i2 app12a, evReady i2 recv .follower w1 i1 w0 [e1], evSend i2 recv ar21,
    evRecv i3 app13a, evReady i3 recv .follower w1 i1 w0 [e1], evSend i3 recv ar31,
    -- 6. node 1 commits 1; node 3 leaves probing
    evRecv i1 ar21, evReady i1 recv .leader w1 i1 w1 [], evSend i1 recv app12b,
    evApply i1 recv [e1],
    evRecv i1 ar31, evSend i1 recv app13b,
    -- 7. node 2 commits 1
    evRecv i2 app12b, evReady i2 recv .follower w1 i1 w1 [], evSend i2 recv ar21b,
    evApply i2 recv [e1],
    -- 8. a proposal at node 2, forwarded
    evSend i2 propose prop21,
    -- 9. node 1 appends it
    evRecv i1 prop21, evReady i1 recv .leader w1 i1 w1 [e2], evSend i1 recv app12c,
    evSend i1 recv app13c,
    -- 10. heartbeats
    evSend i1 tick hb12, evSend i1 tick hb13,
    -- 11. node 3 commits 1 from its heartbeat
    evRecv i3 hb13, evReady i3 recv .follower w1 i1 w1 [], evSend i3 recv hr31,
    evApply i3 recv [e1],
    -- 12. node 2 accepts entry 2; node 1 commits 2
    evRecv i2 app12c, evReady i2 recv .follower w1 i1 w1 [e2], evSend i2 recv ar21c,
    evRecv i1 ar21c, evReady i1 recv .leader w1 i1 w2 [], evSend i1 recv app12d,
    evSend i1 recv app13d, evApply i1 recv [e2] ]

/-- info: Except.ok { kind := Perennial.EtcdGrove.AntCheck.Kind.accepted, k := 51, names := [] } -/
#guard_msgs in
#eval AntCheck.run cfg3 stream

/-- **The stream is accepted.** -/
theorem smoke_accepts : AntCheck.Accepts cfg3 stream := by decide +kernel

/-- A mutant, to see the check is not vacuous: node 3 reports commit 2 at its heartbeat (its log
has one entry). Rejected at that event (the 41st: `OnDisk`'s commit within the log, B 391). -/
def mutant : List AntCheck.Event :=
  stream.set 40 (evReady i3 recv .follower w1 i1 w2 [])

/-- info: Except.ok { kind := Perennial.EtcdGrove.AntCheck.Kind.rejected, k := 41, names := [] } -/
#guard_msgs in
#eval AntCheck.run cfg3 mutant

end Smoke
end AntSim
end EtcdGrove
end Perennial
