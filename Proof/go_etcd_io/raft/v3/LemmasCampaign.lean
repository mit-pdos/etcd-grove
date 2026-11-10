/-
Lean-first (no Rocq counterpart). `raft.campaign`'s role transition and its facts, moved out of the
proof file (`raft__campaign.lean`) on 2026-11-09 (trace-check Q8 stage 1 slice 5), so that the proof
file exposes only its `wp_proof` (CLAUDE.md, "Package APIs": `campRoleState_gh`, added by Q8 stage 0,
was a layout violation, `etc/gen-interface.py --layout`); on 2026-11-10 (slice 7) the messages
`campaign` sends (`vreqTy`, `vrespTy`, `vreqW32`, `vrespW32`, `campReq`, `campMsg`), which its spec's
send gate names.
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section helpers
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The role transition `campaign` makes, by `pre`. -/
def campRoleState (id : w64) (s : NState) (pre : Bool) : NState :=
  if pre then becomePrecandidate s else becomeCandidate id s

/-- (Q8 stage 0) The campaign's role change keeps the ghost (the trace mode). -/
theorem campRoleState_gh (id : w64) (s : NState) (pre : Bool) :
    (campRoleState id s pre).gh = s.gh := by
  cases pre <;> rfl

theorem campRoleState_logst (id : w64) (s : NState) (pre : Bool) :
    (campRoleState id s pre).logst = s.logst := by
  cases pre <;> rfl

/-- The message types `campaign` sends, by `pre` (`t = campaignPreElection`): the
request and the self-addressed response. -/
def vreqTy (pre : Bool) : MsgType := if pre then .preVote else .vote
def vrespTy (pre : Bool) : MsgType := if pre then .preVoteResp else .voteResp
def vreqW32 (pre : Bool) : w32 := if pre then MsgPreVote else MsgVote
def vrespW32 (pre : Bool) : w32 := if pre then MsgPreVoteResp else MsgVoteResp

/-- The request `campaign` sends voter `y`, carrying the entry id `e` that
`lastEntryID()` returned when it was built, and the `Context` `cl` (2026-10-13: the
leader-transfer marker, or nothing). -/
def campReq (pre : Bool) (id y T : w64) (e : entryID) (cl : List w8) : Msg :=
  Msg.mkV (vreqTy pre) id y T false e.index' e.term' (W64 0) (W64 0) [] [] cl

/-- The message `campaign` sends on behalf of voter `y`: the self-addressed response
when `y` is this node, a request otherwise. `send` panics on a self-addressed request,
which is exactly why the code splits these two cases. (Rocq's `cmsg f` takes a ghost
function `f` for the entry id of each request; every request carries the same one,
`L`, so here it is that entry id.) -/
def campMsg (pre : Bool) (id T : w64) (e : entryID) (cl : List w8) (y : w64) : Msg :=
  if y = id then Msg.plain (vrespTy pre) id id T false else campReq pre id y T e cl

end helpers

end EtcdGrove
end Perennial
