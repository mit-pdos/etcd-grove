/-
Lean-first (no Rocq counterpart). Trace-check's layer B, Draft (2026-11-09): the simulation of the
corrected `etcdraft.tla` (`etc/tla-fixes/`) by raft's traced cluster, its pure part
(`notes/trace-validation-sim.md`, revision 13, "The relation `R`").

- `evConv`: a raft `TraceEv` as the checker's `Event`, exactly as the harness's `ConvertEvents`
  (`examples/raft/tracecheck/main.go`) builds it: the corollary's `TraceAccepts` is of these;
- `roleAbs`, `entAbs`, `msgAbs`: raft's role, log entries and traced messages as the
  specification's values;
- `SimServerR`: a node's protocol state (`PState`) related to its server in the specification's
  state, at the hook points of the idle phase.

The ghost part (the trace and the specification's state in `simInv`, each node's share in
`simNode`, the message tokens) is `TraceSimGhost.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrace
public import Proof.go_etcd_io.raft.v3.Protocol.Model
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Tla.Check

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

variable [GooseExts]

/-! ## Events -/

/-- A Go string as the checker's (ASCII, a byte per character, as `strRel` relates them). -/
def gsStr (b : GoString) : String := String.mk (b.map (fun c => Char.ofNat c.toNat))

/-- A `uint64` as Go's `int(·)` converts it (two's complement). -/
def gInt (w : w64) : Int := sint.Z w

/-- A configuration change as `ConvertEvents` builds it: an empty list is omitted. -/
def ccConv (c : TraceCC) : Etcdraft.EventConfChange :=
  { changes := if c.changes.isEmpty then none
      else some (c.changes.map (fun p => ({ nid := gsStr p.1, action := gsStr p.2 } : Etcdraft.EventChange)))
    newconf := if c.newconf.isEmpty then none else some (c.newconf.map gsStr) }

/-- A raft event as the checker's (`ConvertEvents`): the properties present when the map has a
key (raft writes `cc`, `match`, `next`), with `cc` only when it holds a configuration change. -/
def evConv (e : TraceEv) : Etcdraft.Event :=
  { name := gsStr e.name, nid := gsStr e.nid,
    state := { term := gInt e.term, vote := gsStr e.vote, commit := gInt e.commit },
    role := gsStr e.role, log := gInt e.logSize, conf := (e.conf.1.map gsStr, e.conf.2.map gsStr),
    msg := e.msg.map (fun m =>
      { type := gsStr m.typ, term := gInt m.term, «from» := gsStr m.frm, to := gsStr m.to,
        entries := gInt m.entries, logTerm := gInt m.logTerm, index := gInt m.index,
        commit := gInt m.commit, vote := gsStr m.vote, reject := m.reject,
        rejectHint := gInt m.rejectHint }),
    prop := if e.propCC.isNone && e.propMatch.isNone && e.propNext.isNone then none
      else some { cc := e.propCC.map ccConv } }

/-! ## The specification's values of raft's -/

/-- A node's role. -/
def roleAbs : Role → Etcdraft.Role
  | .follower => Etcdraft.follower
  | .candidate => Etcdraft.candidate
  | .leader => Etcdraft.leader

/-- A node id as the specification's server (`nil` is 0, as raft's `None`). -/
def idAbs (w : w64) : Etcdraft.ID := uint.nat w

/-- The bootstrap configuration, as the specification's set. -/
def confAbs (C : List w64) : Etcdraft.SetIds := Etcdraft.SetIds.mk (C.map idAbs)

/-- The `k`-th entry of a log (1-indexed), `bl` the bootstrap log's length and `C` its voters:
a bootstrap entry is the configuration entry `newTrace` builds for it (`C`'s first `k` voters,
0010), any later one a client request of value 0 (`Replicate` lines: `ClientRequest(i, 0)`;
proposals' data is not traced). No other entry occurs (no configuration change: P3). -/
def entAbs (C : List w64) (bl : Nat) (k : Nat) (e : EntryM) : Etcdraft.Entry :=
  if k ≤ bl then { term := 1, type := .config, value := .conf (confAbs (C.take k)) [] }
  else { term := uint.Z e.Term', type := .value, value := .val 0 }

/-- A log as the specification's, from its first index `first` (1 for an uncompacted log). -/
def logAbs (C : List w64) (bl : Nat) (first : Nat) (l : List EntryM) : List Etcdraft.Entry :=
  l.mapIdx (fun k e => entAbs C bl (first + k) e)

/-- A traced message as the specification's (`none` for an untraced type). The traced types are
`traceSendMessage`'s: votes, appends, heartbeats, snapshots, their responses (and, with 0011,
pre-votes: not in the first theorem's workload). -/
def msgAbs (C : List w64) (bl : Nat) (m : Msg) : Option Etcdraft.Msg :=
  let base (t : Etcdraft.MsgType) : Etcdraft.Msg :=
    { type := t, term := uint.Z m.term, source := idAbs m.src, dest := idAbs m.dst }
  match m.ty with
  | .vote =>
    let b := base .requestVoteRequest
    some { b with lastLogIndex := uint.Z m.index, lastLogTerm := uint.Z m.logterm }
  | .voteResp =>
    let b := base .requestVoteResponse
    some { b with voteGranted := !m.reject }
  | .app =>
    let b := base .appendEntriesRequest
    some { b with
      subtype := "app"
      prevLogIndex := uint.Z m.index
      prevLogTerm := uint.Z m.logterm
      entries := logAbs C bl (uint.nat m.index + 1) m.entries
      commitIndex := uint.Z m.commit }
  | .heartbeat =>
    let b := base .appendEntriesRequest
    some { b with subtype := "heartbeat", commitIndex := uint.Z m.commit }
  | .appResp =>
    let b := base .appendEntriesResponse
    some { b with subtype := "app", success := !m.reject, matchIndex := if m.reject then 0 else uint.Z m.index }
  | .heartbeatResp =>
    let b := base .appendEntriesResponse
    some { b with subtype := "heartbeat", success := true }
  | _ => none

/-! ## A node and its server -/

/-- Node `s` and its server `a` agree, at a hook point of the idle phase (revision 13's `R_i`):
term, role, vote, leader, log, commit index, configuration; the vote tally while a candidate;
`matchIndex` while a leader (raft's `Match`, its own entry included); `pendingConfChangeIndex` 0
(no configuration change: P3). `durable` is not raft's (the node's last `Ready` line's,
`durableOf`), so it is the simulation's: not here. -/
def SimServerR (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) : Prop :=
  a.currentTerm = uint.Z s.term ∧ a.state = roleAbs s.role ∧ a.votedFor = idAbs s.vote ∧
  a.lead = idAbs s.lead ∧ uint.Z s.base.index' = 0 ∧ a.log = logAbs C bl 1 s.log ∧
  a.commitIndex = uint.Z s.commit ∧ a.config = { incoming := confAbs C, outgoing := [], learners := [] } ∧
  a.pendingConfChangeIndex = 0 ∧
  (s.role = .candidate →
    a.votesResponded = Etcdraft.SetIds.mk ((GMap.toList s.votes).map (fun p => idAbs p.1)) ∧
    a.votesGranted = Etcdraft.SetIds.mk (((GMap.toList s.votes).filter (fun p => p.2)).map (fun p => idAbs p.1))) ∧
  (s.role = .leader → ∀ j ∈ C, a.matchIndex (idAbs j) = uint.Z ((s.matched !! j).getD (W64 0)))

end TraceSim

section ascii
variable [GooseExts]

/-! ## ASCII events (`ConvertEvents`'s premise, `notes/trace-validation-plan.md`, S7) -/

/-- A Go string of ASCII bytes. -/
def gsAscii (b : GoString) : Prop := ∀ c ∈ b, c.toNat < 128

/-- An event whose strings `ConvertEvents` copies are ASCII (its configuration change field `cc`
and its `match`/`next` properties are not copied). -/
def TraceEv.Ascii (e : TraceEv) : Prop :=
  gsAscii e.name ∧ gsAscii e.nid ∧ gsAscii e.vote ∧ gsAscii e.role ∧
  (∀ s ∈ e.conf.1, gsAscii s) ∧ (∀ s ∈ e.conf.2, gsAscii s) ∧
  (∀ m, e.msg = some m → gsAscii m.typ ∧ gsAscii m.frm ∧ gsAscii m.to ∧ gsAscii m.vote) ∧
  (∀ c, e.propCC = some c → (∀ p ∈ c.changes, gsAscii p.1 ∧ gsAscii p.2) ∧ ∀ s ∈ c.newconf, gsAscii s)

end ascii


end EtcdGrove
end Perennial
