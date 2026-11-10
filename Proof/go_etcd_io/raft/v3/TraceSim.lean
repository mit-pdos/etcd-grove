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

/-- **A candidate's granted voters against raft's tally** (amendment A3, Q17 (d)): the
specification's `votesGranted` `g` is a set (`SetIds.mk L`) holding every voter raft's tally `votes`
counts as granting and only voters raft has heard from. Not equality: raft records a voter's first
response of a term only (`RecordVote`), the specification adds a voter on every granting response,
and a phantom refusal (Q14, of the voter's current term) can sit in flight beside the voter's real
grant, so no fact of the specification's state rules out a second response
(`notes/decisions.md`, "Amendment A3 (Q17)"); with this relation the specification's tally only ever
holds more granting voters than raft's, all of them responded, which is all its `BecomeLeader` reads
(`isQuorum`, monotone on subsets of the configuration: `tallyGranted_quorum`, given that raft's
voters are in it). -/
def TallyGranted (votes : GMap w64 Bool) (g : Etcdraft.SetIds) : Prop :=
  ∃ L : List Etcdraft.ID, g = Etcdraft.SetIds.mk L ∧
    (∀ k, votes !! k = some true → idAbs k ∈ L) ∧ (∀ x ∈ L, ∃ k v, votes !! k = some v ∧ idAbs k = x)

/-- Node `s` and its server `a` agree, at a hook point of the idle phase (revision 13's `R_i`):
term, role, vote, leader, log, commit index, configuration; the vote tally while a candidate (the
responded voters exactly, the granted ones up to `TallyGranted`: amendment A3);
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
    TallyGranted s.votes a.votesGranted) ∧
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

/-! ## The events' facts `Main` needs (Q13, 2026-11-09)

`Main`'s pure obligations (`tracecheck/MainPure.lean`, `mainPure`) take, of raft's events `L`, the
facts below; `simInv` keeps them all (`SimEvents`, `TraceSimGhost.lean`), each law of the
simulation's capability from its premise `TraceEv.Ok K e` (`TraceEv.OkBoot K e` for a bootstrap
line) on the events it may log (`TracedCap.lean`). Moved here from `MainPure.lean` (where they were
stated first, 2026-11-09) so that raft's simulation can state them. -/

section facts
variable [GooseExts]

-- `traceNumBound` (the bound on the events' numbers) moved to `Protocol/Model.lean` (Q8 stage 1 slice
-- 10), verbatim, so that raft's message facts can carry it.

/-- An event of a kind the workload logs outside a node's bootstrap (`Line.InScope` of its line):
not a configuration change (`ChangeConf`, P3), a restart (`InitState`, P1) or a snapshot sent
(`MsgSnap`, P2). -/
def TraceEv.InScope (e : TraceEv) : Prop :=
  TraceSim.gsStr e.name ≠ "ChangeConf" ∧ TraceSim.gsStr e.name ≠ "InitState" ∧
  (TraceSim.gsStr e.name = "SendAppendEntriesRequest" → ∀ m, e.msg = some m → TraceSim.gsStr m.typ ≠ "MsgSnap")

/-- An event's numbers below `K` (the time receipts bound terms and indices). -/
def TraceEv.NumsBelow (K : Nat) (e : TraceEv) : Prop :=
  uint.nat e.term < K ∧ uint.nat e.commit < K ∧ uint.nat e.logSize < K ∧
  ∀ m, e.msg = some m →
    uint.nat m.term < K ∧ uint.nat m.entries < K ∧ uint.nat m.logTerm < K ∧ uint.nat m.index < K ∧
    uint.nat m.commit < K ∧ uint.nat m.rejectHint < K

/-- An event's configuration lists within `n` (raft's: its configuration's voters, and an
`ApplyConfChange`'s new configuration's). -/
def TraceEv.ConfsWithin (n : Nat) (e : TraceEv) : Prop :=
  e.conf.1.length ≤ n ∧ ∀ c, e.propCC = some c → c.newconf.length ≤ n

/-- **What a law of the simulation's capability takes of an event it may log** (Q13): ASCII
(`ConvertEvents`' premise), in scope, its numbers below `traceNumBound`, its configuration lists
within `n` (the laws': the size of raft's configuration, the cluster's voters). -/
def TraceEv.Ok (n : Nat) (e : TraceEv) : Prop :=
  e.Ascii ∧ e.InScope ∧ e.NumsBelow traceNumBound ∧ e.ConfsWithin n

/-- **What the bootstrap lines' law takes of an event** (Q13): as `TraceEv.Ok`, but not in scope
(raft's `InitState` is a bootstrap line), and its log below `2^40` (`Etcdraft.bootLogBound`:
`NewTrace` allocates a bootstrap line's log, `BootLogsOk`). -/
def TraceEv.OkBoot (n : Nat) (e : TraceEv) : Prop :=
  e.Ascii ∧ e.NumsBelow traceNumBound ∧ e.ConfsWithin n ∧ uint.nat e.logSize < 2 ^ 40

theorem TraceEv.confsWithin_mono {n n' : Nat} {e : TraceEv} (hn : n ≤ n') (h : e.ConfsWithin n) :
    e.ConfsWithin n' :=
  ⟨Nat.le_trans h.1 hn, fun c hc => Nat.le_trans (h.2 c hc) hn⟩

namespace TraceSim

/-- Node `i` has logged only bootstrap-named lines in `L1` (`¬ TraceSim.booted L1 i`). -/
def Unbooted (L1 : List TraceEv) (i : Etcdraft.ID) : Prop :=
  ∀ x ∈ L1, ∀ ln, Etcdraft.parseLine 0 (evConv x) = .ok ln → ln.nid = i →
    Etcdraft.isBootstrapName ln.ev.name = true

/-- Event `e`, logged after `L1`, is in scope, or a bootstrap-named line of a node still in its
bootstrap segment (raft's `InitState` at `StartNode`, the only one in the workload). -/
def EvScopeOk (L1 : List TraceEv) (e : TraceEv) : Prop :=
  e.InScope ∨ (Etcdraft.isBootstrapName (gsStr e.name) = true ∧
    ∀ i, Etcdraft.parseID (gsStr e.nid) = some i → Unbooted L1 i)

/-- Every event of `L` is `EvScopeOk` after the events before it. -/
def ScopeOk (L : List TraceEv) : Prop := ∀ k (hk : k < L.length), EvScopeOk (L.take k) L[k]

theorem scopeOk_nil : ScopeOk [] := fun _ hk => absurd hk (Nat.not_lt_zero _)

/-- `ScopeOk` is kept event by event (a `simInv` clause). -/
theorem scopeOk_snoc (L : List TraceEv) (e : TraceEv) (h : ScopeOk L) (he : EvScopeOk L e) :
    ScopeOk (L ++ [e]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k L.length with hl | hl
  · rw [List.take_append_of_le_length (Nat.le_of_lt hl), List.getElem_append_left hl]
    exact h k hl
  · have hk' : k = L.length := by omega
    subst hk'
    rw [List.take_left' rfl, List.getElem_append_right (Nat.le_refl _)]
    simpa using he

/-- Event `e`, logged after `L1`: if it is bootstrap-named and its node unbooted (a line `bootstrapOf`
may flag, the last of which `NewTrace` allocates the log of), its log size is below `2^40`
(`Etcdraft.bootLogBound`). -/
def EvBootLogOk (L1 : List TraceEv) (e : TraceEv) : Prop :=
  Etcdraft.isBootstrapName (gsStr e.name) = true →
    (∀ i, Etcdraft.parseID (gsStr e.nid) = some i → Unbooted L1 i) → uint.nat e.logSize < 2 ^ 40

/-- Every event of `L` is `EvBootLogOk` after the events before it. -/
def BootLogsOk (L : List TraceEv) : Prop := ∀ k (hk : k < L.length), EvBootLogOk (L.take k) L[k]

theorem bootLogsOk_nil : BootLogsOk [] := fun _ hk => absurd hk (Nat.not_lt_zero _)

/-- `BootLogsOk` is kept event by event (a `simInv` clause). -/
theorem bootLogsOk_snoc (L : List TraceEv) (e : TraceEv) (h : BootLogsOk L) (he : EvBootLogOk L e) :
    BootLogsOk (L ++ [e]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k L.length with hl | hl
  · rw [List.take_append_of_le_length (Nat.le_of_lt hl), List.getElem_append_left hl]
    exact h k hl
  · have hk' : k = L.length := by omega
    subst hk'
    rw [List.take_left' rfl, List.getElem_append_right (Nat.le_refl _)]
    simpa using he

/-- A line not bootstrap-named allocates no log. -/
theorem evBootLogOk_of_name (L1 : List TraceEv) (e : TraceEv)
    (h : Etcdraft.isBootstrapName (gsStr e.name) = false) : EvBootLogOk L1 e := by
  intro hb; rw [h] at hb; cases hb

/-- **The facts `simInv` keeps of its events** (Q13; `Main`'s hypotheses on them, `mainPure`): ASCII
(`ConvertEvents`' premise), in scope or a node's bootstrap line (`ScopeOk`), the bootstrap lines'
logs below `2^40` (`BootLogsOk`), their numbers below `traceNumBound` and their configuration
lists within `n` (`simInv`'s: the number of voters). (Their count, `L.length`, is not a clause: it
is bounded by the run's steps, outside the simulation.) -/
def SimEvents (n : Nat) (L : List TraceEv) : Prop :=
  (∀ x ∈ L, x.Ascii) ∧ ScopeOk L ∧ BootLogsOk L ∧ (∀ x ∈ L, x.NumsBelow traceNumBound) ∧
  (∀ x ∈ L, x.ConfsWithin n)

theorem simEvents_nil (n : Nat) : SimEvents n [] :=
  ⟨by simp, scopeOk_nil, bootLogsOk_nil, by simp, by simp⟩

theorem forall_mem_snoc {P : TraceEv → Prop} (L : List TraceEv) (e : TraceEv) (h : ∀ x ∈ L, P x)
    (he : P e) : ∀ x ∈ L ++ [e], P x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · simp at hx; subst hx; exact he

/-- **`SimEvents` after a line of a law's events** (`TraceEv.Ok`), given its bootstrap log's
condition (a line not bootstrap-named: `evBootLogOk_of_name`; of a booted node:
`evBootLogOk_of_booted`). -/
theorem simEvents_snoc (n n' : Nat) (hn : n' ≤ n) (L : List TraceEv) (e : TraceEv) (h : SimEvents n L)
    (he : e.Ok n') (hb : EvBootLogOk L e) : SimEvents n (L ++ [e]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := he
  exact ⟨forall_mem_snoc L e h1 e1, scopeOk_snoc L e h2 (Or.inl e2), bootLogsOk_snoc L e h3 hb,
    forall_mem_snoc L e h4 e3, forall_mem_snoc L e h5 (TraceEv.confsWithin_mono hn e4)⟩

/-- **`SimEvents` after a node's bootstrap line** (`TraceEv.OkBoot`): bootstrap-named, its node
unbooted. -/
theorem simEvents_snoc_boot (n n' : Nat) (hn : n' ≤ n) (L : List TraceEv) (e : TraceEv)
    (h : SimEvents n L) (he : e.OkBoot n') (hbn : Etcdraft.isBootstrapName (gsStr e.name) = true)
    (hun : ∀ i, Etcdraft.parseID (gsStr e.nid) = some i → Unbooted L i) : SimEvents n (L ++ [e]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := he
  exact ⟨forall_mem_snoc L e h1 e1, scopeOk_snoc L e h2 (Or.inr ⟨hbn, hun⟩),
    bootLogsOk_snoc L e h3 (fun _ _ => e4),
    forall_mem_snoc L e h4 e2, forall_mem_snoc L e h5 (TraceEv.confsWithin_mono hn e3)⟩

end TraceSim

end facts


end EtcdGrove
end Perennial
