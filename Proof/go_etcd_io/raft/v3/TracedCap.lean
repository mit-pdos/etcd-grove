/-
Lean-first (no Rocq counterpart). Trace-check's S5 Draft's vocabulary (2026-11-09), moved verbatim out
of `TracedHooksDraft.lean` by Q8 stage 1 (slice 1, 2026-11-09) so that the specs of raft's hook
paths can state their traced case with it (the Draft imports those specs: `notes/decisions.md`,
"Q8 stage 1: the capability's gate"). Every statement here is the frozen Draft's (tag
`trace-check-frozen`), unchanged but for amendment A1 (below); the Draft keeps its `X.tracedSpec`
statements and imports this.

- `TraceFire tr tl E Q` (`TraceFireOpt`, `TraceFireN`; `traceFire_mono`), the events (`NodeEvOf`,
  `SendEvOf`/`MsgEvOf`, `CCEvOf`), the gates (`sendGate`, `recvGate`);
- the capability `trCapB`/`trCap` (`emp` untraced), the phase steps (`PhaseStep*`), the facts kept
  (`FxPres*`), the laws' statements (`trCap_fire*.statement`, proved in `TracedHooksGlobal.lean`);
- (Q8 stage 1) `trOwn`, the gate on what a hook reads only when traced, and the untraced
  instances (`trCapB_none`, `fxPresT_none`, `phaseBot`).

**Amended (Q13, 2026-11-09, amendment A1; to be re-frozen as `trace-check-frozen-a1`, pending):** the
seven laws' event premise `∀ e, E e → TraceEv.Ascii e` became `∀ e, E e → TraceEv.Ok (elements
c.incoming).length e` (`TraceEv.OkBoot` for `trCap_fire_boot`; `trCap_fire_bf`, which had none, gained
it), so that `simInv` keeps `Main`'s facts of the events (`SimEvents`, `TraceSim.lean`); `MsgEvOf`
gained `tm.rejectHint = m.rejecthint` (q13-r1's F1: Go writes the field, `TraceEv.Ok` bounds it), so
that every field `makeTracingMessage` writes is pinned but `Vote` (`SendEvOf`: some decimal; raft's
`Msg` has no vote, and no fact reads it). New lemmas, the premise's discharge from a state's and a
message's numbers: `nodeEvOf_ok`/`_okBoot` (with `nodeEvOf_numsBelow`/`_confsWithin`), `ccEvOf_ok`/
`_okBoot` (`ccEvOf_numsBelow`/`_confsWithin`), `sendEvOf_ok` (`sendEvOf_numsBelow`/`_confsWithin`,
`sendEvt_inScope`, `recvEvt_inScope`: a send and a receive line alike, `sendGate`/`recvGate`; the
message's numbers as one new definition, `Msg.NumsBelow`), `evtNames_inScope`. `trCapB`'s
configuration `c` is always the voters', raft's own whenever raft's tracker holds all the voters, not
while it grows from empty in `newRaft` and `Bootstrap` (A1's second repair, a docstring; the bootstrap
lines' gate takes the two apart, `trCapB_hookGate_bf`). The Draft's traced statements on the capability
(`TracedHooksDraft.lean`) take the same premise; no other statement here changed.

**Amended (A5, Q21; A6, Q22, 2026-11-11):** `simFx`'s `QuorumLogF` clause, now `QuorumKept` (A5: every
committed prefix kept from a term with raft's commit justification) with `AckHists` (A6: the
acknowledgements' histories, raft's `hist` over each acknowledging server's current log, keyed on the
specification's acknowledgements and leaders' match indices), so that a leader's `Commit` line keeps it
(`quorumLogF_commit`, `TracedQuorumLog.lean`; `notes/decisions.md`, "Amendment A6 (Q22, Q23)").
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.InvTrace
public import Proof.go_etcd_io.raft.v3.TraceSimLemmas
public import Proof.go_etcd_io.raft.v3.TraceSimGhost
public import Proof.go_etcd_io.raft.v3.TraceSimFacts
public import Proof.go_etcd_io.raft.v3.TraceSimSpecInv
public import Proof.strconv.FormatUintDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 TraceSim

/-! ## The events of raft's state -/

section pure
variable [GooseExts]

/-- `r.state.String()`. -/
def roleStr : PRole → GoString
  | .follower => go!"StateFollower"
  | .candidate => go!"StateCandidate"
  | .leader => go!"StateLeader"
  | .preCandidate => go!"StatePreCandidate"

/-- `stateMachineEventType.String()`: the event names, by their constant. -/
def evtNames : List GoString :=
  [go!"InitState", go!"BecomeCandidate", go!"BecomeFollower", go!"BecomeLeader", go!"Commit",
   go!"Replicate", go!"ChangeConf", go!"ApplyConfChange", go!"Ready", go!"SendAppendEntriesRequest",
   go!"ReceiveAppendEntriesRequest", go!"SendAppendEntriesResponse", go!"ReceiveAppendEntriesResponse",
   go!"SendRequestVoteRequest", go!"ReceiveRequestVoteRequest", go!"SendRequestVoteResponse",
   go!"ReceiveRequestVoteResponse", go!"SendSnapshot", go!"ReceiveSnapshot"]

/-- `rsmCommit`. -/
def rsmCommit : w64 := W64 4

/-- The node events `traceNodeEvent(evt, r)` may log at node `id` in state `s` and configuration
`c`: `traceEvent`'s `TracingEvent` with no message and no properties (`makeTracingState`: the hard
state's term, vote and commit; `lastIndex()`; each half's voters, `Slice()`'s permutation of them,
formatted). -/
def NodeEvOf (evt : w64) (id : w64) (s : NState) (c : CfgM) (e : TraceEv) : Prop :=
  evtNames[uint.nat evt]? = some e.name ∧
  e.nid = decStr id ∧ e.term = s.term ∧ e.vote = decStr s.vote ∧ e.commit = s.logst.committed ∧
  e.role = roleStr s.role ∧ e.logSize = plastIndex (toPState s) ∧
  (∃ xs ys : List w64, xs ≡ₚ elements c.incoming ∧ ys ≡ₚ elements c.outgoing ∧
    e.conf = (xs.map decStr, ys.map decStr)) ∧
  e.msg = none ∧ e.cc = none ∧ e.propCC = none ∧ e.propMatch = none ∧ e.propNext = none

/-- (Q8 stage 1, slice 3) A node event reads no `Progress`. -/
theorem nodeEvOf_prvals (evt id : w64) (s : NState) (p : GMap w64 Progress) (c : CfgM) :
    NodeEvOf evt id { s with prvals := p } c = NodeEvOf evt id s c := rfl

/-- Raft's traced messages of an outbox, as the specification's. -/
def pendAbs (C : List w64) (ob : List Msg) : List Etcdraft.Msg := ob.filterMap (TraceSim.msgAbs C C.length)

/-- **The idle relation**: node state `s` and the node's share, its server `c` and its pending
messages `P`, at a hook point of the idle phase (`notes/trace-validation-sim.md`, "Phases"): the
server is `R_i`-related to the protocol reading of `s` (`SimServerR`, the bootstrap log the `|C|`
configuration entries), the log uncompacted, `P` the outbox's traced messages, and the numbers the
line's parse reads as `int` below `2^63` (review round 1's F4). -/
def SimIdle (C : List w64) (s : NState) (c : ServerC) (P : List Etcdraft.Msg) : Prop :=
  ∃ a : Etcdraft.Server, toC (confAbs C) a = c ∧ SimServerR C C.length (toPState s) a ∧
    LogShapeOk C.length (toPState s) ∧ P = pendAbs C (toPState s).outbox ∧
    uint.Z s.term < 2 ^ 63 ∧ uint.Z s.logst.committed < 2 ^ 63 ∧ uint.Z (plastIndex (toPState s)) < 2 ^ 63

/-- The specification's `AdvanceCommitIndex` at a server `a` commits exactly to `n` (whatever the
rest of the state: it reads only the server's own variables). -/
def AdvancesTo (a : Etcdraft.Server) (n : Int) : Prop :=
  ∀ (st : Etcdraft.State) (i : Etcdraft.ID), st.s i = a →
    st.advanceCommitIndex i = some (st.commitTo i n)

/-- (Q8 stage 1, slice 3) **`r.maybeCommit()`'s outcome** (`b`, `N`): `N` is `r.trk.Committed()`, the
joint quorum index of the voters' `Match` values, and `b` is `raftLog.maybeCommit`'s test at
`(r.Term, N)` (a non-zero term, past the commit index, the log's term there `r.Term`). The traced
premises of `raft.maybeCommit.spec` quantify over it: the `Commit` line is of the state it gives. -/
def maybeCommitOut (c : CfgM) (s : NState) (b : Bool) (N : w64) : Prop :=
  JCommittedIdx c.incoming c.outgoing (pvsMatchAt s.prvals) N ∧
  (b = true ↔ (s.term ≠ W64 0 ∧ uint.Z s.logst.committed < uint.Z N ∧
    plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) N = some s.term))

/-- `MessageType.String()` of the traced types. -/
def msgTypeStr : MsgType → GoString
  | .vote => go!"MsgVote"
  | .voteResp => go!"MsgVoteResp"
  | .app => go!"MsgApp"
  | .appResp => go!"MsgAppResp"
  | .heartbeat => go!"MsgHeartbeat"
  | .heartbeatResp => go!"MsgHeartbeatResp"
  | _ => go!""

/-- The traced message `tm` of raft's message `m` (`makeTracingMessage`, a non-snapshot): every field
it writes but `Vote` (`SendEvOf`'s). Only for the traced types (`sendEvt m.ty ≠ none`, the gates'):
`msgTypeStr` names no other, so of a Go `MsgSnap` this is false. -/
def MsgEvOf (m : Msg) (tm : TraceMsg) : Prop :=
  tm.typ = msgTypeStr m.ty ∧ tm.term = m.term ∧ tm.frm = decStr m.src ∧ tm.to = decStr m.dst ∧
  tm.entries = W64 m.entries.length ∧ tm.logTerm = m.logterm ∧ tm.index = m.index ∧
  tm.commit = m.commit ∧ tm.reject = m.reject ∧ tm.rejectHint = m.rejecthint

/-- The events `traceSendMessage(r, m)` may log for a traced message `m` (`traceEvent` with the
message; its properties unconstrained). -/
def SendEvOf (evt : w64) (id : w64) (s : NState) (c : CfgM) (m : Msg) (e : TraceEv) : Prop :=
  evtNames[uint.nat evt]? = some e.name ∧
  e.nid = decStr id ∧ e.term = s.term ∧ e.vote = decStr s.vote ∧ e.commit = s.logst.committed ∧
  e.role = roleStr s.role ∧ e.logSize = plastIndex (toPState s) ∧
  (∃ xs ys : List w64, xs ≡ₚ elements c.incoming ∧ ys ≡ₚ elements c.outgoing ∧
    e.conf = (xs.map decStr, ys.map decStr)) ∧
  (∃ tm, e.msg = some tm ∧ MsgEvOf m tm) ∧ e.cc = none ∧
  -- what `makeTracingMessage` and `traceSendMessage` write besides (`ConvertEvents`'s ASCII premise)
  e.propCC = none ∧ ∀ tm, e.msg = some tm → ∃ v : w64, tm.vote = decStr v

/-- `traceSendMessage`'s event, by the message's type (`rsmSend*`); `none`: not traced (a snapshot
is `SendAppendEntriesRequest` in Go, never sent in a traced cluster, P2). -/
def sendEvt : MsgType → Option w64
  | .app | .heartbeat => some (W64 9)
  | .appResp | .heartbeatResp => some (W64 11)
  | .vote => some (W64 13)
  | .voteResp => some (W64 15)
  | _ => none

/-- `traceReceiveMessage`'s event, by the message's type (`rsmReceive*`). -/
def recvEvt : MsgType → Option w64
  | .app | .heartbeat => some (W64 10)
  | .appResp | .heartbeatResp => some (W64 12)
  | .vote => some (W64 14)
  | .voteResp => some (W64 16)
  | _ => none

/-- **`traceSendMessage`'s gate**: for a message of a traced type, the events it may log; `none` for
any other (an untyped one included: review round 1's F3). -/
def sendGate (id : w64) (s : NState) (c : CfgM) (ms : MsgSt) : Option (TraceEv → Prop) :=
  match mtypeOf ms.msg.Type' with
  | some ty => (sendEvt ty).map (fun evt => SendEvOf evt id s c (absMsg ty ms.msg ms.ents))
  | none => none

/-- **`traceReceiveMessage`'s gate** (every message `raft.Step` receives, local ones included: F2). -/
def recvGate (id : w64) (s : NState) (c : CfgM) (ms : MsgSt) : Option (TraceEv → Prop) :=
  match mtypeOf ms.msg.Type' with
  | some ty => (recvEvt ty).map (fun evt => SendEvOf evt id s c (absMsg ty ms.msg ms.ents))
  | none => none

/-- The normal entries of a batch (`traceReplicate` logs one `Replicate` per normal entry). -/
def normalCount (ents : List EntryM) : Nat := (ents.filter (fun e => decide (e.Type' = EntryNormal))).length

/-! ## A line's effect -/

/-- The message predicate a receive line applies (`receive`'s `isMatch`). -/
def recvPred (ln : Etcdraft.Line) (m : Etcdraft.Msg) : Bool :=
  if (or (ln.ev.name == "ReceiveAppendEntriesRequest") (ln.ev.name == "ReceiveSnapshot")) = true then
    ln.isAppendEntriesRequest m
  else if (ln.ev.name == "ReceiveAppendEntriesResponse") = true then ln.isAppendEntriesResponse m
  else if (ln.ev.name == "ReceiveRequestVoteRequest") = true then ln.isRequestVoteRequest m
  else ln.isRequestVoteResponse m

/-- `σ` with node `i`'s server `a'` and its bags transformed. -/
def withNode (σ : Etcdraft.State) (i : Etcdraft.ID) (a' : Etcdraft.Server) (fM fP : Etcdraft.Bag → Etcdraft.Bag) :
    Etcdraft.State :=
  Etcdraft.State.mk σ.server (fun j => if j = i then a' else σ.s j) (fM σ.messages) (fP σ.pendingMessages)
    σ.reconfigCount σ.preVote σ.checkQuorum

/-- **A line's effect** (`notes/trace-validation-sim.md`, "S5 Draft: the capability", and the
revision after it): node `i`'s line `e` takes server `a` to `a'` and the bags by `fM`, `fP`, in **every
trace and every state** where it could occur: the line (`e`'s) at `t.line l`, past the bootstrap,
the trace's servers the voters `C`, `BecomeFollower`'s skip the bit `bf`; the state's servers the
voters, node `i`'s server `a`, pre-vote and check-quorum off, for a receive line (`rcv = some m`)
`m` present and the only message the line matches; and the invariants holding at every state that
is `σ` with node `i`'s server of the shape `Mid` (the line's intermediate states: a term change, a
log prefix) and at the result. Then the search's rounds from the line's first state are a `Chain`
to the result (single fresh successors with the invariants). The global step supplies the
conditions (`simRun_lineEffect`). -/
def LineEffect (C : List w64) (bf : Bool) (e : TraceEv) (i : Etcdraft.ID) (a a' : Etcdraft.Server)
    (rcv : Option Etcdraft.Msg) (fM fP : Etcdraft.Bag → Etcdraft.Bag) (Mid : Etcdraft.Server → Prop) : Prop :=
  ∃ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln ∧ ln.nid = i ∧
  ∀ (t : Etcdraft.Trace) (l pl : Nat) (σ : Etcdraft.State),
    t.line l = ln → l ≠ 0 → l ≤ t.len → t.bootstrap.getD (l - 1) false = false → t.server = confAbs C →
    t.isBecomeFollowerInUpdateTermOrReturnToFollower ⟨σ, l, pl⟩ = bf →
    σ.server = confAbs C → σ.s i = a → σ.preVote = false → σ.checkQuorum = false →
    (match rcv with
     | none => True
     | some m => σ.messages.domain.Nodup ∧ m ∈ σ.messages.domain ∧ 0 < Etcdraft.Bag.count σ.messages m ∧
         ∀ m' ∈ σ.messages.domain, m' ≠ m → recvPred ln m' = false) →
    (∀ v, Mid v → (withNode σ i v _root_.id _root_.id).violated = .ok none) →
    (withNode σ i a' fM fP).violated = .ok none →
    ∃ tsF : Etcdraft.TState, tsF.s = withNode σ i a' fM fP ∧ Chain t l [⟨σ, l, pl⟩] ⟨σ, l, pl⟩ tsF

/-- `IsBecomeFollowerInUpdateTermOrReturnToFollower`'s test on the node's last line before it (`e0`)
and the line (`e`). -/
def bfCond (e0 e : Etcdraft.Event) : Bool :=
  match e0.msg with
  | none => false
  | some pm =>
    or (Etcdraft.isReceiveName e0.name && decide (e0.state.term < pm.term) && pm.term == e.state.term)
      (e0.name == "ReceiveAppendEntriesRequest" && e0.state.term == pm.term && pm.term == e.state.term &&
        (or (e0.role == Etcdraft.candidate) (e0.role == Etcdraft.preCandidate)))

/-! ### The events are ASCII (`ConvertEvents`'s premise; a `simInv` clause) -/

theorem gsAscii_decStr (n : w64) : gsAscii (decStr n) := by
  rw [decStr_eq]
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  have := baseDigits_lt 10 (by omega) n.toNat d hd
  unfold digitChar
  simp [W8, this]
  omega

theorem gsAscii_evtNames : ∀ x ∈ evtNames, gsAscii x := by
  simp only [evtNames, List.mem_cons, List.not_mem_nil, or_false, gsAscii]
  intro x hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem gsAscii_roleStr (r : PRole) : gsAscii (roleStr r) := by
  cases r <;> simp only [roleStr, gsAscii] <;> decide

theorem gsAscii_msgTypeStr (t : MsgType) : gsAscii (msgTypeStr t) := by
  cases t <;> simp only [msgTypeStr, gsAscii] <;> decide

theorem gsAscii_conf (xs : List w64) : ∀ x ∈ xs.map decStr, gsAscii x := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  exact gsAscii_decStr y

theorem nodeEvOf_ascii (evt id : w64) (s : NState) (c : CfgM) (e : TraceEv) (h : NodeEvOf evt id s c e) :
    TraceEv.Ascii e := by
  obtain ⟨hname, hnid, -, hvote, -, hrl, -, ⟨xs, ys, -, -, hconf⟩, hmsg, -, hcc, -, -⟩ := h
  refine ⟨gsAscii_evtNames _ (List.mem_of_getElem? hname), by rw [hnid]; exact gsAscii_decStr _,
    by rw [hvote]; exact gsAscii_decStr _, by rw [hrl]; exact gsAscii_roleStr _,
    by rw [hconf]; exact gsAscii_conf xs, by rw [hconf]; exact gsAscii_conf ys,
    (by intro m hm; rw [hmsg] at hm; cases hm), (by intro c hc; rw [hcc] at hc; cases hc)⟩

theorem sendEvOf_ascii (evt id : w64) (s : NState) (c : CfgM) (m : Msg) (e : TraceEv)
    (h : SendEvOf evt id s c m e) : TraceEv.Ascii e := by
  obtain ⟨hname, hnid, -, hvote, -, hrl, -, ⟨xs, ys, -, -, hconf⟩, ⟨tm, hmsg, hm⟩, -, hcc, hv⟩ := h
  refine ⟨gsAscii_evtNames _ (List.mem_of_getElem? hname), by rw [hnid]; exact gsAscii_decStr _,
    by rw [hvote]; exact gsAscii_decStr _, by rw [hrl]; exact gsAscii_roleStr _,
    by rw [hconf]; exact gsAscii_conf xs, by rw [hconf]; exact gsAscii_conf ys, ?_,
    (by intro c hc; rw [hcc] at hc; cases hc)⟩
  intro tm' htm
  rw [hmsg] at htm; cases htm
  obtain ⟨v, hv'⟩ := hv tm hmsg
  exact ⟨by rw [hm.1]; exact gsAscii_msgTypeStr _, by rw [hm.2.2.1]; exact gsAscii_decStr _,
    by rw [hm.2.2.2.1]; exact gsAscii_decStr _, by rw [hv']; exact gsAscii_decStr _⟩

/-- **The events `traceConfChangeEvent(cfg, r)` may log** (review round 3's B5): an `ApplyConfChange`
node event of `r`'s state (its configuration `c`, the old one at `switchToConfig`), its `cc`
property the new configuration `cn`'s voters (`formatConf(cfg.Voters[0].Slice())`, no changes). -/
def CCEvOf (id : w64) (s : NState) (c cn : CfgM) (e : TraceEv) : Prop :=
  evtNames[7]? = some e.name ∧
  e.nid = decStr id ∧ e.term = s.term ∧ e.vote = decStr s.vote ∧ e.commit = s.logst.committed ∧
  e.role = roleStr s.role ∧ e.logSize = plastIndex (toPState s) ∧
  (∃ xs ys : List w64, xs ≡ₚ elements c.incoming ∧ ys ≡ₚ elements c.outgoing ∧
    e.conf = (xs.map decStr, ys.map decStr)) ∧
  e.msg = none ∧ e.cc = none ∧
  (∃ ns : List w64, ns ≡ₚ elements cn.incoming ∧ e.propCC = some { changes := [], newconf := ns.map decStr }) ∧
  e.propMatch = none ∧ e.propNext = none

theorem ccEvOf_ascii (id : w64) (s : NState) (c cn : CfgM) (e : TraceEv) (h : CCEvOf id s c cn e) :
    TraceEv.Ascii e := by
  obtain ⟨hname, hnid, -, hvote, -, hrl, -, ⟨xs, ys, -, -, hconf⟩, hmsg, -, ⟨ns, -, hcc⟩, -, -⟩ := h
  refine ⟨gsAscii_evtNames _ (List.mem_of_getElem? hname), by rw [hnid]; exact gsAscii_decStr _,
    by rw [hvote]; exact gsAscii_decStr _, by rw [hrl]; exact gsAscii_roleStr _,
    by rw [hconf]; exact gsAscii_conf xs, by rw [hconf]; exact gsAscii_conf ys,
    (by intro m hm; rw [hmsg] at hm; cases hm), ?_⟩
  intro c' hc'
  rw [hcc] at hc'; cases hc'
  exact ⟨by simp, gsAscii_conf ns⟩

/-! ### (Q13) A node event as the laws take it (`TraceEv.Ok`, `TraceEv.OkBoot`) -/

/-- The event names but `InitState` and `ChangeConf` are in scope. -/
theorem evtNames_inScope : ∀ k : Fin evtNames.length, k.val ≠ 0 → k.val ≠ 6 →
    TraceSim.gsStr evtNames[k] ≠ "ChangeConf" ∧ TraceSim.gsStr evtNames[k] ≠ "InitState" := by
  decide

/-- A node event's numbers are its state's. -/
theorem nodeEvOf_numsBelow (evt id : w64) (s : NState) (c : CfgM) (e : TraceEv) (K : Nat)
    (h : NodeEvOf evt id s c e) (ht : uint.nat s.term < K) (hc : uint.nat s.logst.committed < K)
    (hl : uint.nat (plastIndex (toPState s)) < K) : e.NumsBelow K := by
  obtain ⟨-, -, hterm, -, hcommit, -, hlog, -, hmsg, -⟩ := h
  refine ⟨by rw [hterm]; exact ht, by rw [hcommit]; exact hc, by rw [hlog]; exact hl, ?_⟩
  intro m hm; rw [hmsg] at hm; cases hm

/-- A node event's configuration list is its configuration's voters. -/
theorem nodeEvOf_confsWithin (evt id : w64) (s : NState) (c : CfgM) (e : TraceEv) (n : Nat)
    (h : NodeEvOf evt id s c e) (hC : (elements c.incoming).length ≤ n) : e.ConfsWithin n := by
  obtain ⟨-, -, -, -, -, -, -, ⟨xs, ys, hxs, -, hconf⟩, -, -, hpcc, -⟩ := h
  refine ⟨by rw [hconf]; simp only [List.length_map]; rw [hxs.length_eq]; exact hC, ?_⟩
  intro c' hc'; rw [hpcc] at hc'; cases hc'

/-- **A node event of an in-scope kind (not `InitState`, 0, nor `ChangeConf`, 6), as the laws take
it** (`TraceEv.Ok n`, `n` at least its configuration's size): from its state's numbers below
`traceNumBound` (the caller's, from the time receipts). -/
theorem nodeEvOf_ok (evt id : w64) (s : NState) (c : CfgM) (e : TraceEv) (n : Nat)
    (h : NodeEvOf evt id s c e) (hevt : uint.nat evt ≠ 0 ∧ uint.nat evt ≠ 6)
    (ht : uint.nat s.term < traceNumBound) (hc : uint.nat s.logst.committed < traceNumBound)
    (hl : uint.nat (plastIndex (toPState s)) < traceNumBound) (hn : (elements c.incoming).length ≤ n) :
    e.Ok n := by
  refine ⟨nodeEvOf_ascii evt id s c e h, ?_, nodeEvOf_numsBelow evt id s c e _ h ht hc hl,
    nodeEvOf_confsWithin evt id s c e _ h hn⟩
  have hname := h.1
  have hmsg := h.2.2.2.2.2.2.2.2.1
  have hk : uint.nat evt < evtNames.length := (List.getElem?_eq_some_iff.1 hname).1
  obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.1 hname
  have hn := evtNames_inScope ⟨uint.nat evt, hk⟩ hevt.1 hevt.2
  simp only [Fin.getElem_fin] at hn
  rw [hk2] at hn
  exact ⟨hn.1, hn.2, fun _ m hm => by rw [hmsg] at hm; cases hm⟩

/-- **A node's bootstrap event, as the bootstrap law takes it** (`TraceEv.OkBoot n`, `n` at least its
configuration's size: during the bootstrap raft's configuration grows to the voters'): its numbers,
and its log below `2^40` (`Etcdraft.bootLogBound`; raft's bootstrap log is the voters' configuration
entries). -/
theorem nodeEvOf_okBoot (evt id : w64) (s : NState) (c : CfgM) (e : TraceEv) (n : Nat)
    (h : NodeEvOf evt id s c e) (ht : uint.nat s.term < traceNumBound)
    (hc : uint.nat s.logst.committed < traceNumBound)
    (hlb : uint.nat (plastIndex (toPState s)) < 2 ^ 40) (hn : (elements c.incoming).length ≤ n) :
    e.OkBoot n := by
  have hl : uint.nat (plastIndex (toPState s)) < traceNumBound := by unfold traceNumBound; omega
  refine ⟨nodeEvOf_ascii evt id s c e h, nodeEvOf_numsBelow evt id s c e _ h ht hc hl,
    nodeEvOf_confsWithin evt id s c e _ h hn, ?_⟩
  rw [h.2.2.2.2.2.2.1]; exact hlb

/-- A configuration-change event's numbers are its state's. -/
theorem ccEvOf_numsBelow (id : w64) (s : NState) (c cn : CfgM) (e : TraceEv) (K : Nat)
    (h : CCEvOf id s c cn e) (ht : uint.nat s.term < K) (hc : uint.nat s.logst.committed < K)
    (hl : uint.nat (plastIndex (toPState s)) < K) : e.NumsBelow K := by
  obtain ⟨-, -, hterm, -, hcommit, -, hlog, -, hmsg, -⟩ := h
  refine ⟨by rw [hterm]; exact ht, by rw [hcommit]; exact hc, by rw [hlog]; exact hl, ?_⟩
  intro m hm; rw [hmsg] at hm; cases hm

/-- A configuration-change event's lists are its old and new configurations' voters. -/
theorem ccEvOf_confsWithin (id : w64) (s : NState) (c cn : CfgM) (e : TraceEv) (n : Nat)
    (h : CCEvOf id s c cn e) (hn : (elements c.incoming).length ≤ n)
    (hn' : (elements cn.incoming).length ≤ n) : e.ConfsWithin n := by
  obtain ⟨-, -, -, -, -, -, -, ⟨xs, ys, hxs, -, hconf⟩, -, -, ⟨ns, hns, hcc⟩, -, -⟩ := h
  refine ⟨by rw [hconf]; simp only [List.length_map]; rw [hxs.length_eq]; exact hn, ?_⟩
  intro c' hc'; rw [hcc] at hc'; cases hc'
  simp only [List.length_map]; rw [hns.length_eq]; exact hn'

/-- **A bootstrap `ApplyConfChange` event, as the bootstrap law takes it** (`TraceEv.OkBoot n`): its
numbers, its log below `2^40`, its old and new configurations within `n`. -/
theorem ccEvOf_okBoot (id : w64) (s : NState) (c cn : CfgM) (e : TraceEv) (n : Nat)
    (h : CCEvOf id s c cn e) (ht : uint.nat s.term < traceNumBound)
    (hc : uint.nat s.logst.committed < traceNumBound)
    (hlb : uint.nat (plastIndex (toPState s)) < 2 ^ 40) (hn : (elements c.incoming).length ≤ n)
    (hn' : (elements cn.incoming).length ≤ n) : e.OkBoot n := by
  have hl : uint.nat (plastIndex (toPState s)) < traceNumBound := by unfold traceNumBound; omega
  refine ⟨ccEvOf_ascii id s c cn e h, ccEvOf_numsBelow id s c cn e _ h ht hc hl,
    ccEvOf_confsWithin id s c cn e n h hn hn', ?_⟩
  rw [h.2.2.2.2.2.2.1]; exact hlb

/-- **An `ApplyConfChange` event past the bootstrap, as the laws take it** (`TraceEv.Ok n`; the
application's after the first `Ready`): in scope (`ApplyConfChange` is neither `InitState` nor
`ChangeConf`), its numbers, its old and new configurations within `n`. -/
theorem ccEvOf_ok (id : w64) (s : NState) (c cn : CfgM) (e : TraceEv) (n : Nat)
    (h : CCEvOf id s c cn e) (ht : uint.nat s.term < traceNumBound)
    (hc : uint.nat s.logst.committed < traceNumBound)
    (hl : uint.nat (plastIndex (toPState s)) < traceNumBound) (hn : (elements c.incoming).length ≤ n)
    (hn' : (elements cn.incoming).length ≤ n) : e.Ok n := by
  have hname := h.1
  have hmsg := h.2.2.2.2.2.2.2.2.1
  have hk : 7 < evtNames.length := (List.getElem?_eq_some_iff.1 hname).1
  obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.1 hname
  have hsc := evtNames_inScope ⟨7, hk⟩ (show (7 : Nat) ≠ 0 by omega) (show (7 : Nat) ≠ 6 by omega)
  simp only [Fin.getElem_fin] at hsc
  rw [hk2] at hsc
  exact ⟨ccEvOf_ascii id s c cn e h, ⟨hsc.1, hsc.2, fun _ m hm => by rw [hmsg] at hm; cases hm⟩,
    ccEvOf_numsBelow id s c cn e _ h ht hc hl, ccEvOf_confsWithin id s c cn e n h hn hn'⟩

/-! ### (Q13, amendment A1) A send or receive event as the laws take it -/

/-- The events `traceSendMessage` logs (`sendEvt`) are in scope (neither `InitState` nor
`ChangeConf`). -/
theorem sendEvt_inScope (ty : MsgType) (evt : w64) (h : sendEvt ty = some evt) :
    uint.nat evt ≠ 0 ∧ uint.nat evt ≠ 6 := by
  cases ty <;> simp only [sendEvt, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> decide

/-- The events `traceReceiveMessage` logs (`recvEvt`) are in scope. -/
theorem recvEvt_inScope (ty : MsgType) (evt : w64) (h : recvEvt ty = some evt) :
    uint.nat evt ≠ 0 ∧ uint.nat evt ≠ 6 := by
  cases ty <;> simp only [recvEvt, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> decide

-- `Msg.NumsBelow` (a message's numbers below `K`) moved to `Protocol/Model.lean` (Q8 stage 1 slice 10),
-- verbatim, so that raft's message facts can carry it (`isMessageC`'s trace-gated conjunct).

/-- (Q8 stage 1 slice 10) A type `traceSendMessage` logs is a traced one (`MsgType.traced`). -/
theorem sendEvt_traced (ty : MsgType) (evt : w64) (h : sendEvt ty = some evt) : ty.traced = true := by
  cases ty <;> simp_all [sendEvt, MsgType.traced]

/-- (Q8 stage 1 slice 10) A type `traceReceiveMessage` logs is a traced one: what the message's
trace-gated fact (`Msg.TrOk`, `isMessageC`) covers. -/
theorem recvEvt_traced (ty : MsgType) (evt : w64) (h : recvEvt ty = some evt) : ty.traced = true := by
  cases ty <;> simp_all [recvEvt, MsgType.traced]

/-- A send or receive event's numbers: its state's and its message's (`MsgEvOf`'s fields). -/
theorem sendEvOf_numsBelow (evt id : w64) (s : NState) (c : CfgM) (m : Msg) (e : TraceEv) (K : Nat)
    (h : SendEvOf evt id s c m e) (ht : uint.nat s.term < K) (hc : uint.nat s.logst.committed < K)
    (hl : uint.nat (plastIndex (toPState s)) < K) (hm : m.NumsBelow K) : e.NumsBelow K := by
  obtain ⟨hmt, hme, hmlt, hmi, hmc, hmr⟩ := hm
  obtain ⟨-, -, hterm, -, hcommit, -, hlog, -, ⟨tm, hmsg, hm⟩, -⟩ := h
  refine ⟨by rw [hterm]; exact ht, by rw [hcommit]; exact hc, by rw [hlog]; exact hl, ?_⟩
  intro tm' htm; rw [hmsg] at htm; cases htm
  obtain ⟨-, h1, -, -, h2, h3, h4, h5, -, h6⟩ := hm
  refine ⟨by rw [h1]; exact hmt, ?_, by rw [h3]; exact hmlt, by rw [h4]; exact hmi,
    by rw [h5]; exact hmc, by rw [h6]; exact hmr⟩
  rw [h2]
  exact Nat.lt_of_le_of_lt (by word) hme

/-- A send or receive event's configuration list is its configuration's voters. -/
theorem sendEvOf_confsWithin (evt id : w64) (s : NState) (c : CfgM) (m : Msg) (e : TraceEv) (n : Nat)
    (h : SendEvOf evt id s c m e) (hC : (elements c.incoming).length ≤ n) : e.ConfsWithin n := by
  obtain ⟨-, -, -, -, -, -, -, ⟨xs, ys, hxs, -, hconf⟩, -, -, hpcc, -⟩ := h
  refine ⟨by rw [hconf]; simp only [List.length_map]; rw [hxs.length_eq]; exact hC, ?_⟩
  intro c' hc'; rw [hpcc] at hc'; cases hc'

/-- **A send or receive event, as the laws take it** (`TraceEv.Ok n`, `n` at least its configuration's
size; the event a gate's predicate allows, `sendGate`/`recvGate`, of an event `sendEvt_inScope` or
`recvEvt_inScope` puts in scope): from its state's numbers and its message's below `traceNumBound`
(the caller's: the state's from the time receipts; the message's, `Msg.NumsBelow`, a sent message's
from the state and the message it answers, a received one's from what its send line recorded: owed by
the Prove phase). In scope also by its message's type: `msgTypeStr` names no `MsgSnap`. -/
theorem sendEvOf_ok (evt id : w64) (s : NState) (c : CfgM) (m : Msg) (e : TraceEv) (n : Nat)
    (h : SendEvOf evt id s c m e) (hevt : uint.nat evt ≠ 0 ∧ uint.nat evt ≠ 6)
    (ht : uint.nat s.term < traceNumBound) (hc : uint.nat s.logst.committed < traceNumBound)
    (hl : uint.nat (plastIndex (toPState s)) < traceNumBound) (hm : m.NumsBelow traceNumBound)
    (hn : (elements c.incoming).length ≤ n) :
    e.Ok n := by
  refine ⟨sendEvOf_ascii evt id s c m e h, ?_,
    sendEvOf_numsBelow evt id s c m e _ h ht hc hl hm,
    sendEvOf_confsWithin evt id s c m e _ h hn⟩
  have hname := h.1
  obtain ⟨tm, hmsg, hmev⟩ := h.2.2.2.2.2.2.2.2.1
  have hk : uint.nat evt < evtNames.length := (List.getElem?_eq_some_iff.1 hname).1
  obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.1 hname
  have hsc := evtNames_inScope ⟨uint.nat evt, hk⟩ hevt.1 hevt.2
  simp only [Fin.getElem_fin] at hsc
  rw [hk2] at hsc
  refine ⟨hsc.1, hsc.2, fun _ tm' htm => ?_⟩
  rw [hmsg] at htm; cases htm
  rw [hmev.1]
  cases m.ty <;> simp only [msgTypeStr] <;> decide

/-- **A step-down's server** (`StepDownToFollower`, the specification's `BecomeFollowerOfTerm` at the
server's own term). -/
def bfSrv (a : Etcdraft.Server) : Etcdraft.Server :=
  { a with state := Etcdraft.follower, lead := Etcdraft.nil }

/-- **A phase step by a line consuming no message** (not a bootstrap-named line: not `BecomeFollower`,
whose skip bit only the node's previous line decides, review round 1's F6, so that the line is never
a bootstrap line, `bootFlags_nonBoot`): from every share `(cs, P)` in phase `Φ`,
each event `E` allows has, for every server `a` the share stands for, an effect into a share in
phase `Φ'` (review round 1's S2), its pending messages `P'` added. -/
def PhaseStep (id : w64) (c : CfgM) (E : TraceEv → Prop) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : Prop :=
  ∀ C cs P, Φ C cs P → (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C → ∀ e, E e →
    e.nid = decStr id ∧ Etcdraft.isBootstrapName (gsStr e.name) = false ∧
    ∀ a : Etcdraft.Server, toC (confAbs C) a = cs →
    ∃ (a' : Etcdraft.Server) (P' : List Etcdraft.Msg),
      Φ' C (toC (confAbs C) a') (P ++ P') ∧ (∀ x ∈ P', x.source = idAbs id) ∧
      LineEffect C false e (idAbs id) a a' none _root_.id (fun b => P'.foldl Etcdraft.Bag.with b) (fun _ => False)

end pure

/-! ## The capability -/

section gate
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! (Q8 stage 1, slice 2) The event builder's gate and the gate `trOwn`, at any `HasLC`: the hook specs
state them, and their callers' proofs are at any `HasLC`. -/

/-- **What a hook's caller gives the event builder**, by the cluster's trace mode: untraced, a nil
logger and `Q`; traced, the logger's contract and, for any event `e` the builder may log (`E e`),
the atomic update appending it to the trace and giving `Q`. -/
def TraceFire (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) : IProp GF :=
  match tr with
  | none => iprop(⌜TraceLoggerOk tl⌝ ∗ Q)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ isTraceLogger tn.tr tl ∗ ⌜tl ≠ interface.nil⌝ ∗
      ∀ e, ⌜E e⌝ -∗ AU <{ ∃∃ L, traceAuth tn.tr L }> @ ⊤, ∅ <{ traceAuth tn.tr (L ++ [e]), COMM Q }>)

/-- **What a hook's caller gives for an event that may or may not be logged**: `some E`, as
`TraceFire`; `none` (a message type the hook does not trace), `Q` (review round 1's S6). -/
def TraceFireOpt (tr : Option GName) (tl : GoInterface) (oE : Option (TraceEv → Prop)) (Q : IProp GF) :
    IProp GF :=
  match oE with
  | some E => TraceFire tr tl E Q
  | none => Q

/-- An atomic update's postcondition weakened (Rocq Iris's `atomic_update_wand`, absent from the
Lean port: `notes/perennial-changes.md`). -/
theorem aupd_wand_post {TA TB : Std.Tele} {Eo Ei : CoPset} {α : TA.Arg → IProp GF}
    {β Φ1 Φ2 : TA.Arg → TB.Arg → IProp GF} :
    iprop(atomic_update Eo Ei α β Φ1 ∗ (∀.. x, ∀.. y, Φ1 x y -∗ Φ2 x y)) ⊢ atomic_update Eo Ei α β Φ2 := by
  have h := aupd_intro (P := iprop(True))
    (Q := iprop(atomic_update Eo Ei α β Φ1 ∗ (∀.. x, ∀.. y, Φ1 x y -∗ Φ2 x y))) (α := α) (β := β)
    (Φ := Φ2) (Eo := Eo) (Ei := Ei) (by
      iintro ⟨-, ⟨HAU, HW⟩⟩
      ihave Hacc : atomic_acc Eo Ei α (atomic_update Eo Ei α β Φ1) β Φ1 $$ [HAU]
      · iapply aupd_aacc; iexact HAU
      iapply atomic_acc_wand $$ [HW] Hacc
      isplit
      · iintro HAU'; iframe
      · iexact HW)
  iintro H
  iapply h
  isplit
  · ipureintro; trivial
  · iexact H

/-- **`TraceFire`'s monotonicity** (review round 2's A10). -/
theorem traceFire_mono (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) (Q Q' : IProp GF) :
    iprop((Q -∗ Q') ∗ TraceFire tr tl E Q) ⊢ TraceFire tr tl E Q' := by
  cases tr with
  | none =>
    dsimp only [TraceFire]
    iintro ⟨HW, %Hok, HQ⟩
    isplitr; · ipureintro; exact Hok
    iapply HW $$ HQ
  | some γd =>
    dsimp only [TraceFire]
    iintro ⟨HW, %tn, Hd, Hl, %Hnn, HAU⟩
    iexists tn
    iframe Hd Hl
    isplitr; · ipureintro; exact Hnn
    iintro %e %HE
    iapply aupd_wand_post
    isplitl [HAU]
    · iapply HAU $$ %e %HE
    · isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
      iintro %L HQ
      iapply HW $$ HQ

/-- ... and `TraceFireOpt`'s. -/
theorem traceFireOpt_mono (tr : Option GName) (tl : GoInterface) (oE : Option (TraceEv → Prop))
    (Q Q' : IProp GF) :
    iprop((Q -∗ Q') ∗ TraceFireOpt tr tl oE Q) ⊢ TraceFireOpt tr tl oE Q' := by
  cases oE with
  | none => dsimp only [TraceFireOpt]; iintro ⟨HW, H⟩; iapply HW $$ H
  | some E => dsimp only [TraceFireOpt]; exact traceFire_mono tr tl E Q Q'

/-- **`n` events in a row** (`traceReplicate`'s loop), each `E`'s, the caller's updates nested. -/
def TraceFireN (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) : Nat → IProp GF → IProp GF
  | 0, Q => TraceFireOpt tr tl none Q
  | n + 1, Q => TraceFire tr tl E (TraceFireN tr tl E n Q)

/-- ... and so is the event builder's gate but the nil logger and `Q`. -/
theorem traceFire_none (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) :
    TraceFire (GF := GF) none tl E Q ⊣⊢ iprop(⌜TraceLoggerOk tl⌝ ∗ Q) := .rfl

/-! ## Q8 stage 1: one spec per function, for both modes (2026-11-09)

The Draft's capability is already mode-indexed: `trCapB tr …`, `trCap tr …`, `TraceFire tr …`,
`FxPresT tr …` and `FxPresUT tr …` are `emp`, `⌜TraceLoggerOk tl⌝ ∗ Q`, `True` and `|==> R'` when
`tr = none` (by their `match`), so a hook-path spec stated with them at `s.gh.tr` is one spec for
both modes, whose untraced instance is the stage-0 spec. No wrapper over them is needed
(`notes/decisions.md`, "Q8 stage 1: the capability's gate"). What stage 1 adds is the gate `trOwn`
on what a hook reads only to build a traced event (raft's state, the message), so that an untraced
caller, which may hold the struct open (`send`'s queue accessor, `switchToConfig`'s tracker), keeps
calling the hook as before; and the untraced instances below. -/

/-- **What a hook reads only when traced** (Q8 stage 1): `P` in a traced cluster, nothing in an
untraced one, whose hooks return at the nil check. A hook-path spec takes raft's state for its
event under it (`trOwn s.gh.tr (ownRaftPhysCV …)`), and gives it back the same way. -/
def trOwn (tr : Option GName) (P : IProp GF) : IProp GF :=
  match tr with
  | none => iprop(emp)
  | some _ => P

theorem trOwn_none (P : IProp GF) : trOwn (GF := GF) none P ⊣⊢ iprop(emp) := .rfl

theorem trOwn_some (γd : GName) (P : IProp GF) : trOwn (GF := GF) (some γd) P ⊣⊢ P := .rfl

/-- An untraced caller supplies the gate with nothing. -/
theorem trOwn_none_intro (P : IProp GF) : ⊢ trOwn (GF := GF) none P := by
  exact .rfl

/-- The gate is monotone. -/
theorem trOwn_wand (tr : Option GName) (P P' : IProp GF) :
    iprop((P -∗ P') ∗ trOwn tr P) ⊢ trOwn tr P' := by
  cases tr with
  | none => simp only [trOwn]; iintro ⟨-, H⟩; iexact H
  | some _ => simp only [trOwn]; iintro ⟨HW, H⟩; iapply HW $$ H

instance trOwn_persistent (tr : Option GName) (P : IProp GF) [Persistent P] :
    Persistent (trOwn (GF := GF) tr P) := by
  cases tr <;> simp only [trOwn] <;> infer_instance

/-- (Q8 stage 1, slice 2) An untraced caller, whose node's mode is `none` (`s.gh.tr = none`),
supplies the gate with nothing ... -/
theorem trOwn_of_none {tr : Option GName} (h : tr = none) (P : IProp GF) : ⊢ trOwn tr P := by
  subst h; exact trOwn_none_intro P

/-- ... and the event builder's gate with the nil logger and `Q`. -/
theorem traceFire_of_none {tr : Option GName} (h : tr = none) (tl : GoInterface) (E : TraceEv → Prop)
    (Q : IProp GF) : iprop(⌜TraceLoggerOk tl⌝ ∗ Q) ⊢ TraceFire tr tl E Q := by
  subst h; exact (traceFire_none tl E Q).2

/-- (Q8 stage 1, slice 2) At a nil logger the gate gives `Q` whatever the mode (a traced node's
logger is never nil): `traceInitState`'s own nil check. -/
theorem traceFire_nil (tr : Option GName) (E : TraceEv → Prop) (Q : IProp GF) :
    TraceFire tr interface.nil E Q ⊢ Q := by
  cases tr with
  | none => dsimp only [TraceFire]; iintro ⟨-, HQ⟩; iexact HQ
  | some γd =>
    dsimp only [TraceFire]
    iintro ⟨%tn, -, -, %Hnn, -⟩
    exact absurd rfl Hnn

/-- (Q8 stage 1, slice 2) The gate for fewer events. -/
theorem traceFire_mono_E (tr : Option GName) (tl : GoInterface) (E E' : TraceEv → Prop) (Q : IProp GF)
    (h : ∀ e, E' e → E e) : TraceFire tr tl E Q ⊢ TraceFire tr tl E' Q := by
  cases tr with
  | none => exact .rfl
  | some γd =>
    dsimp only [TraceFire]
    iintro ⟨%tn, Hd, Hl, %Hnn, HAU⟩
    iexists tn
    iframe Hd Hl
    isplitr
    · ipureintro; exact Hnn
    iintro %e %He
    iapply HAU $$ %e []
    ipureintro; exact h e He

/-- (Q8 stage 1, slice 2) `n` untraced events: the nil logger and `Q`. -/
theorem traceFireN_of_none {tr : Option GName} (h : tr = none) (tl : GoInterface) (E : TraceEv → Prop)
    (Hok : TraceLoggerOk tl) (Q : IProp GF) : ∀ n, Q ⊢ TraceFireN tr tl E n Q
  | 0 => by simp only [TraceFireN, TraceFireOpt]; exact .rfl
  | n + 1 => by
    simp only [TraceFireN]
    iintro HQ
    iapply traceFire_of_none h
    isplitr
    · ipureintro; exact Hok
    iapply traceFireN_of_none h tl E Hok Q n $$ HQ

/-- (Q8 stage 1, slice 2) What a caller holds whole, put under the gate and taken back: the Draft's
traced statements (which take raft's state in both modes) from the gated specs. -/
theorem trOwn_split (tr : Option GName) (P : IProp GF) : P ⊢ trOwn tr P ∗ (trOwn tr P -∗ P) := by
  cases tr with
  | none => simp only [trOwn]; iintro HP; isplitr; · iempintro
            iintro -; iexact HP
  | some _ => simp only [trOwn]; iintro HP; iframe HP; iintro H; iexact H

/-- (Q8 stage 1, slice 3) The gate on the caller's struct at another voter set `V`, which a traced
node's is not (`tr ≠ none → V = c.voters`: the hook's event reads the configuration's voters). -/
theorem trOwn_split_V [StorageModel GF] [go_etcd_io.raft.v3.Assumptions]
    (tr : Option GName) (c : CfgM) (V : GSet w64) (r : Loc) (id : w64) (s : NState)
    (hV : tr ≠ none → V = c.voters) :
    ownRaftPhysCV (GF := GF) c V r id s ⊢
      trOwn tr (ownRaftPhysCV c c.voters r id s) ∗
        (trOwn tr (ownRaftPhysCV c c.voters r id s) -∗ ownRaftPhysCV c V r id s) := by
  cases tr with
  | none => simp only [trOwn]; iintro HP; isplitr; · iempintro
            iintro -; iexact HP
  | some γd =>
    have hV' : V = c.voters := hV (Option.some_ne_none γd)
    subst hV'
    simp only [trOwn]; iintro HP; iframe HP; iintro H; iexact H

/-- (Q8 stage 1, slice 3) **A node-event hook's gate, the caller's** (the node-event hooks' direct
callers take it: `notes/decisions.md`, "Q8 stage 1 (slice 3)"): an update at `⊤`, run at the hook,
giving the logger field and the event builder's gate `TraceFire tr tl E Q` for the events `E` the
hook logs there. In a traced cluster the simulation's capability gives it, by the law of the line
(`trCapB_hookGate`, `TracedHooksGlobal.lean`), with `Q` the capability in its next phase; in an
untraced one the struct's nil logger does, with `Q` any resource the caller holds (`hookGate_none`). -/
def HookGate (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (Q : IProp GF) : IProp GF :=
  iprop(|={⊤}=> ∃ tl, r.[raft, go!"traceLogger"] ↦□ tl ∗ TraceFire tr tl E Q)

/-- The gate after an update at `⊤`. -/
theorem hookGate_fupd (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (Q : IProp GF) :
    iprop(|={⊤}=> HookGate tr r E Q) ⊢ HookGate tr r E Q := by
  iintro H
  iunfold HookGate at H
  iunfold HookGate
  imod H with H
  iexact H

/-- An untraced caller's gate: the struct's nil logger and `Q`. -/
theorem hookGate_none (r : Loc) (E : TraceEv → Prop) (tl : GoInterface) (Q : IProp GF)
    (hok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl ∗ Q : IProp GF) ⊢ HookGate none r E Q := by
  iintro ⟨#Htl, HQ⟩
  iunfold HookGate
  imodintro
  iexists tl
  isplitr
  · iexact Htl
  simp only [TraceFire]
  iframe HQ
  ipureintro; exact hok

end gate

set_option hygiene false in
/-- (Q8 stage 1, slice 2) An untraced call of a node-event hook (`traceBecome*`, `traceCommit`,
`traceReady`: `X.spec`'s `c r id s tl Q`) where `Hphys : ownRaftPhysCV c V r id _` is held whole and
the caller's state `s` is untraced (`tr_none`): the logger field and its contract read from it, the
gate `trOwn` and the event builder's gate `TraceFire` supplied at the nil logger (`Q := True`). The
hook's spec is instantiated at the caller's `c r id s` (any state of the node's mode will do, the
gate being `emp`). -/
macro "wp_node_hookC " h:term:max : tactic => `(tactic| (
  icases Perennial.EtcdGrove.ownRaftPhysC_traceLogger _ _ _ _ (by tr_none) $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  wp_apply ($h) c r id s tl iprop(True) $$ [Htl] as -
  · isplitr
    · iexact Htl
    isplitr
    · iapply Perennial.EtcdGrove.trOwn_of_none (by tr_none)
    iapply Perennial.EtcdGrove.traceFire_of_none (by tr_none)
    isplitr
    · ipureintro; exact Htlok
    itrivial
  iclear Htl))

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The simulation's invariant's namespace, beside raft's commit invariant's (`raftLogN`, `raftRegN`). -/
def simNS (γ : RaftNames) : Namespace := (raftN γ).@"tracesim"

/-- (Amendment A5, Q21) **The servers not known to keep `P` from term `t` on**: of the state's
servers, those whose log does not extend `P` or whose term is below `t`. -/
def lackingAt (σ : Etcdraft.State) (P : List Etcdraft.Entry) (t : Int) : List Etcdraft.ID :=
  σ.server.filter (fun j => or (!Etcdraft.isPrefix P (σ.s j).log) (decide ((σ.s j).currentTerm < t)))

/-- (Amendment A5, Q21) **`P` is kept from term `t` on**: the servers that hold `P` at a term at least
`t` are a quorum of the servers (those that lack it or are below `t` are none). With `t` a term `P` was
committed at or after (`CommitCert`), such a server never loses `P`: it truncates only on accepting an
append request of its own term, so of a term at least `t`, from that term's leader, whose log raft's
leader completeness (`lc_core`) puts the commit quorum's log, so `P`, in; the request agrees with `P` and
its first conflict is past `P` (the receiver's raft facts of the request, `commitCert_app` and
`quorumLogF_conflict`, `TracedQuorumLog.lean`). It is the inductive form of `QuorumLogInv`'s fact
(`quorumLogF_quorumLogS`): a server below `t` may hold `P` by coincidence and truncate it
(`notes/decisions.md`, "Q8 stage 1 (slice 22b)"), but it is not counted. -/
def KeptFrom (σ : Etcdraft.State) (P : List Etcdraft.Entry) (t : Int) : Prop :=
  Etcdraft.isQuorum (lackingAt σ P t) σ.server = false

/-- (Amendment A5, Q21) **`P` is committed at a term at most `t`**: `P` is a prefix of a log `es`
(read by `logAbs`, with its records) up to an index `c` that raft's commit justification covers at a
term at most `t` (`commitJ`: within the bootstrap log, or a commit quorum `cq` of a term `≤ t` whose log
has `es`'s term at `c`). With it the log of any leader of a term `T ≥ t` agrees with `P` (`lc_core`), so
does an append request of `T` (`commitCert_app`, `TracedQuorumLog.lean`). -/
def CommitCert (γ : RaftNames) (C : List w64) (P : List Etcdraft.Entry) (t : Int) : IProp GF :=
  iprop(∃ (es : List EntryM) (c : w64),
    ⌜P <+: logAbs C C.length 1 (es.take (uint.nat c)) ∧ PlogWf base0 es ∧ uint.Z c ≤ es.length ∧
      es.length < 2 ^ 63 ∧ 0 ≤ t ∧ t < 2 ^ 63⌝ ∗
    logRecs γ base0 es ∗ commitJ γ es c (W64 t))

instance commitCert_persistent (γ : RaftNames) (C : List w64) (P : List Etcdraft.Entry) (t : Int) :
    Persistent (CommitCert (GF := GF) γ C P t) := by
  unfold CommitCert; infer_instance

instance commitCert_timeless (γ : RaftNames) (C : List w64) (P : List Etcdraft.Entry) (t : Int) :
    Timeless (CommitCert (GF := GF) γ C P t) := by
  unfold CommitCert; infer_instance

/-- (Amendment A5, Q21) **The committed prefixes, kept**: every server's committed prefix is kept from
some term `t` on (`KeptFrom`), `t` a term it was committed at or after (`CommitCert`). `QuorumLogInv`
follows (`quorumLogF_quorumLogS`). (Until amendment A6 this was all of `QuorumLogF`.) -/
def QuorumKept (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop(□ ∀ i, ⌜i ∈ σ.server⌝ → ∃ t, ⌜KeptFrom σ (committedL σ i) t⌝ ∗ CommitCert γ C (committedL σ i) t)

instance quorumKept_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Persistent (QuorumKept (GF := GF) γ C σ) := by
  unfold QuorumKept; infer_instance

instance quorumKept_timeless (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Timeless (QuorumKept (GF := GF) γ C σ) := by
  unfold QuorumKept; infer_instance

/-- (Amendment A6, Q22) **An acknowledgement in flight**: a successful append response to another
server with a positive match index (the specification's `HandleAppendEntriesResponse` raises its
destination's match index for its source to it, `respSrv`). A leader's response to itself
(`AppendEntriesToSelf`) is not one: a leader's own log needs no history. -/
def AckMsg (x : Etcdraft.Msg) : Prop :=
  x.type = .appendEntriesResponse ∧ x.success = true ∧ x.source ≠ x.dest ∧ 0 < x.matchIndex

/-- (Amendment A6, Q22) **Server `k`'s acknowledgement of index `m` at term `T`, with its history over
`k`'s current log**: `k` is at a term at least `T`, and every raft log `F` that `k`'s log abstracts
(`logAbs`, its bootstrap entries of term 1) has raft's history of the acknowledgement `(T, m)`
(`hist`, `Protocol/Ghost.lean`; its bound on the leaders' terms is immaterial, `hist_mono`, so left to
each establishing lemma): at every index `j ≤ m`, `F` has
the term some `okL` log has there (a full log of a leader of a term `≥ T`, a committed log of an
earlier term, or the bootstrap log), or two such logs already disagree at or below `j`. It is raft's
`histsOk` (`GhostState.lean`), kept by the simulation over the specification's log rather than raft's,
and keyed on the specification's acknowledgements (`AckHists`) rather than raft's acknowledgement maps:
raft mints those at a batch's *enter*, outside any line, and a receive line moves `k`'s log before raft
does (`notes/decisions.md`, "Amendment A6 (Q22, Q23)"). -/
def AckHist (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (k : Etcdraft.ID) (T m : Int) : IProp GF :=
  iprop(⌜0 ≤ T ∧ T ≤ (σ.s k).currentTerm ∧ T < 2 ^ 63 ∧ m < 2 ^ 63⌝ ∗
    □ ∀ F : List EntryM, ⌜(σ.s k).log = logAbs C C.length 1 F ∧ BootTerms C.length 1 F⌝ →
      ∃ B : Int, hist γ F (W64 T) (W64 m) B)

instance ackHist_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (k : Etcdraft.ID) (T m : Int) :
    Persistent (AckHist (GF := GF) γ C σ k T m) := by
  unfold AckHist; infer_instance

instance ackHist_timeless (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (k : Etcdraft.ID) (T m : Int) :
    Timeless (AckHist (GF := GF) γ C σ k T m) := by
  unfold AckHist; infer_instance

/-- (Amendment A6, Q22) **The acknowledgements' histories** (the notes' acknowledgement-history copy):
every acknowledgement in flight from a server (`AckMsg`), and every positive match index a leader holds
for another server, at the leader's term, is its server's acknowledgement with its history (`AckHist`).
A leader's `Commit` line reads it (`quorumLogF_commit`, `TracedQuorumLog.lean`): the members of its
match-index quorum hold the newly committed prefix at terms at least the leader's (their histories
agree with the leader's log there, by raft's leader completeness from the commit certificate), so the
prefix is kept from the leader's term (`KeptFrom`). -/
def AckHists (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop((□ ∀ x, ⌜x ∈ σ.messages.domain ++ σ.pendingMessages.domain ∧ AckMsg x ∧ x.source ∈ σ.server⌝ →
      AckHist γ C σ x.source x.term x.matchIndex) ∗
    □ ∀ i k, ⌜i ∈ σ.server ∧ k ∈ σ.server ∧ (σ.s i).state = Etcdraft.leader ∧ k ≠ i ∧
        0 < (σ.s i).matchIndex k⌝ →
      AckHist γ C σ k (σ.s i).currentTerm ((σ.s i).matchIndex k))

instance ackHists_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Persistent (AckHists (GF := GF) γ C σ) := by
  unfold AckHists; infer_instance

instance ackHists_timeless (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Timeless (AckHists (GF := GF) γ C σ) := by
  unfold AckHists; infer_instance

/-- **`QuorumLogInv`'s fact** (amended, A5, Q21; until then the bare `QuorumLogInv` over `σ`, which a
truncating receiver at a lower term than the commit's could not be shown to keep; amended again, A6,
Q22): every server's committed prefix is kept from some term `t` on, `t` a term it was committed at or
after (`QuorumKept`), and the acknowledgements carry their histories (`AckHists`), which a leader's
`Commit` line needs to show its new prefix kept from its term. `QuorumLogInv` follows
(`quorumLogF_quorumLogS`). -/
def QuorumLogF (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop(QuorumKept γ C σ ∗ AckHists γ C σ)

instance quorumLogF_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Persistent (QuorumLogF (GF := GF) γ C σ) := by
  unfold QuorumLogF; infer_instance

instance quorumLogF_timeless (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Timeless (QuorumLogF (GF := GF) γ C σ) := by
  unfold QuorumLogF; infer_instance

/-- `KeptFrom` gives `QuorumLogInv`'s fact for `P`: the servers lacking `P` are among those not
known to keep it, and every configuration is the server set (`CfgFixed`). -/
theorem quorumLogS_of_keptFrom (σ : Etcdraft.State) (hcf : TraceSpecInv.CfgFixed σ)
    (h : ∀ i ∈ σ.server, ∃ t, KeptFrom σ (committedL σ i) t) : TraceSpecInv.QuorumLogS σ := by
  intro i hi
  obtain ⟨t, hK⟩ := h i hi
  have hcfg : σ.getConfig i = σ.server := by simp only [Etcdraft.State.getConfig, hcf i hi]
  rw [hcfg]
  refine TraceSpecInv.isQuorum_filter_mono (fun j hj hp => ?_) hK
  have hc : σ.server.contains j = true := List.elem_iff.2 hj
  simp only [hc, Bool.not_true, Bool.false_or] at hp
  simp [hp]

/-- **`QuorumLogInv`'s fact from the amended clause** (with `SpecInv`'s `CfgFixed`). -/
theorem quorumLogF_quorumLogS (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hcf : TraceSpecInv.CfgFixed σ) :
    QuorumLogF (GF := GF) γ C σ ⊢ ⌜TraceSpecInv.QuorumLogS σ⌝ := by
  iintro #H
  iunfold QuorumLogF at H
  icases H with ⟨#H, -⟩
  iunfold QuorumKept at H
  by_cases hc : ∀ i ∈ σ.server, ∃ t, KeptFrom σ (committedL σ i) t
  · ipureintro; exact quorumLogS_of_keptFrom σ hcf hc
  simp only [Classical.not_forall, not_exists] at hc
  obtain ⟨i, hi, hn⟩ := hc
  ihave Hi := H $$ %i %hi
  icases Hi with ⟨%t, %hK, -⟩
  exact absurd hK (hn t)

/-- `SpecInv`'s `CfgFixed` holds at the bootstrap state: every server's configuration is the voters'
`confAbs C`, the server set (review round 4's D1). -/
theorem cfgFixed_simInit (C : List w64) : TraceSpecInv.CfgFixed (simInit C) := fun i hi => by
  rw [simInit_s_voter C i hi]; rfl

/-- **The bags' uniqueness** (the notes' `MsgsDet`/`AppSlices`): two messages in flight that a line
matches are equal, over both bags (so that a `Ready` moving pending messages out keeps it: review
round 2's A5; a receive line's message is then the one its token names). -/
def MsgsUniq (σ : Etcdraft.State) : Prop :=
  ∀ (ln : Etcdraft.Line) (m1 m2 : Etcdraft.Msg),
    m1 ∈ σ.messages.domain ++ σ.pendingMessages.domain → m2 ∈ σ.messages.domain ++ σ.pendingMessages.domain →
    recvPred ln m1 = true → recvPred ln m2 = true → m1 = m2

/-- **A message's canonical form** (amendment A2, Q15): the fields its type's receive line logs (the
specification's `LoglineIs*`, `recvPred`; besides them a snapshot's commit and an `"app"` request's
entries' contents, which its line does not log: their agreement is not this clause's, plan Q16), the
others at the values the specification's constructors (and raft's, `msgAbs`: `msgAbs_canon`) give them: a vote request its term, last log term and index; a vote response its
term and grant; an append request its subtype, term, previous index and term, entries and commit, a
heartbeat (subtype `"heartbeat"`) its subtype, term and commit only (no previous entry, no entries); an
append response its subtype, term, success and, when a successful `"app"` response, its match index
(else 0); always the source and destination. -/
def canonMsg (x : Etcdraft.Msg) : Etcdraft.Msg :=
  match x.type with
  | .requestVoteRequest | .preVoteRequest =>
    { type := x.type, term := x.term, lastLogTerm := x.lastLogTerm, lastLogIndex := x.lastLogIndex,
      source := x.source, dest := x.dest }
  | .requestVoteResponse | .preVoteResponse =>
    { type := x.type, term := x.term, voteGranted := x.voteGranted, source := x.source, dest := x.dest }
  | .appendEntriesRequest =>
    if x.subtype = "heartbeat" then
      { type := x.type, subtype := x.subtype, term := x.term, commitIndex := x.commitIndex,
        source := x.source, dest := x.dest }
    else
      { type := x.type, subtype := x.subtype, term := x.term, prevLogIndex := x.prevLogIndex,
        prevLogTerm := x.prevLogTerm, entries := x.entries, commitIndex := x.commitIndex,
        source := x.source, dest := x.dest }
  | .appendEntriesResponse =>
    { type := x.type, subtype := x.subtype, term := x.term, success := x.success,
      matchIndex := if x.success && x.subtype != "heartbeat" then x.matchIndex else 0,
      source := x.source, dest := x.dest }

/-- (Amendment A6, Q23) **A message's ends are servers**: its source and its destination. -/
def MsgEnds (σ : Etcdraft.State) (x : Etcdraft.Msg) : Prop :=
  x.source ∈ σ.server ∧ x.dest ∈ σ.server

/-- (Amendment A6, Q23) **Every server's tally holds servers only**: the voters it has heard from
(`votesResponded`, which `SimServerR` ties to raft's tally's keys) are servers (a vote response's
source is, `MsgEnds`), so that a won tally is counted over the configuration
(`tallyGranted_quorum`'s `hc`, `wonVote_quorum`). -/
def VotesIn (σ : Etcdraft.State) : Prop :=
  ∀ i ∈ σ.server, ∀ k ∈ (σ.s i).votesResponded, k ∈ σ.server

/-- **Every message in flight in its canonical form** (amendment A2, Q15; the notes' `MsgsDet`, "the
other fields constant"): with it, two messages a line matches are equal (`MsgsUniq`) once the fields it
logs agree, which a new message's line can then re-establish. (Amendment A6, Q23) and between servers
(`MsgEnds`: a server sends only as itself, to a server of its configuration, and a reply, phantom or
not, goes from its request's destination back to its source), so that the receive law can give a
receive line's phase step its message's source among the voters (`PhaseStepR`; a won vote's quorum is
counted over the configuration, `tallyGranted_quorum`'s `hc`); and every server's tally of servers
(`VotesIn`), which the receive law also gives the phase step. -/
def MsgsShape (σ : Etcdraft.State) : Prop :=
  (∀ x ∈ σ.messages.domain ++ σ.pendingMessages.domain, canonMsg x = x ∧ MsgEnds σ x) ∧ VotesIn σ

/-- **`MsgsShape` carried** to a state with the same servers and tallies, whose messages in flight
were in flight (each canonical between servers). -/
theorem msgsShape_of {σ σ' : Etcdraft.State} (hsrv : σ'.server = σ.server)
    (hsub : ∀ x ∈ σ'.messages.domain ++ σ'.pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain)
    (hV : ∀ i, (σ'.s i).votesResponded = (σ.s i).votesResponded) (h : MsgsShape σ) : MsgsShape σ' :=
  ⟨fun x hx => ⟨(h.1 x (hsub x hx)).1, by unfold MsgEnds; rw [hsrv]; exact (h.1 x (hsub x hx)).2⟩,
    fun i hi k hk => by rw [hsrv] at hi ⊢; rw [hV] at hk; exact h.2 i hi k hk⟩

/-- **A leader's append requests of its term are slices of its log** (amendment A2, Q16; the notes'
`AppSlices`): while server `i` leads term `T`, every append request in flight of term `T` from `i`
carries, at each of its positions, the entry of `i`'s log at that index. Inductive with `SpecInv`'s
`CandS`: only a leader sends append requests, from its log (`appendEntriesInRangeToPeer`); a leader's
log only grows while it leads (`Replicate`; truncations, `ConflictAppendEntriesRequest` and a
snapshot's, happen at followers only); a step-down, a term change or a restart makes the clause
vacuous; and at `BecomeLeader` it holds vacuously, a candidate having no append request of its term out
(`CandS`), whatever happened in that term before (a restart may return to an earlier term). With it, a new append request of the leader matches no other in-flight request
differing from it in its entries (which its line logs by count only). -/
def AppSlices (σ : Etcdraft.State) : Prop :=
  ∀ m ∈ σ.messages.domain ++ σ.pendingMessages.domain, m.type = .appendEntriesRequest →
    ∀ i ∈ σ.server, (σ.s i).state = Etcdraft.leader → (σ.s i).currentTerm = m.term → m.source = i →
      ∀ (k : Nat) (e : Etcdraft.Entry), m.entries[k]? = some e → (σ.s i).log[m.prevLogIndex.toNat + k]? = some e

/-- **A message's facts** (review round 2's A3): an append request carries its source's leadership of
its term (`isLeader`: raft sends one only while leading), its entries' records after its previous
entry (`logRecs`, their indices within `w64`); any other message carries no entries. (Review round
5's E2: the receiver's raised commit index gets its `commitIn` from raft's own message facts, which
`raft.Step` receives with the message, `#Hmsg`, carried over with `commitIn_move`; so no commit
certificate here.) -/
def msgFacts (γ : RaftNames) (C : List w64) (m : Etcdraft.Msg) : IProp GF :=
  if m.type = .appendEntriesRequest then
    iprop(∃ (src : w64) (es : List EntryM),
      ⌜m.source = idAbs src ∧ m.entries = logAbs C C.length (m.prevLogIndex.toNat + 1) es ∧
        m.prevLogIndex + m.entries.length < 2 ^ 64⌝ ∗
      isLeader γ src (W64 m.term) ∗ logRecs γ (entryID.mk (W64 m.prevLogTerm) (W64 m.prevLogIndex)) es)
  -- (review round 4's D2) only an append request carries entries (raft's `MsgApp`)
  else iprop(⌜m.entries = []⌝)

instance msgFacts_persistent (γ : RaftNames) (C : List w64) (m : Etcdraft.Msg) :
    Persistent (msgFacts (GF := GF) γ C m) := by
  unfold msgFacts; split <;> infer_instance

instance msgFacts_timeless (γ : RaftNames) (C : List w64) (m : Etcdraft.Msg) :
    Timeless (msgFacts (GF := GF) γ C m) := by
  unfold msgFacts; split <;> infer_instance

/-- **The specification state's facts in `simInv`** (Draft): every voter's raft facts (`allFacts`:
`MoreThanOneLeaderInv`, `LogInv`, `LogMatchingInv`, `CommitOk`, and with the vote table
`LeaderCompletenessInv`; a leader's log is its records followed by its pending entries, those its
`Replicate` lines announced before raft appends them: `srvFacts`, review finding A9), the
specification invariant `SpecInv` (`TraceSimSpecInv.lean`: with it
`ElectionSafetyInv`, `CommittedIsDurableInv`, `CommitWithinLeader`; it replaces `DurInv`, false as
stated), `QuorumLogInv`'s fact (amendment A5, Q21: in its inductive form, with raft's commit
justification, `QuorumKept`; amendment A6, Q22: with the acknowledgements' histories, `AckHists`, which
a leader's `Commit` line needs: together `QuorumLogF`), the bags' uniqueness and (amendment A2, Q15, Q16)
every message in flight canonical (`MsgsShape`; amendment A6, Q23: between servers) and a leader's
append requests of its term slices of its log (`AppSlices`). -/
def simFx (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop(allFacts γ C σ ∗ (□ ∀ m, ⌜m ∈ σ.messages.domain ++ σ.pendingMessages.domain⌝ → msgFacts γ C m) ∗
    QuorumLogF γ C σ ∗ ⌜TraceSpecInv.SpecInv σ ∧ MsgsUniq σ ∧ MsgsShape σ ∧ AppSlices σ⌝)

instance simFx_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Persistent (simFx (GF := GF) γ C σ) := by
  unfold simFx; infer_instance

instance simFx_timeless (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Timeless (simFx (GF := GF) γ C σ) := by
  unfold simFx; infer_instance

/-- **The facts give the invariants** (`violated = none`), with raft's vote table. -/
theorem simFx_violated (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (hsrv : σ.server = confAbs C) :
    votesTbl (GF := GF) γ ∗ simFx γ C σ ⊢ ⌜σ.violated = .ok none⌝ := by
  iintro ⟨Htbl, Hfx⟩
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, -, #Hq, %Hp⟩
  obtain ⟨hsi, -⟩ := Hp
  icases quorumLogF_quorumLogS γ C σ hsi.cfgFixed $$ Hq with %hq
  have hcw := hsi.commitWithinLeader
  icases allFacts_oneLeader γ C σ hsrv $$ Hal with %h1
  icases allFacts_logInv γ C σ hsrv $$ Hal with %h2
  icases allFacts_logMatching γ C σ hsrv $$ Hal with %h3
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %h4
  icases allFacts_leaderCompleteness γ C σ hsrv hcw $$ [$Htbl $Hal] with %h5
  ipureintro
  exact violated_none σ ⟨h4, h2, h1, hsi.electionSafety, h3, hq, h5, hsi.committedIsDurable⟩

/-- **The simulation's capability** on a hook path (Q8): `emp` in an untraced cluster; in a traced
one, the node's share `(cs, P)` with the function's phase `Φ C cs P` (`C` the voters, the
configuration `c` their permutation with no outgoing half, the node one of them: review round 1's
F4), the node's logger and its contract, and the simulation's invariant. `c` is only this pure
clause, always the voters': raft's own whenever raft's tracker holds all the voters (the gates
require it once `b = true`: `trCapB_hookGate_bf`'s `hcC`), not while it grows from empty in `newRaft` and `Bootstrap` (amendment A1: the bootstrap
lines' events are of raft's configuration, their law's bound of the capability's,
`trCapB_hookGate_bf`; `trCapB_cfg` re-keys it). (Amendment A6, Q24) The voters fit the bootstrap log
(`C.length ≤ γ.reBoot.length`: one bootstrap entry per voter, `BootLogOk`, known where the capability is
made; every law keeps it, `C` and `γ.reBoot` being fixed), so that an accepted append request's entries
lie past the specification's bootstrap positions.

**Coupled to `trCapStart`** (`TracedBootVocab.lean`, the capability before the `raft` struct exists): its
traced arm copies this body, with the logger as a parameter in place of the field. Keep the two in step: a
conjunct added here must be added there, and the law `trCapStart_trCapB` re-proved (review `step5-r1.md`'s
S3). -/
def trCapB (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop := fun _ => True) :
    IProp GF :=
  match tr with
  | none => iprop(emp)
  | some γd => iprop(∃ (tn : TraceNames) (C : List w64) (tl : GoInterface) (cs : ServerC)
      (P : List Etcdraft.Msg),
      traceDir γd tn ∗ ⌜tn.voters = C ∧ (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C ∧
        C.length ≤ γ.reBoot.length⌝ ∗
      r.[raft, go!"traceLogger"] ↦□ tl ∗ isTraceLogger tn.tr tl ∗
      ⌜tl ≠ interface.nil⌝ ∗ inv (simNS γ) (simInv C tn (simFx γ C)) ∗ raftLogInv γ ∗ simNode tn id cs P ∗
      (∃ o, simBoot tn id b o ∗ ⌜Λ o⌝) ∗ ⌜Φ C cs P⌝)

/-- **The capability, whatever the node's `booted` flag** (`trCapB`'s, review round 2's A7: the laws
of non-bootstrap lines set it; the bootstrap lines' law needs it unset). -/
def trCap (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop := fun _ => True) :
    IProp GF :=
  match tr with
  | none => iprop(emp)
  | some _ => iprop(∃ b, trCapB tr γ r id c b Φ Λ)

/-- In an untraced cluster the capability is nothing. -/
theorem trCap_none (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) :
    trCap (GF := GF) none γ r id c Φ ⊣⊢ iprop(emp) := .rfl

/-! ## The global step (Draft statement, review round 1's S1) -/

/-- **The facts kept by a phase's lines**: for every share in phase `Φ`, event `E` allows and effect
of it (`PhaseStep`'s), the specification state's facts (`simFx`) at any state whose node `id` is the
share's server hold at the state the line leads to, and at its intermediate states (`Mid`-shaped:
none for a line consuming no message). The caller proves it from node `id`'s raft ghost (a leader's
term log, its records, its commit certificate), which only it holds. -/
def FxPres (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  iprop(□ ∀ (C : List w64) (cs : ServerC) (P : List Etcdraft.Msg) (e : TraceEv) (a a' : Etcdraft.Server)
      (P' : List Etcdraft.Msg) (σ : Etcdraft.State),
    ⌜Φ C cs P ∧ E e ∧ toC (confAbs C) a = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
      LineEffect C false e (idAbs id) a a' none _root_.id (fun b => P'.foldl Etcdraft.Bag.with b) (fun _ => False) ∧
      σ.server = confAbs C ∧ σ.s (idAbs id) = a ∧ σ.preVote = false ∧ σ.checkQuorum = false ∧
      σ.violated = .ok none⌝ -∗
    votesTbl γ -∗ simFx γ C σ -∗
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs id) a' _root_.id (fun b => P'.foldl Etcdraft.Bag.with b)))

/-- **The facts kept by a phase's lines, with a ghost update** (review round 5's E1): as `FxPres`, but
consumed once and allowed an update (`==∗`) of ghost state the caller lends to it, which comes back
as `R'` (the `BecomeLeader` line: the new leader's term log is created inside the line's step, after
its freshness is read). `FxPres` is the case `R' = emp` (`fxPres_upd`). -/
def FxPresU (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (R' : IProp GF) : IProp GF :=
  iprop(∀ (C : List w64) (cs : ServerC) (P : List Etcdraft.Msg) (e : TraceEv) (a a' : Etcdraft.Server)
      (P' : List Etcdraft.Msg) (σ : Etcdraft.State),
    ⌜Φ C cs P ∧ E e ∧ toC (confAbs C) a = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
      LineEffect C false e (idAbs id) a a' none _root_.id (fun b => P'.foldl Etcdraft.Bag.with b) (fun _ => False) ∧
      σ.server = confAbs C ∧ σ.s (idAbs id) = a ∧ σ.preVote = false ∧ σ.checkQuorum = false ∧
      σ.violated = .ok none⌝ -∗
    votesTbl γ -∗ simFx γ C σ ==∗
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs id) a' _root_.id (fun b => P'.foldl Etcdraft.Bag.with b)) ∗ R')

/-- `FxPresU`, gated on the cluster's trace mode (review round 6's F4): untraced, only the update
giving `R'` (so one spec per function still works for both modes). -/
def FxPresUT (tr : Option GName) (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (R' : IProp GF) : IProp GF :=
  match tr with
  | none => iprop(|==> R')
  | some _ => FxPresU γ id E Φ Φ' R'

theorem fxPres_upd (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) :
    FxPres (GF := GF) γ id E Φ Φ' ⊢ FxPresU γ id E Φ Φ' iprop(emp) := by
  iintro H
  iunfold FxPres at H
  icases H with #H
  iunfold FxPresU
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl Hfx
  icases H $$ %C %cs %P %e %a %a' %P' %σ %hpre Htbl Hfx with ⟨Htbl, Hfx'⟩
  imodintro
  iframe Htbl Hfx'

/-- `FxPres`, in a traced cluster only. -/
def FxPresT (tr : Option GName) (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  match tr with
  | none => iprop(True)
  | some _ => FxPres γ id E Φ Φ'

/-- **The global step, as one law** (Draft statement; its proof is `simRun_lineEffect` inside the
logger's update, with the invariants from `simFx` and the bags' uniqueness): a capability in phase
`Φ`, a phase step by the events `E` and the facts kept give the event builder's gate whose update
leaves the capability in phase `Φ'`. Internal (review round 4's D6): callers use `trCap_fire_any`,
of which this is the case of a node whose segment may not be over. -/
abbrev trCap_fire.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop) (R' : IProp GF),
  PhaseStep id c E Φ Φ' → (∀ e, E e → Λ' (some e)) →
  (∀ e, E e → TraceEv.Ok (elements c.incoming).length e) →
  (trCap (some γd) γ r id c Φ Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ FxPresU γ id E Φ Φ' R' : IProp GF) ⊢
    TraceFire (some γd) tl E iprop(trCapB (some γd) γ r id c true Φ' Λ' ∗ R')

/-! ## The global step of a receive line (Draft statement) -/

/-- **A phase step by a receive line consuming `m`**: from every share in phase `Φ`, each event `E`
allows is a line matching `m` (its parse's `recvPred`), not bootstrap-named, with, for every server
`a` the share stands for, an effect consuming `m` into phase `Φ'`, its replies pending: raft's `P'` in
the node's share, the phantoms `ph a` (the specification's replies raft does not send, review round
2's A6; a function of the receiving server before the line, amendment A2, chosen by the caller: the
intended instance is `recvPhantoms m` (`TracedRecvPhantom.lean`), `phantomOf` for a lower-term request and none otherwise) among
the phantoms, through intermediate states of the shape `Mid`. (Amendment A6, Q23: the step may assume
the message's source a voter, `m.source ∈ confAbs C`, and the share's tally of voters, which the
receive law gives from `simFx`'s `MsgsShape`: with them a won tally is counted over the
configuration, `wonVote_quorum`.) -/
def PhaseStepR (id : w64) (c : CfgM) (m : Etcdraft.Msg) (E : TraceEv → Prop) (Mid : Etcdraft.Server → Prop)
    (ph : Etcdraft.Server → List Etcdraft.Msg)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : Prop :=
  ∀ C cs P, Φ C cs P → (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C ∧ m.source ∈ confAbs C ∧
      (∀ k ∈ cs.votesResponded, k ∈ confAbs C) →
    ∀ e, E e →
    e.nid = decStr id ∧ Etcdraft.isBootstrapName (gsStr e.name) = false ∧
    (∀ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln → recvPred ln m = true) ∧
    ∀ a : Etcdraft.Server, toC (confAbs C) a = cs →
    ∃ (a' : Etcdraft.Server) (P' : List Etcdraft.Msg),
      Φ' C (toC (confAbs C) a') (P ++ P') ∧ (∀ x ∈ P', x.source = idAbs id) ∧
      LineEffect C false e (idAbs id) a a' (some m) (fun b => b.without m)
        (fun b => (P' ++ ph a).foldl Etcdraft.Bag.with b) Mid

/-- **The facts kept by a receive line** (`FxPres`'s counterpart): at the result, and at every
intermediate state; the phantom replies are the receiving server's `ph a` (amendment A2). -/
def FxPresR (γ : RaftNames) (id : w64) (m : Etcdraft.Msg) (E : TraceEv → Prop) (Mid : Etcdraft.Server → Prop)
    (ph : Etcdraft.Server → List Etcdraft.Msg)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  iprop(□ ∀ (C : List w64) (cs : ServerC) (P : List Etcdraft.Msg) (e : TraceEv) (a a' : Etcdraft.Server)
      (P' : List Etcdraft.Msg) (σ : Etcdraft.State),
    ⌜Φ C cs P ∧ E e ∧ toC (confAbs C) a = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
      LineEffect C false e (idAbs id) a a' (some m) (fun b => b.without m)
        (fun b => (P' ++ ph a).foldl Etcdraft.Bag.with b) Mid ∧
      σ.server = confAbs C ∧ σ.s (idAbs id) = a ∧ σ.preVote = false ∧ σ.checkQuorum = false ∧
      σ.violated = .ok none ∧ m ∈ σ.messages.domain⌝ -∗
    votesTbl γ -∗ simFx γ C σ -∗
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs id) a' (fun b => b.without m)
        (fun b => (P' ++ ph a).foldl Etcdraft.Bag.with b)) ∗
      (∀ v, ⌜Mid v⌝ -∗ simFx γ C (withNode σ (idAbs id) v _root_.id _root_.id)))

/-- **The global step of a receive line, as one law** (Draft statement): as `trCap_fire`, the line
consuming the message of the caller's token `k`. -/
abbrev trCap_fire_recv.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (k : Nat) (m : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop) (ph : Etcdraft.Server → List Etcdraft.Msg)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop),
  PhaseStepR id c m E Mid ph Φ Φ' → (∀ e, E e → Λ' (some e)) →
  (∀ e, E e → TraceEv.Ok (elements c.incoming).length e) →
  (trCap (some γd) γ r id c Φ Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ FxPresR γ id m E Mid ph Φ Φ' ∗
    (∃ tn, traceDir γd tn ∗ inFlight tn k m) : IProp GF) ⊢
    TraceFire (some γd) tl E (trCapB (some γd) γ r id c true Φ' Λ')

/-! ## The global step of a `Ready` line (Draft statement, review round 2's A5) -/

/-- **A phase step by a `Ready` line**: its events are node `id`'s `Ready` events, and the phase moves
to `Φ'` with the share's server persisted and its pending messages handed out. -/
def PhaseStepReady (id : w64) (c : CfgM) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : Prop :=
  ∀ C cs P, Φ C cs P → (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C → ∀ e, E e →
    (∃ (s : NState) (cfg : CfgM), NodeEvOf (W64 8) id s cfg e ∧ cfg.outgoing = ∅) ∧
    ∀ a : Etcdraft.Server, toC (confAbs C) a = cs →
      Φ' C (toC (confAbs C) { a with durable := Etcdraft.durableOf a }) []

/-- **The facts kept by a `Ready` line.** -/
def FxPresReady (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  iprop(□ ∀ (C : List w64) (cs : ServerC) (P : List Etcdraft.Msg) (e : TraceEv) (σ : Etcdraft.State),
    ⌜Φ C cs P ∧ E e ∧ σ.server = confAbs C ∧ toC (confAbs C) (σ.s (idAbs id)) = cs ∧
      σ.preVote = false ∧ σ.checkQuorum = false ∧ σ.violated = .ok none⌝ -∗
    votesTbl γ -∗ simFx γ C σ -∗ votesTbl γ ∗ simFx γ C (σ.ready (idAbs id)))

/-- **The global step of a `Ready` line, as one law** (Draft statement): the line moves node `id`'s
pending messages to the network, the share empties, and the caller receives their tokens. -/
abbrev trCap_fire_ready.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop),
  PhaseStepReady id c E Φ Φ' → (∀ e, E e → Λ' (some e)) →
  (∀ e, E e → TraceEv.Ok (elements c.incoming).length e) →
  -- (review round 3's C1) the facts a `Ready` line keeps are a lemma (`fxPresReady`), not a premise
  (trCap (some γd) γ r id c Φ Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢
    TraceFire (some γd) tl E iprop(trCapB (some γd) γ r id c true Φ' Λ' ∗
      ∃ (tn : TraceNames) (P : List Etcdraft.Msg) (Bn : GMap Nat Etcdraft.Msg), traceDir γd tn ∗
        -- (review round 3's B1) the list the tokens are for: the share's pending messages before the
        -- line, in phase `Φ`: the outbox `readyWithoutAccept` handed out (review round 4's D3: at the
        -- hook raft's outbox is already cleared, so the caller's phase is anchored at the hand-out)
        ⌜∃ cs, Φ tn.voters cs P⌝ ∗
        ⌜((GMap.toList Bn).map Prod.snd).Perm P⌝ ∗ [∗map] k ↦ m ∈ Bn, inFlight tn k m)

/-! ## The global step of a bootstrap line (Draft statement, review round 2's A7) -/

/-- **A bootstrap line's law**: before its segment is over (`booted` unset), a node's bootstrap-named
line is one `TraceNext` steps over, the state and the share unchanged. `c` is the capability's
configuration, the voters' (`trCapB`), not raft's: the events `E` (`InitState`, `BecomeFollower`,
`ApplyConfChange`) are of raft's growing configuration, within the voters' (amendment A1).
(Amendment A7, Q29) Each event is the next of raft's bootstrap sequence for the voters `C` (the
capability's, which the phase `Φ` may pin) after the node's last event, which `Λ` describes
(`BootNext`): so the bootstrap segments `simInv` keeps (`BootSegs`) are raft's, which `NewTrace` reads. -/
abbrev trCap_fire_boot.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop),
  (∀ e, E e → e.nid = decStr id ∧ ∃ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln ∧ ln.nid = idAbs id ∧
    Etcdraft.isBootstrapName ln.ev.name = true) →
  (∀ C cs P, Φ C cs P → ∀ e, E e → ∀ o, Λ o → BootNext C id o e) → (∀ e, E e → Λ' (some e)) →
  (∀ e, E e → TraceEv.OkBoot (elements c.incoming).length e) →
  (trCapB (some γd) γ r id c false Φ Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢
    TraceFire (some γd) tl E (trCapB (some γd) γ r id c false Φ Λ')

/-! ## The completion witness (amendment A8, Q37) -/

/-- **A node's bootstrap complete**: an unbooted capability whose last event is raft's last bootstrap
event for the voters (`BootEvAt C id (|C| + 3)`, which the caller states through its phase `Φ`, which pins
the voters, and `Λ`) mints the persistent witness `bootDone tn id` at the cluster's trace names, the
capability kept. (No line is logged; the witness outlives the capability, for the end of the run:
`simInv_end_bootDone`.) -/
abbrev trCapB_bootDone.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) (E : CoPset),
  ↑(simNS γ) ⊆ E →
  (∀ C cs P o, Φ C cs P → Λ o → ∃ x, o = some x ∧ BootEvAt C id (C.length + 3) x) →
  trCapB (GF := GF) (some γd) γ r id c false Φ Λ ⊢
    |={E}=> (trCapB (some γd) γ r id c false Φ Λ ∗ ∃ tn, traceDir γd tn ∗ bootDone tn id)

/-! ## The global step of a booted node's bootstrap-named line (Draft, review round 2's A7) -/

/-- **A phase step by a booted node's line** other than `BecomeFollower` (`PhaseStep` without its
bootstrap-name condition: past the node's segment, a bootstrap-named line, the application's
`ApplyConfChange` after the first `Ready`, is an ordinary step). -/
def PhaseStepB (id : w64) (c : CfgM) (E : TraceEv → Prop) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : Prop :=
  ∀ C cs P, Φ C cs P → (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C → ∀ e, E e →
    e.nid = decStr id ∧ gsStr e.name ≠ "BecomeFollower" ∧
    ∀ a : Etcdraft.Server, toC (confAbs C) a = cs →
    ∃ (a' : Etcdraft.Server) (P' : List Etcdraft.Msg),
      Φ' C (toC (confAbs C) a') (P ++ P') ∧ (∀ x ∈ P', x.source = idAbs id) ∧
      LineEffect C false e (idAbs id) a a' none _root_.id (fun b => P'.foldl Etcdraft.Bag.with b) (fun _ => False)

/-- **The global step of a booted node's line, as one law** (`trCap_fire`'s, any name but
`BecomeFollower`, the node's segment over). Internal (review round 4's D6): callers use
`trCap_fire_any`. -/
abbrev trCap_fire_booted.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop) (R' : IProp GF),
  PhaseStepB id c E Φ Φ' → (∀ e, E e → Λ' (some e)) →
  (∀ e, E e → TraceEv.Ok (elements c.incoming).length e) →
  (trCapB (some γd) γ r id c true Φ Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ FxPresU γ id E Φ Φ' R' : IProp GF) ⊢
    TraceFire (some γd) tl E iprop(trCapB (some γd) γ r id c true Φ' Λ' ∗ R')

/-- **The global step of a line consuming no message, any `booted` flag, as one law** (review round 3's
C3: `trCap_fire` and `trCap_fire_booted` in one, so that a caller never chooses): before the node's
segment is over, the line must not be bootstrap-named. -/
abbrev trCap_fire_any.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (b : Bool) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop) (R' : IProp GF),
  PhaseStepB id c E Φ Φ' → (b = false → ∀ e, E e → Etcdraft.isBootstrapName (gsStr e.name) = false) →
  (∀ e, E e → Λ' (some e)) →
  (∀ e, E e → TraceEv.Ok (elements c.incoming).length e) →
  (trCapB (some γd) γ r id c b Φ Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ FxPresU γ id E Φ Φ' R' : IProp GF) ⊢
    TraceFire (some γd) tl E iprop(trCapB (some γd) γ r id c true Φ' Λ' ∗ R')

/-! ## The global step of a `BecomeFollower` line after the node's segment (Draft, review round 2's A7) -/

/-- **A phase step by a `BecomeFollower` line** past the node's bootstrap segment: its skip bit is
the node's last line's (`bfCond`, the specification's `IsBecomeFollowerInUpdateTermOrReturnToFollower`),
which the capability's last-event predicate `Λ` describes. Skipped (after an `UpdateTerm` or a lost
election's `ReturnToFollower` by the previous line): the share unchanged, in phase `Φ'`. Not skipped:
the node steps down (`StepDownToFollower`, from leader or candidate), its server `bfSrv a`, related
to the event's state `s`, in phase `Φ'`. -/
def PhaseStepBF (id : w64) (c : CfgM) (s : NState) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ : Option TraceEv → Prop) : Prop :=
  ∀ C cs P o, Φ C cs P → Λ o → (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C →
    ∀ e e0, NodeEvOf (W64 2) id s c e → o = some e0 →
      (bfCond (evConv e0) (evConv e) = true → Φ' C cs P) ∧
      (bfCond (evConv e0) (evConv e) = false → ∀ a : Etcdraft.Server, toC (confAbs C) a = cs →
        (a.state = Etcdraft.leader ∨ a.state = Etcdraft.candidate) ∧
        SimServerR C C.length (toPState s) (bfSrv a) ∧ LogShapeOk C.length (toPState s) ∧
        s.role ≠ .preCandidate ∧ uint.Z s.term < 2 ^ 63 ∧ uint.Z s.logst.committed < 2 ^ 63 ∧
        uint.Z (plastIndex (toPState s)) < 2 ^ 63 ∧ Φ' C (toC (confAbs C) (bfSrv a)) P)

/-- **The facts kept by a step-down.** The caller's (review round 3's C1 asked for a lemma): a
leader's `srvFacts` may have pending entries (A9), which a non-leader's may not, so the step-down
keeps the facts only where the leader has none, which its caller knows from raft's log. -/
def FxPresBF (γ : RaftNames) (id : w64) (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  iprop(□ ∀ (C : List w64) (P : List Etcdraft.Msg) (σ : Etcdraft.State),
    ⌜Φ C (toC (confAbs C) (σ.s (idAbs id))) P ∧ σ.server = confAbs C ∧ σ.preVote = false ∧
      σ.checkQuorum = false ∧ σ.violated = .ok none ∧
      ((σ.s (idAbs id)).state = Etcdraft.leader ∨ (σ.s (idAbs id)).state = Etcdraft.candidate)⌝ -∗
    votesTbl γ -∗ simFx γ C σ -∗
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs id) (bfSrv (σ.s (idAbs id))) _root_.id _root_.id))

/-- **A `BecomeFollower` line's law** past the node's segment (`booted` set): skipped or a step-down,
as the node's last line decides. -/
abbrev trCap_fire_bf.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (s : NState)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop),
  PhaseStepBF id c s Φ Φ' Λ → (∀ e, NodeEvOf (W64 2) id s c e → Λ' (some e)) →
  (∀ e, NodeEvOf (W64 2) id s c e → TraceEv.Ok (elements c.incoming).length e) →
  (trCapB (some γd) γ r id c true Φ Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ FxPresBF γ id Φ : IProp GF) ⊢
    TraceFire (some γd) tl (NodeEvOf (W64 2) id s c) (trCapB (some γd) γ r id c true Φ' Λ')

/-- **The capability re-keyed to another configuration of raft's** (review round 3's B5: during the
bootstrap, raft's configuration grows from empty to the voters'; the capability's `c` is only its
pure clause, so any `c'` of the same voters will do). -/
theorem trCapB_cfg (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c c' : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop)
    (h : ∀ C, (elements c.incoming).Perm C → c.outgoing = ∅ → id ∈ C →
      (elements c'.incoming).Perm C ∧ c'.outgoing = ∅) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢ trCapB (some γd) γ r id c' b Φ Λ := by
  iintro H
  iunfold trCapB at H
  iunfold trCapB
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, Hrest⟩
  obtain ⟨hvC, hperm, hout, hC, hbf⟩ := Hpf
  obtain ⟨hperm', hout'⟩ := h C hperm hout hC
  iexists tn, C, tl, cs, P
  iframe Hdir Hrest
  ipureintro; exact ⟨hvC, hperm', hout', hC, hbf⟩

/-- A capability with its `booted` flag known is one. -/
theorem trCapB_trCap (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢ trCap (some γd) γ r id c Φ Λ := by
  iintro H; iunfold trCap; iexists b; iexact H

/-- The capability's untraced instance (`trCap_none`'s, with the `booted` flag). -/
theorem trCapB_none (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) none γ r id c b Φ Λ ⊣⊢ iprop(emp) := .rfl

/-- An untraced caller supplies the capability with nothing. -/
theorem trCapB_none_intro (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    ⊢ trCapB (GF := GF) none γ r id c b Φ Λ := by
  exact .rfl

/-- The facts kept, untraced: nothing. -/
theorem fxPresT_none (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) :
    FxPresT (GF := GF) none γ id E Φ Φ' ⊣⊢ iprop(True) := .rfl

/-- ... and with a ghost update, only the update. -/
theorem fxPresUT_none (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (R' : IProp GF) :
    FxPresUT (GF := GF) none γ id E Φ Φ' R' ⊣⊢ iprop(|==> R') := .rfl

end ghost

section phaseBot
variable [GooseExts]

/-- **The untraced instance's phase**: no share. An untraced caller instantiates a hook-path spec's
phases with it; every phase-step premise then holds vacuously (`phaseStep_bot`, ...), and its
capability is `emp` whatever the phase. -/
def phaseBot : List w64 → ServerC → List Etcdraft.Msg → Prop := fun _ _ _ => False

theorem phaseStep_bot (id : w64) (c : CfgM) (E : TraceEv → Prop)
    (Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : PhaseStep id c E phaseBot Φ' :=
  fun _ _ _ h => h.elim

theorem phaseStepB_bot (id : w64) (c : CfgM) (E : TraceEv → Prop)
    (Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : PhaseStepB id c E phaseBot Φ' :=
  fun _ _ _ h => h.elim

theorem phaseStepR_bot (id : w64) (c : CfgM) (m : Etcdraft.Msg) (E : TraceEv → Prop)
    (Mid : Etcdraft.Server → Prop) (ph : Etcdraft.Server → List Etcdraft.Msg)
    (Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) :
    PhaseStepR id c m E Mid ph phaseBot Φ' :=
  fun _ _ _ h => h.elim

theorem phaseStepReady_bot (id : w64) (c : CfgM) (E : TraceEv → Prop)
    (Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : PhaseStepReady id c E phaseBot Φ' :=
  fun _ _ _ h => h.elim

theorem phaseStepBF_bot (id : w64) (c : CfgM) (s : NState)
    (Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    PhaseStepBF id c s phaseBot Φ' Λ :=
  fun _ _ _ _ h => h.elim

end phaseBot

end EtcdGrove
end Perennial
