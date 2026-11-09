/-
Lean-first (no Rocq counterpart). Trace-check's S5, Draft (2026-11-09): the simulation's capability
on raft's hook paths, and the traced statements of the `Commit` path (`traceNodeEvent`,
`traceCommit`, `raft.maybeCommit`) (`notes/trace-validation-sim.md`, "S5 Draft: the capability";
the plan's Q8).

- `TraceFire tr tl E Q`: what a hook's caller gives the event builder, by the cluster's trace mode
  (`NGhost.tr`): in an untraced cluster, a nil logger and `Q`; in a traced one, the logger's
  contract and the atomic update appending any event `e` with `E e` and giving `Q` (the caller's
  simulation step);
- `SimIdle C s c P`: node state `s` and the node's share `(c, P)` related at a hook point of the
  idle phase (revision 13's `R_i` with the pending messages);
- `trCap tr r id Φ`: the simulation's capability a function on a hook path carries, `emp` in an
  untraced cluster, and in a traced one the node's share with `Φ` of it (the function's phase),
  the logger's contract and the simulation's invariant.

**Vacuous until Q8's logger clause lands** (review round 1, `notes/trace-validation-reviews/s5-r1.md`):
`ownRaftPhys` still requires a nil logger (`InvRaftPhys.lean`, `TraceLoggerOk`), while the traced
capability carries a non-nil one, so every traced triple here is provable by contradiction until
that clause becomes `TraceLoggerOkS s.gh.tr tl`. Prove none before.

Each `X.tracedSpec` is `X.spec` with the capability added (one spec per function: the untraced
instance, `s.gh.tr = none`, is `X.spec`'s, `trCap none … = emp`). **As `TracedApiDraft`:** a traced
statement replaces its `X.spec` only once proved; until then these are definitions, reviewed with
the rest of the Draft, and the existing specs stay as they are.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.traceCommit
public import Spec.go_etcd_io.raft.v3.traceNodeEvent
public import Spec.go_etcd_io.raft.v3.traceSendMessage
public import Spec.go_etcd_io.raft.v3.traceReceiveMessage
public import Spec.go_etcd_io.raft.v3.traceBecomeFollower
public import Spec.go_etcd_io.raft.v3.traceBecomeCandidate
public import Spec.go_etcd_io.raft.v3.traceBecomeLeader
public import Spec.go_etcd_io.raft.v3.traceReady
public import Spec.go_etcd_io.raft.v3.traceReplicate
public import Spec.go_etcd_io.raft.v3.raft__send
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

/-- `MessageType.String()` of the traced types. -/
def msgTypeStr : MsgType → GoString
  | .vote => go!"MsgVote"
  | .voteResp => go!"MsgVoteResp"
  | .app => go!"MsgApp"
  | .appResp => go!"MsgAppResp"
  | .heartbeat => go!"MsgHeartbeat"
  | .heartbeatResp => go!"MsgHeartbeatResp"
  | _ => go!""

/-- The traced message `tm` of raft's message `m` (`makeTracingMessage`, a non-snapshot). -/
def MsgEvOf (m : Msg) (tm : TraceMsg) : Prop :=
  tm.typ = msgTypeStr m.ty ∧ tm.term = m.term ∧ tm.frm = decStr m.src ∧ tm.to = decStr m.dst ∧
  tm.entries = W64 m.entries.length ∧ tm.logTerm = m.logterm ∧ tm.index = m.index ∧
  tm.commit = m.commit ∧ tm.reject = m.reject

/-- The events `traceSendMessage(r, m)` may log for a traced message `m` (`traceEvent` with the
message; its properties unconstrained). -/
def SendEvOf (evt : w64) (id : w64) (s : NState) (c : CfgM) (m : Msg) (e : TraceEv) : Prop :=
  evtNames[uint.nat evt]? = some e.name ∧
  e.nid = decStr id ∧ e.term = s.term ∧ e.vote = decStr s.vote ∧ e.commit = s.logst.committed ∧
  e.role = roleStr s.role ∧ e.logSize = plastIndex (toPState s) ∧
  (∃ xs ys : List w64, xs ≡ₚ elements c.incoming ∧ ys ≡ₚ elements c.outgoing ∧
    e.conf = (xs.map decStr, ys.map decStr)) ∧
  (∃ tm, e.msg = some tm ∧ MsgEvOf m tm) ∧ e.cc = none

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

/-- **A phase step by a line consuming no message** (not a bootstrap-named line: not `BecomeFollower`,
whose skip bit only the node's previous line decides, review round 1's F6, so that the line is never
a bootstrap line, `bootFlags_nonBoot`): from every share `(cs, P)` in phase `Φ`,
each event `E` allows has, for every server `a` the share stands for, an effect into a share in
phase `Φ'` (review round 1's S2), its pending messages `P'` added. -/
def PhaseStep (id : w64) (c : CfgM) (E : TraceEv → Prop) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : Prop :=
  ∀ C cs P, Φ C cs P → (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C → ∀ e, E e → Etcdraft.isBootstrapName (gsStr e.name) = false ∧
    ∀ a : Etcdraft.Server, toC (confAbs C) a = cs →
    ∃ (a' : Etcdraft.Server) (P' : List Etcdraft.Msg),
      Φ' C (toC (confAbs C) a') (P ++ P') ∧
      LineEffect C false e (idAbs id) a a' none _root_.id (fun b => P'.foldl Etcdraft.Bag.with b) (fun _ => False)

end pure

/-! ## The capability -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The simulation's invariant's namespace, beside raft's commit invariant's (`raftLogN`, `raftRegN`). -/
def simNS (γ : RaftNames) : Namespace := (raftN γ).@"tracesim"

/-- **What a hook's caller gives the event builder**, by the cluster's trace mode: untraced, a nil
logger and `Q`; traced, the logger's contract and, for any event `e` the builder may log (`E e`),
the atomic update appending it to the trace and giving `Q`. -/
def TraceFire (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) : IProp GF :=
  match tr with
  | none => iprop(⌜TraceLoggerOk tl⌝ ∗ Q)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ isTraceLogger tn.tr tl ∗ ⌜tl ≠ interface.nil⌝ ∗
      ∀ e, ⌜E e⌝ -∗ AU <{ ∃∃ L, traceAuth tn.tr L }> @ ⊤, ∅ <{ traceAuth tn.tr (L ++ [e]), COMM Q }>)

/-- `QuorumLogInv`'s fact (Draft: to come from the acknowledgement-history copy of the notes' table;
until then a clause of its own). -/
def QuorumLogF (σ : Etcdraft.State) : Prop :=
  ∀ i ∈ σ.server, Etcdraft.isQuorum ((σ.getConfig i).filter (fun j =>
    or (!σ.server.contains j) (!Etcdraft.isPrefix (committedL σ i) (σ.s j).log))) (σ.getConfig i) = false

/-- **The bags' uniqueness** (the notes' `MsgsDet`/`AppSlices`): two messages in flight that a line
matches are equal, over both bags (so that a `Ready` moving pending messages out keeps it: review
round 2's A5; a receive line's message is then the one its token names). -/
def MsgsUniq (σ : Etcdraft.State) : Prop :=
  ∀ (ln : Etcdraft.Line) (m1 m2 : Etcdraft.Msg),
    m1 ∈ σ.messages.domain ++ σ.pendingMessages.domain → m2 ∈ σ.messages.domain ++ σ.pendingMessages.domain →
    recvPred ln m1 = true → recvPred ln m2 = true → m1 = m2

/-- **A message's facts** (review round 2's A3): an append request carries its source's leadership of
its term (`isLeader`: raft sends one only while leading) and its entries' records after its previous
entry (`logRecs`). -/
def msgFacts (γ : RaftNames) (C : List w64) (m : Etcdraft.Msg) : IProp GF :=
  if m.type = .appendEntriesRequest then
    iprop(∃ (src : w64) (es : List EntryM),
      ⌜m.source = idAbs src ∧ m.entries = logAbs C C.length (m.prevLogIndex.toNat + 1) es⌝ ∗
      isLeader γ src (W64 m.term) ∗ logRecs γ (entryID.mk (W64 m.prevLogTerm) (W64 m.prevLogIndex)) es)
  else iprop(True)

instance msgFacts_persistent (γ : RaftNames) (C : List w64) (m : Etcdraft.Msg) :
    Persistent (msgFacts (GF := GF) γ C m) := by
  unfold msgFacts; split <;> infer_instance

instance msgFacts_timeless (γ : RaftNames) (C : List w64) (m : Etcdraft.Msg) :
    Timeless (msgFacts (GF := GF) γ C m) := by
  unfold msgFacts; split <;> infer_instance

/-- **The specification state's facts in `simInv`** (Draft): every voter's raft facts (`allFacts`:
`MoreThanOneLeaderInv`, `LogInv`, `LogMatchingInv`, `CommitOk`, and with the vote table
`LeaderCompletenessInv`), the specification invariant `SpecInv` (`TraceSimSpecInv.lean`: with it
`ElectionSafetyInv`, `CommittedIsDurableInv`, `CommitWithinLeader`; it replaces `DurInv`, false as
stated), `QuorumLogInv`'s fact and the bags' uniqueness. -/
def simFx (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop(allFacts γ C σ ∗ (□ ∀ m, ⌜m ∈ σ.messages.domain ++ σ.pendingMessages.domain⌝ → msgFacts γ C m) ∗
    ⌜TraceSpecInv.SpecInv σ ∧ QuorumLogF σ ∧ MsgsUniq σ⌝)

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
  icases Hfx with ⟨#Hal, -, %Hp⟩
  obtain ⟨hsi, hq, -⟩ := Hp
  have hcw := hsi.commitWithinLeader
  icases allFacts_oneLeader γ C σ hsrv $$ Hal with %h1
  icases allFacts_logInv γ C σ hsrv $$ Hal with %h2
  icases allFacts_logMatching γ C σ hsrv $$ Hal with %h3
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %h4
  icases allFacts_leaderCompleteness γ C σ hsrv hcw $$ [$Htbl $Hal] with %h5
  ipureintro
  exact violated_none σ ⟨h4, h2, h1, hsi.electionSafety, h3, hq, h5, hsi.committedIsDurable⟩

/-- **The simulation's capability** on a hook path (Q8): `emp` in an untraced cluster; in a traced
one, the node's share `(cs, P)` with the function's phase `Φ C cs P` (`C` the voters, raft's
configuration `c` their permutation with no outgoing half, the node one of them: review round 1's
F4), the node's logger and its contract, and the simulation's invariant. -/
def trCap (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  match tr with
  | none => iprop(emp)
  | some γd => iprop(∃ (tn : TraceNames) (C : List w64) (tl : GoInterface) (cs : ServerC)
      (P : List Etcdraft.Msg),
      traceDir γd tn ∗ ⌜tn.voters = C ∧ (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C⌝ ∗
      r.[raft, go!"traceLogger"] ↦□ tl ∗ isTraceLogger tn.tr tl ∗
      ⌜tl ≠ interface.nil⌝ ∗ inv (simNS γ) (simInv C tn (simFx γ C)) ∗ raftLogInv γ ∗ simNode tn id cs P ∗ ⌜Φ C cs P⌝)

/-- **What a hook's caller gives for an event that may or may not be logged**: `some E`, as
`TraceFire`; `none` (a message type the hook does not trace), `Q` (review round 1's S6). -/
def TraceFireOpt (tr : Option GName) (tl : GoInterface) (oE : Option (TraceEv → Prop)) (Q : IProp GF) :
    IProp GF :=
  match oE with
  | some E => TraceFire tr tl E Q
  | none => Q

/-- **`n` events in a row** (`traceReplicate`'s loop), each `E`'s, the caller's updates nested. -/
def TraceFireN (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) : Nat → IProp GF → IProp GF
  | 0, Q => TraceFireOpt tr tl none Q
  | n + 1, Q => TraceFire tr tl E (TraceFireN tr tl E n Q)

/-- In an untraced cluster the capability is nothing. -/
theorem trCap_none (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) :
    trCap (GF := GF) none γ r id c Φ ⊣⊢ iprop(emp) := .rfl

/-- ... and so is the event builder's gate but the nil logger and `Q`. -/
theorem traceFire_none (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) :
    TraceFire (GF := GF) none tl E Q ⊣⊢ iprop(⌜TraceLoggerOk tl⌝ ∗ Q) := .rfl

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

/-- `FxPres`, in a traced cluster only. -/
def FxPresT (tr : Option GName) (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  match tr with
  | none => iprop(True)
  | some _ => FxPres γ id E Φ Φ'

/-- **The global step, as one law** (Draft statement; its proof is `simRun_lineEffect` inside the
logger's update, with the invariants from `simFx` and the bags' uniqueness): a capability in phase
`Φ`, a phase step by the events `E` and the facts kept give the event builder's gate whose update
leaves the capability in phase `Φ'`. -/
abbrev trCap_fire.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop),
  PhaseStep id c E Φ Φ' →
  (trCap (some γd) γ r id c Φ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ FxPres γ id E Φ Φ' : IProp GF) ⊢
    TraceFire (some γd) tl E (trCap (some γd) γ r id c Φ')

/-! ## The global step of a receive line (Draft statement) -/

/-- **A phase step by a receive line consuming `m`**: from every share in phase `Φ`, each event `E`
allows is a line matching `m` (its parse's `recvPred`), not bootstrap-named, with, for every server
the share stands for, an effect consuming `m` (its replies `P'` pending) into phase `Φ'`, through
intermediate states of the shape `Mid`. -/
def PhaseStepR (id : w64) (c : CfgM) (m : Etcdraft.Msg) (E : TraceEv → Prop) (Mid : Etcdraft.Server → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : Prop :=
  ∀ C cs P, Φ C cs P → (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C → ∀ e, E e → Etcdraft.isBootstrapName (gsStr e.name) = false ∧
    (∀ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln → recvPred ln m = true) ∧
    ∀ a : Etcdraft.Server, toC (confAbs C) a = cs →
    ∃ (a' : Etcdraft.Server) (P' : List Etcdraft.Msg),
      Φ' C (toC (confAbs C) a') (P ++ P') ∧
      LineEffect C false e (idAbs id) a a' (some m) (fun b => b.without m)
        (fun b => P'.foldl Etcdraft.Bag.with b) Mid

/-- **The facts kept by a receive line** (`FxPres`'s counterpart): at the result, and at every
intermediate state. -/
def FxPresR (γ : RaftNames) (id : w64) (m : Etcdraft.Msg) (E : TraceEv → Prop) (Mid : Etcdraft.Server → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  iprop(□ ∀ (C : List w64) (cs : ServerC) (P : List Etcdraft.Msg) (e : TraceEv) (a a' : Etcdraft.Server)
      (P' : List Etcdraft.Msg) (σ : Etcdraft.State),
    ⌜Φ C cs P ∧ E e ∧ toC (confAbs C) a = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
      LineEffect C false e (idAbs id) a a' (some m) (fun b => b.without m)
        (fun b => P'.foldl Etcdraft.Bag.with b) Mid ∧
      σ.server = confAbs C ∧ σ.s (idAbs id) = a ∧ σ.preVote = false ∧ σ.checkQuorum = false ∧
      σ.violated = .ok none ∧ m ∈ σ.messages.domain⌝ -∗
    votesTbl γ -∗ simFx γ C σ -∗
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => P'.foldl Etcdraft.Bag.with b)) ∗
      (∀ v, ⌜Mid v⌝ -∗ simFx γ C (withNode σ (idAbs id) v _root_.id _root_.id)))

/-- **The global step of a receive line, as one law** (Draft statement): as `trCap_fire`, the line
consuming the message of the caller's token `k`. -/
abbrev trCap_fire_recv.statement : Prop :=
  ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface) (E : TraceEv → Prop)
    (k : Nat) (m : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop),
  PhaseStepR id c m E Mid Φ Φ' →
  (trCap (some γd) γ r id c Φ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ FxPresR γ id m E Mid Φ Φ' ∗
    (∃ tn, traceDir γd tn ∗ inFlight tn k m) : IProp GF) ⊢
    TraceFire (some γd) tl E (trCap (some γd) γ r id c Φ')

/-! ## The `Commit` path, traced -/

/-- **`traceNodeEvent(evt, r)`, traced** (`traceNodeEvent.spec` with the gate): reads the logger;
nil, it returns, giving `Q`; otherwise it reads `r`'s state (`ownRaftPhysCV`, given back) to build
the event, a `NodeEvOf` one, and fires the caller's update with it. -/
abbrev traceNodeEvent.tracedSpec : Prop :=
  ∀ (evt : w64) (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  -- `evt.String()` panics past the event names (review round 1's F1)
  uint.nat evt < evtNames.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf evt id s c) Q }}
    (App (App (Val #(functions traceNodeEvent [])) (Val #evt)) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceCommit(r)`, traced**: the `Commit` line, logged at the end of `maybeCommit` (its
`defer`), with raft's commit index already moved. The caller's phase: the node's server `a` is a
leader whose `AdvanceCommitIndex` commits exactly to `n`, and the server so committed is idle-related
to `s` (`SimIdle`): the line's step. After it, the share is idle-related to `s`. -/
abbrev traceCommit.tracedSpec : Prop :=
  ∀ (c : CfgM) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      trCap s.gh.tr γ r id c (fun C cs P => ∃ (a : Etcdraft.Server) (n : Int),
        toC (confAbs C) a = cs ∧ a.state = Etcdraft.leader ∧ AdvancesTo a n ∧
        SimIdle C s (toC (confAbs C) { a with commitIndex := max a.commitIndex n }) P) ∗
      -- (review round 2's A4) the facts the line keeps, the caller's (from its node's ghost)
      FxPresT s.gh.tr γ id (NodeEvOf rsmCommit id s c)
        (fun C cs P => ∃ (a : Etcdraft.Server) (n : Int),
          toC (confAbs C) a = cs ∧ a.state = Etcdraft.leader ∧ AdvancesTo a n ∧
          SimIdle C s (toC (confAbs C) { a with commitIndex := max a.commitIndex n }) P)
        (fun C => SimIdle C s) }}
    (App (Val #(functions traceCommit [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ trCap s.gh.tr γ r id c (fun C => SimIdle C s) }}

/-- **`r.maybeCommit()`, traced** (`raft.maybeCommit.spec` with the capability): at a leader whose
share is idle-related to its state, it commits as `raft.maybeCommit.spec` says and logs `Commit`,
the specification's `AdvanceCommitIndex` (exact: `Committed()`'s quorum index is `maxAgree`), after
which the share is idle-related to the new state. -/
abbrev raft.maybeCommit.tracedSpec : Prop :=
  ∀ (c : CfgM) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗ trCap s.gh.tr γ r id c (fun C => SimIdle C s) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64), RET #b;
      ownRaftPhysCV c c.voters r id
        (if b then { s with logst := { s.logst with committed := N } } else s) ∗
      ⌜b = true → CommitOkC c (toPState s) N⌝ ∗
      trCap s.gh.tr γ r id c (fun C =>
        SimIdle C (if b then { s with logst := { s.logst with committed := N } } else s)) }}

/-! ## The other hooks, traced -/

/-- **`traceSendMessage(r, m)`, traced**: reads the logger; for a traced type (`sendEvt`), reads
`r`'s state and the message (both given back) and fires the caller's update with a `SendEvOf`
event of the message as sent (`absMsg`: `send` has stamped `From` and `Term`); for another type
nothing. A snapshot is never traced in a traced cluster (P2). -/
abbrev traceSendMessage.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq : DFrac) (ms : MsgSt)
    (tl : GoInterface) (Q : IProp GF),
  (s.gh.tr.isSome → mtypeOf ms.msg.Type' ≠ some .snap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗
      TraceFireOpt s.gh.tr tl (sendGate id s c ms) Q }}
    (App (App (Val #(functions traceSendMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗ Q }}

/-- **`traceReceiveMessage(r, m)`, traced**: at `raft.Step`'s entry, before any handling: the
receipt's event (`recvEvt`), with `r`'s state as it is. -/
abbrev traceReceiveMessage.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq : DFrac) (ms : MsgSt)
    (tl : GoInterface) (Q : IProp GF),
  (s.gh.tr.isSome → mtypeOf ms.msg.Type' ≠ some .snap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗
      TraceFireOpt s.gh.tr tl (recvGate id s c ms) Q }}
    (App (App (Val #(functions traceReceiveMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗ Q }}

/-- **`traceBecomeFollower(r)`, traced**: a `BecomeFollower` node event of `r`'s state. -/
abbrev traceBecomeFollower.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 2) id s c) Q }}
    (App (Val #(functions traceBecomeFollower [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceBecomeCandidate(r)`, traced**. -/
abbrev traceBecomeCandidate.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 1) id s c) Q }}
    (App (Val #(functions traceBecomeCandidate [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceBecomeLeader(r)`, traced**. -/
abbrev traceBecomeLeader.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 3) id s c) Q }}
    (App (Val #(functions traceBecomeLeader [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceReady(r)`, traced**. -/
abbrev traceReady.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 8) id s c) Q }}
    (App (Val #(functions traceReady [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceReplicate(r, es...)`, traced**: one `Replicate` node event per normal entry of the batch,
of `r`'s state before the append (`appendEntry` traces first). -/
abbrev traceReplicate.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (es : GoSlice) (dq : DFrac) (ents : List EntryM)
    (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entsPts es dq ents ∗
      r.[raft, go!"traceLogger"] ↦□ tl ∗ ownRaftPhysCV c c.voters r id s ∗
      TraceFireN s.gh.tr tl (NodeEvOf (W64 5) id s c) (normalCount ents) Q }}
    (App (App (Val #(functions traceReplicate [])) (Val #r)) (Val #es))
  {{ RET #(); entsPts es dq ents ∗ ownRaftPhysCV c c.voters r id s ∗ Q }}

/-! ## `send`, traced -/

/-- **`r.send(m)`, traced** (`raft.send.spec` with the capability): the message queued as
`raft.send.spec` says, then `traceSendMessage`: for a traced type, a line whose local effect takes the
caller's phase `Φ` to `Φ'` (`PhaseStep`, the message as sent, `out`'s); otherwise `Φ` kept. -/
abbrev raft.send.tracedSpec : Prop :=
  ∀ (c : CfgM) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (out : List Msg) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop),
  (m.From' = W64 0 ∨ m.From' = id ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader) →
  SendOk id s m ents ctx out →
  SnapOut id s m sn out →
  (m.Type' = MsgApp → AppShape ⟨m, ents, sn, ctx, rs⟩) →
  rs = [] →
  (s.gh.tr.isSome → mtypeOf m.Type' ≠ some .snap) →
  (match (mtypeOf m.Type').bind sendEvt with
   | some evt => ∀ mm ∈ out, PhaseStep id c (SendEvOf evt id s c mm) Φ Φ'
   | none => ∀ C cs P, Φ C cs P → Φ' C cs P) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgOwn ml (DFrac.own 1) ⟨m, ents, sn, ctx, rs⟩ ∗
      "#Hsrc" ∷ tsSrc s.gh.sn m.Type' sn ∗
      trCap s.gh.tr γ r id c Φ ∗
      -- (review round 2's A4) the facts the send line keeps, the caller's
      (match (mtypeOf m.Type').bind sendEvt with
       | some evt => [∗list] mm ∈ out, FxPresT s.gh.tr γ id (SendEvOf evt id s c mm) Φ Φ'
       | none => iprop(True)) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (sendMsgs s out) ∗ trCap s.gh.tr γ r id c Φ' }}

end ghost

end EtcdGrove
end Perennial
