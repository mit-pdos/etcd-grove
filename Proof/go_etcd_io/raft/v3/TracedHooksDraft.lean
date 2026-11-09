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
configuration entries), the log uncompacted, and `P` the outbox's traced messages. -/
def SimIdle (C : List w64) (s : NState) (c : ServerC) (P : List Etcdraft.Msg) : Prop :=
  ∃ a : Etcdraft.Server, toC (confAbs C) a = c ∧ SimServerR C C.length (toPState s) a ∧
    LogShapeOk C.length (toPState s) ∧ P = pendAbs C (toPState s).outbox

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

/-- The normal entries of a batch (`traceReplicate` logs one `Replicate` per normal entry). -/
def normalCount (ents : List EntryM) : Nat := (ents.filter (fun e => decide (e.Type' = EntryNormal))).length

end pure

/-! ## The capability -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The simulation's invariant's namespace. -/
def simNS : Namespace := (nroot.@"raft").@"tracesim"

/-- **What a hook's caller gives the event builder**, by the cluster's trace mode: untraced, a nil
logger and `Q`; traced, the logger's contract and, for any event `e` the builder may log (`E e`),
the atomic update appending it to the trace and giving `Q`. -/
def TraceFire (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) : IProp GF :=
  match tr with
  | none => iprop(⌜TraceLoggerOk tl⌝ ∗ Q)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ isTraceLogger tn.tr tl ∗ ⌜tl ≠ interface.nil⌝ ∗
      ∀ e, ⌜E e⌝ -∗ AU <{ ∃∃ L, traceAuth tn.tr L }> @ ⊤, ∅ <{ traceAuth tn.tr (L ++ [e]), COMM Q }>)

/-- **The simulation's capability** on a hook path (Q8): `emp` in an untraced cluster; in a traced
one, the node's share `(c, P)` with the function's phase `Φ C c P` (`C` the voters), the node's
logger and its contract, and the simulation's invariant. -/
def trCap (tr : Option GName) (r : Loc) (id : w64)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  match tr with
  | none => iprop(emp)
  | some γd => iprop(∃ (tn : TraceNames) (C : List w64) (tl : GoInterface) (c : ServerC)
      (P : List Etcdraft.Msg),
      traceDir γd tn ∗ ⌜tn.voters = C⌝ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ isTraceLogger tn.tr tl ∗
      ⌜tl ≠ interface.nil⌝ ∗ inv simNS (simInv C tn) ∗ simNode tn id c P ∗ ⌜Φ C c P⌝)

/-- **What a hook's caller gives for an event that may or may not be logged**: `some E`, as
`TraceFire`; `none` (a message type the hook does not trace), the logger's contract (traced) and
`Q`. -/
def TraceFireOpt (tr : Option GName) (tl : GoInterface) (oE : Option (TraceEv → Prop)) (Q : IProp GF) :
    IProp GF :=
  match oE with
  | some E => TraceFire tr tl E Q
  | none => match tr with
    | none => iprop(⌜TraceLoggerOk tl⌝ ∗ Q)
    | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ isTraceLogger tn.tr tl ∗ ⌜tl ≠ interface.nil⌝ ∗ Q)

/-- **`n` events in a row** (`traceReplicate`'s loop), each `E`'s, the caller's updates nested. -/
def TraceFireN (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) : Nat → IProp GF → IProp GF
  | 0, Q => TraceFireOpt tr tl none Q
  | n + 1, Q => TraceFire tr tl E (TraceFireN tr tl E n Q)

/-- In an untraced cluster the capability is nothing. -/
theorem trCap_none (r : Loc) (id : w64) (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) :
    trCap (GF := GF) none r id Φ ⊣⊢ iprop(emp) := .rfl

/-- ... and so is the event builder's gate but the nil logger and `Q`. -/
theorem traceFire_none (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) :
    TraceFire (GF := GF) none tl E Q ⊣⊢ iprop(⌜TraceLoggerOk tl⌝ ∗ Q) := .rfl

/-! ## The `Commit` path, traced -/

/-- **`traceNodeEvent(evt, r)`, traced** (`traceNodeEvent.spec` with the gate): reads the logger;
nil, it returns, giving `Q`; otherwise it reads `r`'s state (`ownRaftPhysCV`, given back) to build
the event, a `NodeEvOf` one, and fires the caller's update with it. -/
abbrev traceNodeEvent.tracedSpec : Prop :=
  ∀ (evt : w64) (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf evt id s c) Q }}
    (App (App (Val #(functions traceNodeEvent [])) (Val #evt)) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceCommit(r)`, traced**: the `Commit` line, logged at the end of `maybeCommit` (its
`defer`), with raft's commit index already moved. The caller's phase: the node's server `a` is a
leader whose `AdvanceCommitIndex` commits exactly to `n`, and the server so committed is idle-related
to `s` (`SimIdle`): the line's step. After it, the share is idle-related to `s`. -/
abbrev traceCommit.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      trCap s.gh.tr r id (fun C cs P => ∃ (a : Etcdraft.Server) (n : Int),
        toC (confAbs C) a = cs ∧ a.state = Etcdraft.leader ∧ AdvancesTo a n ∧
        SimIdle C s (toC (confAbs C) { a with commitIndex := max a.commitIndex n }) P) }}
    (App (Val #(functions traceCommit [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ trCap s.gh.tr r id (fun C => SimIdle C s) }}

/-- **`r.maybeCommit()`, traced** (`raft.maybeCommit.spec` with the capability): at a leader whose
share is idle-related to its state, it commits as `raft.maybeCommit.spec` says and logs `Commit`,
the specification's `AdvanceCommitIndex` (exact: `Committed()`'s quorum index is `maxAgree`), after
which the share is idle-related to the new state. -/
abbrev raft.maybeCommit.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗ trCap s.gh.tr r id (fun C => SimIdle C s) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64), RET #b;
      ownRaftPhysCV c c.voters r id
        (if b then { s with logst := { s.logst with committed := N } } else s) ∗
      ⌜b = true → CommitOkC c (toPState s) N⌝ ∗
      trCap s.gh.tr r id (fun C =>
        SimIdle C (if b then { s with logst := { s.logst with committed := N } } else s)) }}

/-! ## The other hooks, traced -/

/-- **`traceSendMessage(r, m)`, traced**: reads the logger; for a traced type (`sendEvt`), reads
`r`'s state and the message (both given back) and fires the caller's update with a `SendEvOf`
event of the message as sent (`absMsg`: `send` has stamped `From` and `Term`); for another type
nothing. A snapshot is never traced in a traced cluster (P2). -/
abbrev traceSendMessage.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq : DFrac) (ms : MsgSt) (ty : MsgType)
    (tl : GoInterface) (Q : IProp GF),
  mtypeOf ms.msg.Type' = some ty → (s.gh.tr.isSome → ty ≠ .snap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗
      TraceFireOpt s.gh.tr tl ((sendEvt ty).map (fun evt => SendEvOf evt id s c (absMsg ty ms.msg ms.ents))) Q }}
    (App (App (Val #(functions traceSendMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗ Q }}

/-- **`traceReceiveMessage(r, m)`, traced**: at `raft.Step`'s entry, before any handling: the
receipt's event (`recvEvt`), with `r`'s state as it is. -/
abbrev traceReceiveMessage.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq : DFrac) (ms : MsgSt) (ty : MsgType)
    (tl : GoInterface) (Q : IProp GF),
  mtypeOf ms.msg.Type' = some ty → (s.gh.tr.isSome → ty ≠ .snap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗
      TraceFireOpt s.gh.tr tl ((recvEvt ty).map (fun evt => SendEvOf evt id s c (absMsg ty ms.msg ms.ents))) Q }}
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

end ghost

end EtcdGrove
end Perennial
