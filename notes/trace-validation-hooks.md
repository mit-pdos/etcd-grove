# Draft S3: the trace hooks' and logger's specs (design, 2026-11-08)

Part of `notes/trace-validation-plan.md` (layer A). The eleven hooks of raft's `with_tla` build
(`state_trace.go`, translated from the local fork commit) replace eleven no-op specs
(`Spec/go_etcd_io/raft/v3/trace*.lean`, "a no-op ... owns nothing").

## What the code does (the translation, 2026-11-08)

- Nine hooks read `r.traceLogger` first and return when it is nil: `traceInitState`,
  `traceConfChangeEvent`, `traceSendMessage`, `traceReceiveMessage`, and through `traceNodeEvent`
  -> `traceEvent` the node events (`traceReady`, `traceCommit`, `traceBecomeFollower`,
  `traceBecomeCandidate`, `traceBecomeLeader`).
- **Two do work before that check**, so their specs need more even with no logger:
  - `traceReplicate(r, es...)` reads each entry's type (`es[i].GetType()`) and calls
    `traceNodeEvent` for each normal one: read access to the entries;
  - `traceChangeConfEvent(cci, r)` calls `cci.AsV2()`, loops over its changes (`GetType`,
    `GetNodeId`), formats ids (`strconv.FormatUint`) and allocates the `TracingConfChange` before
    `traceEvent`'s check: the change's model and `AsV2`'s and the getters' specs.
- With a logger, `traceEvent` reads the node's state (`hardState()`: term, vote, commit;
  `raftLog.lastIndex()`; `trk.Voters[0/1].Slice()`; `state`; `id`), formats it into a fresh
  `TracingEvent` and calls `r.traceLogger.TraceEvent(ev)`; `traceReceiveMessage` first sleeps 1ms
  (`time.Sleep`, Perennial's spec); `traceSendMessage` adds `prop["match"/"next"]` from the
  progress tracker for `MsgApp`.

## The design

1. **The field**, as raft's `Logger` (`InvRaftPhys.lean`: `rv.logger' = interface.ok lok` and
   `isLogger lok`): `ownRaftPhys` holds `traceLogger` persistently (`↦□`, never written after
   `newRaft`) with `isTraceLogger γt tl`, the logger's contract (below), persistent. `newRaft`
   copies it from the `Config` (today `H_traceLogger ∷ l.[raft, "traceLogger"] ↦ v.traceLogger'`,
   writable: becomes `↦□` there).
2. **The contract** `isTraceLogger γt tl`: `tl = nil`, or `tl = ok tlok` with the triple of
   `TraceEvent` (stored as a method triple, `examples/apply-uber-contract.md`: one contract,
   established by whoever constructs the logger, the trace harness): an atomic update the
   implementation fires inside its lock, appending the event to the trace ghost `γt`. Its exact
   form is S4's (the simulation decides what the update's grant and post are); the hooks' specs
   pass it through.
3. **The hooks' specs** (one each, the hard rule "one spec per function"): the field and the
   contract (persistent), the reads the code makes (for the two above, even when nil), and in the
   non-nil case the node's state the event is computed from, handed to the contract as the
   abstract event `eventOf kind s msg` (term, vote, commit, role, log length, configuration, the
   message's fields: the Lean counterpart of `ConvertEvents`). With `tl = nil`: no effect.
4. **The constructors' premise**: `NewRawNode`, `StartNode`, `RestartNode` take
   `isTraceLogger γt c.TraceLogger` for the configuration's field, with the law
   `isTraceLogger_nil : ⊢ isTraceLogger γt nil`, so a client that sets no logger (every client
   today: `StartCluster` sets `TraceLogger' := GoInterface.nil`) discharges it in one line.

## Open: what S4 settles before the Lean of points 2-3

- **Where the hooks are called from and what is held there.** Several are called mid-update (the
  struct's fields owned one by one, not as `ownRaftPhys`): `becomeLeader` after setting the state,
  `send` while the message is being built, `Step` at entry. The non-nil spec must take only what
  every call site holds; a survey of the twelve call sites (`raft.go`, `rawnode.go`) comes first.
- **The ghost the update acts on.** The trace and the specification's state `σ` (layer B) are
  cluster-wide: the update's precondition is the cluster's ghost (raft's cluster invariant), and its
  grant at a node's event needs that node's protocol state at that moment. Whether the hook gives
  the event with a certificate of the node's state (and the simulation fires in the logger) or raft
  fires the update itself is S4's choice.

## The question for the user (recorded per the delegation)

A new premise on public constructors with clients (`NewRawNode`, `StartNode`, `RestartNode`):
`isTraceLogger γt c.TraceLogger` (point 4) is the user's decision by the `spec` skill's policy.
Options: (a) the premise, discharged by `isTraceLogger_nil` (one line per existing client); (b) a
second spec of each constructor for a configuration with a logger (a spec family: the hard rule
"one spec per function" forbids it); (c) no premise, with the contract a configuration invariant
(`ConfigValid` gains it): the same premise, hidden. **Taken by the agent, pending the user's veto:
(a).**
