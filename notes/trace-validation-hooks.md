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

## The call sites (surveyed 2026-11-08)

| Go call | Lean call | what is held there |
|---|---|---|
| `traceInitState`, `newRaft` (raft.go:469) | `newRaft.lean:695` | `raftOwn` of the struct literal, the log, the empty tracker (before `Restore`, `loadState`) |
| `traceSendMessage` ×2, `send` (raft.go:593, 599) | `raft__send.lean:207` (`send_tail`) | opened: the queue field, the rest in the wand `Hback`; the message owned |
| `traceCommit` (deferred), `maybeCommit` (raft.go:794) | `raft__maybeCommit.lean:114` | the whole `ownRaftPhysCV` (after the commit) |
| `traceReplicate`, `appendEntry` (raft.go:849) | `raft__appendEntry.lean:272` | the whole; the cloned entries owned; before the append |
| `traceBecomeFollower/Candidate/Leader` (raft.go:917, 932, 978) | `raft__become*.lean:56/58/139` | the whole (the new role) |
| `traceReceiveMessage`, `Step` (raft.go:1112) | `raft__Step/MsgProp.lean:190` and 35 `_P.traceReceiveMessage` (`raft__Step/Base.lean:177`) | the whole and the message |
| `traceChangeConfEvent`, `stepLeader` (raft.go:1362) | `stepLeader/MsgProp.lean:209` | the whole; the decoded change |
| `traceConfChangeEvent`, `switchToConfig` (raft.go:1981) | `raft__switchToConfig.lean:68`; `newRaft.lean:452` | opened: the tracker field and the new configuration, the rest in a wand |
| `traceReady`, `acceptReady` (rawnode.go:437) | `RawNode__acceptReady.lean:715` | opened (`ownRaftPhysReady`'s fields), the tracker inside `Hclose` |

So the field and the contract are handed out persistently before the struct is opened, as
`ownRaftPhysC_shared` hands out `id` and `logger` (`InvRaftPhys.lean:1807`); the non-nil case
needs the event's state readable at the four opened sites (S4). An instrumentation detail:
`traceSendMessage` reads `r.trk.Progress[m.GetFrom()]` (the sender's own progress) for its
`match`/`next` properties, not the target's; `Traceetcdraft.tla` reads neither.

## Increment 1: the nil-logger half (decided by the agent, 2026-11-08)

The branch's build is red since the retranslation (the eleven proofs of "a no-op"). First the half
every existing result uses, which S4 does not change: `traceLogger` persistent in `raftOwn`,
`isTraceLogger tl` in `ownRaftPhysG` defined for now as `⌜tl = nil⌝` (replaced in increment 2 by
the non-nil contract, an `IProp` with a ghost name: not in place, review round 1's S6), the constructors' premise (Q1), the
eleven specs (the field and the contract, persistent, and the reads made before the nil check)
and their call sites. Options considered: the full contract first (blocked on S4's event and
update), or keeping the specs `True` with an axiom that the field is nil (a trust-base change, no).

## The question for the user (recorded per the delegation)

A new premise on public constructors with clients (`NewRawNode`, `StartNode`, `RestartNode`):
`isTraceLogger γt c.TraceLogger` (point 4) is the user's decision by the `spec` skill's policy.
Options: (a) the premise, discharged by `isTraceLogger_nil` (one line per existing client); (b) a
second spec of each constructor for a configuration with a logger (a spec family: the hard rule
"one spec per function" forbids it); (c) no premise, with the contract a configuration invariant
(`ConfigValid` gains it): the same premise, hidden. **Taken by the agent, pending the user's veto:
(a).**

## Increment 1: done (2026-11-08)

As decided above, with `TraceLoggerOk tl := tl = nil` (`InvLogger.lean`) for `isTraceLogger`. What
the call sites needed, beyond the survey: `switchToConfig`'s spec takes the field (its three
callers have the struct open), `ownRaftPhysReady` carries it (`Hf_traceLogger`, for `traceReady`),
`Config.validate` preserves `TraceLogger` (`newRaft` reads it from the validated config), and
`stepLeader` folds its decoded change into `ownConfChangeI` for `traceChangeConfEvent`
(`ownConfChangeI_v{1,2}_{intro,elim}`, `LemmasStepR.lean`). `traceChangeConfEvent` calls
`strconv.FormatUint` before its nil check: Q2 of the plan. The record: `notes/decisions.md`, "The
trace hooks' specs, increment 1: no logger".

## The update's place: decided (2026-11-08, S4 revision 3)

Point 2 left open whether the logger or raft fires the simulation's update. Decided by the agent,
after round 2 of S4's review (N4): raft. The logger's contract is generic (`isTraceLogger γt tl`:
nil, or `TraceEvent(ev)` fires the caller's atomic update on `traceAuth γt L`, appending `ev`), the
harness's recorder proves it, and the simulation is raft's invariant, each hook supplying the update
(`notes/trace-validation-sim.md`, "Increment 2"). Rejected: the logger stepping `σ` itself (it holds
neither the hook's phase facts nor the other servers'), and a contract naming the TLA+ specification
(couples every logger, and raft's constructors through Q1, to it).
