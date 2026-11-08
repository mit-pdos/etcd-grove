# Q6: the node-API changes a traced cluster needs, side by side (2026-11-08)

For the user's decision (`notes/trace-validation-plan.md`, Q6; the spec skill: "a new premise or
new client-owned ghost state on a spec that has clients is the user's decision ... the old and new
statement side by side, with the alternatives"). The design they come from:
`notes/trace-validation-sim.md`, "Increment 2" (revision 12, Review clean). Each change is
**gated on a traced cluster**, `γ.raft.reTrace = some γt` (a new field of raft's cluster names,
`none` by default, as `dup`), so every existing client (raft's examples, the etcd server, all
untraced) keeps its statements but for one pure fact, item 9. The current statements are
quoted from `interface/` (abbreviated: `…` is unchanged text); the proposed ones are drafts, not
yet in Lean. Items 4 and 5 depend on Q5's choice ((a), a FIFO network); with Q5 (b) item 5 goes.

Why they are needed, in one line each, is the "because" of each item; the proofs that need them are
layer B's (S5), stepping the TLA+ state inside raft at each traced event.

## 1. `StartNode`: the trace logger and the simulation's piece of the allocation

Current (`interface/Spec/go_etcd_io/raft/v3/StartNode.txt`):

    ∀ γ N vs ctxs c cv lok si csm Q F peers dq pv,
      ConfigValid cv → … → vs = List.map Peer.ID' pv →
      TraceLoggerOk cv.TraceLogger' →                       -- Q1, increment 1: the logger is nil
      {{ isPkgInit … ∗ c ↦ cv ∗ isLogger lok ∗ nodeBoot γ N vs ctxs cv.ID' ∗ nodeVacant γ cv.ID' ∗
         AU<…raftState…> ∗ restartStorage … ∗ ownSlice peers pv dq ∗ peersCtx pv ctxs }}
        StartNode(c, peers)
      {{ nd, … isNode n γ N cv.ID' ∗ nodeDriver … ∗ nodeConfig … ∗ nodeRunning n γ N 1 ∗ Q ∗ F K … }}

Proposed:

    ∀ γ N vs ctxs c cv lok si csm Q F peers dq pv (γt : GName),
      ConfigValid cv → … → vs = List.map Peer.ID' pv →
      (cv.TraceLogger' ≠ nil ↔ γ.raft.reTrace ≠ none) →        -- logger iff traced cluster
      (cv.TraceLogger' ≠ nil → γ.raft.reTrace = some γt ∧ TracedConfigOk cv) →
      {{ isPkgInit … ∗ c ↦ cv ∗ isLogger lok ∗ nodeBoot … ∗ nodeVacant … ∗ AU<…> ∗ restartStorage … ∗
         ownSlice peers pv dq ∗ peersCtx pv ctxs ∗
         isTraceLogger γt cv.TraceLogger' ∗                       -- nil, or the generic contract
         (if γ.raft.reTrace.isSome then simNode γt cv.ID' (σ_init γt).s cv.ID' else emp) }}
        StartNode(c, peers)
      {{ nd, … (unchanged) }}

- `isTraceLogger γt tl := ⌜tl = nil⌝ ∨ □ ∀ p e Q, tracingEventRep p e -∗ AU⟨∀ L, traceAuth γt L⟩⟨traceAuth γt (L ++ [e]), Q⟩ -∗ WP tl.TraceEvent(#p) {Q}`:
  the logger only appends the event it is handed, atomically; it names nothing of the TLA+.
- `TracedConfigOk cv`: `PreVote`, `CheckQuorum`, `AsyncStorageWrites` off, `MaxSizePerMsg`
  unlimited, `MaxInflightMsgs` above a leader's appends per term (P5, P7).
- Because: the hooks fire the logger's update; the simulation needs the configuration's facts and
  each node's starting piece of the TLA+ state.
- Alternative: keep `TraceLoggerOk` (nil only) and verify only untraced runs: no closed theorem.

## 2. `RestartNode`: untraced only

Current: `… → TraceLoggerOk cv.TraceLogger' → {{ … }} RestartNode(c) {{ … }}`.
Proposed: `… → TraceLoggerOk cv.TraceLogger' → γ.raft.reTrace = none → {{ … }} RestartNode(c) {{ … }}`.
Because: the specification cannot follow a restart (gap 1); a nil-logger node in a traced cluster
would propose without a credit.

## 3. `node.Propose`: a budget credit

Current: `{{ isPkgInit … ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗ ownSlice data_sl data □ ∗ □?γ.dup AU<…ownCommittedOps…> }} n.Propose(ctx, data) {{ … }}`.
Proposed: the same, plus `∗ (if γ.raft.reTrace.isSome then propCredit γt ∗ ⌜data ≠ []⌝ else emp)`.
Because: a leader's inflights must never fill (P5: else an empty `MsgApp` carries a commit index
past its entries, gap 5); raft cannot see the workload's 60 proposals. The credits are a counter
allocated with the trace (item 8), not a list (`etc/bounds-check.py`).

## 4. `node.Advance`: the handed-out messages' tokens

Current post (abridged): `nodeDriver … {handling := none} ∗ nodeAppliedLb … ∗ (nodeConfig …) ∨ nodeStopped … ∗ nodeDriver …`.
Proposed post: both disjuncts also give, in a traced cluster, `[∗list] m ∈ tracedOut rd, inFlight γt (link m) (pos m) (msgOf m)`,
the tokens of the `Ready`'s traced messages to others (`rd.Messages` joins the driver state), at
their positions on their links (item 5).
Because: the specification moves a message to `messages` at the sender's `Ready` line and consumes
it at its receipt; the token is that message, so it is received at most once (no duplication, P6)
and only after its `Ready` (P8).

## 5. `node.Step`: a token, and with Q5 (a) the link's cursor

Current: `{{ isPkgInit … ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗ stepIn γ N id ml }} n.Step(ctx, m) {{ err, nodeErrS … }}`.
Proposed: the same, plus, in a traced cluster and for a traced message type,
`∗ inFlight γt (src, id) p mm ∗ linkCur γt (src, id) f ∗ ⌜f < p⌝` in the pre, and in the post
`linkCur γt (src, id) p` on success, `linkCur … f ∗ inFlight … p mm` back on a timeout, a stop or an
error.
Because: a voter that knows its term's leader refuses a vote the specification grants (gap 6);
with three voters and each link delivering in order, the leader's `MsgVote` comes first or never.
Without Q5 (a): the token only, no cursor.

## 6. Calls refused in a traced cluster

`node.ProposeConfChange`, `node.TransferLeadership`, `node.ReadIndex`, `node.Campaign`,
`node.ForgetLeader`: each gains `γ.raft.reTrace = none` (P3, P7: the specification models no
configuration change after bootstrap; the others look followable but are unchecked, and the harness
calls none). `ReportSnapshot`, `Status`, `Stop`, `ReportUnreachable`, `Tick`, `Ready` are unchanged.

## 7. `storBnd`: no compaction in a traced cluster

Current (`interface/Proof/go_etcd_io/raft/v3/InvNodeRule.txt`):
`def storBnd γ K c := iprop(∃ k, ⌜c ≤ k⌝ ∗ nodeAppliedLb γ K k)`.
Proposed: `iprop((∃ k, ⌜c ≤ k⌝ ∗ nodeAppliedLb γ K k) ∗ ⌜c = 0 ∨ γ.raft.reTrace = none⌝)`.
Because: a compacted log makes raft send snapshots, which the specification cannot follow (gap
3); and with it, in a traced cluster, `Ready`'s snapshot is empty (raft's `reNoSnap` mode,
revived as `reTrace.isSome`), so the client never needs `ApplySnapshot`'s bound.

## 8. `cluster_alloc`: the traced cluster's allocation

Current: `cluster_alloc N vs ctxs boot dup sl E : receiptBound GF ≤ 2^64 - 2 → vs ≠ [] → … ⊢ … ={E}=∗ ∃ γ, ⌜γ.dup = dup ∧ γ.snapLoc = sl ∧ γ.bootLen = boot.length⌝ ∗ …`.
Proposed: a new argument `tr : Option GName`, the premise
`tr.isSome → vs.length ≤ 3 ∧ dup = false ∧ boot ≠ [] ∧ receiptBound GF ≤ 2^62 - 2`, and
`γ.raft.reTrace = tr` in the post; plus a new law allocating `γt` (the trace's authority, the
budget, the link cursors) before it and the simulation's invariant at `σ_init` after it.
Because: P9 (at most three voters), the budget's tickets (no `dup`), the revived mode (a bootstrap
log), the `int` bounds of the trace's numbers (the receipt bound).

## 9. What every untraced client takes: `γ.raft.reTrace = none`

From `cluster_alloc`'s post with `tr := none`. It enters the proofs of `kvJ_bnd` (kv),
`KvrStorageApi`, `KdStorageApi` (kvreconf, kvdurable), the exported `memStorage_isStorage` (a new
premise: in a traced cluster it would be false) and so the server's `NodeStart` and
`srvMem_bootStorage`. No statement of a closed theorem changes.
