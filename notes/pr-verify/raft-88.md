# PR etcd-io/raft#88: `Config.DisableProposalForwardingCallback`

- PR: https://github.com/etcd-io/raft/pull/88, "Add Config.DisableProposalForwardingCallback for
  controlling message level proposal forwarding" (open; needs a rebase), head
  `ddd5443cdbc9ebab0dda6a315b19043d193b0b62`. Motivation: etcd-io/raft#73 (a stale etcd leader's
  lease revocations forwarded by its raft follower to the new leader).
- Verified at: fork branch `pr-raft-88-goose-lean` (`~/etcd-pr/raft-88`), commit `5ca594d3e`, the
  PR's non-test diff applied with `git apply -3` onto `raft37-goose-lean` `509271dac` (the pin).
- This branch: `pr-verify/raft-88` (worktree `/shared/etcd-grove-pr/raft-88`). The pin in
  `etc/goose.py` is unchanged (the fork commit is local), so `etc/goose.py --check` fails here by
  design.
- Probes and tests: `notes/pr-verify/raft-88/` (README there).

## Verdict

The change is sound as far as it was verified. `stepFollower` asks the callback only where the PR
says (a follower that knows a leader, `DisableProposalForwarding` off). It drops the proposal with
`ErrProposalDropped`, leaving the state unchanged, exactly when the callback returns true, and
otherwise forwards it as before. With a nil callback the step is the pre-PR step exactly
(`stepFollower.spec_nil_old`). A dropped proposal is a stuttering step of the protocol model, so
`raft.Step`'s spec, and with it every protocol-level result, is unchanged. No axiom or `sorry` was
added.

What it rests on is a contract on the callback that the PR's documentation does not state. The
callback must:

- return a function of the message;
- give the message back unchanged;
- not panic;
- not touch the node or the raft state.

Two Go tests at the PR head show what goes wrong without it: a callback calling `n.Status()`
wedges the node, and a callback editing the entries changes the forwarded proposal.

Not covered:

- callbacks outside that contract;
- liveness (a blocking callback);
- `MsgProp`s relayed from peers (the spec's existing scope is local proposals);
- the link between the caller's callback and the `p` that `raft.Step` and the node API see. `newRaft`
  returns `pfcbIs r pcb`, but the `RawNode`/`node` predicates do not carry it upward.

## Conflict resolutions (where the verified code differs from the PR)

1. `Config` and `raft` struct: the base has `TraceLogger` / `traceLogger` and `trk` (the PR's base
   had `prs`); the new field is added after them. No behavior change.
2. **The callback's type is `func(m *pb.Message) bool`, not the PR's `func(m pb.Message) bool`.**
   The base is raft v3.7 with protobuf-go v2 messages, where `stepFollower` holds a `*pb.Message`;
   every message in the base is passed by pointer. So the verified callback receives the very message
   raft is about to forward (the PR's receives a shallow copy, still sharing `Entries`). The spec's
   callback contract (below) requires the message back unchanged, which covers both.
3. The PR's test `TestDisableProposalForwardingCallback` is ported to pointer messages and getters
   (in the fork commit); it passes, as do all of the fork's `go test ./...`.

## Changed functions

| Package `go.etcd.io/raft/v3` | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| `stepFollower` | behavior change (a proposal with a leader may be dropped by the callback) | verified | verified | new spec `stepFollower.spec_cb` (exact); `stepFollower.spec` weakened (drop allowed), incompatible: caller `raft.Step` re-checked, absorbed; with a nil callback the old step exactly (`stepFollower.spec_nil_old`) |
| `newRaft` | behavior change (copies the new field) | verified | verified | spec gains a precondition on the new `Config` field (`pfcbImpl`, any callback meeting the contract, or nil) |
| type `Config` | new field `DisableProposalForwardingCallback` | | | `Config.validate`'s `ConfigPreserved` gains it (validate leaves it alone; re-proved) |
| type `raft` | new field `disableProposalForwardingCallback` | | | `raftOwn` (the struct's points-to) keeps it read-only with its contract |

No other function changes. No new axiom, no new `sorry` (`etc/tcb-report.py --check`: matches the
baseline, 229 axioms, 12 sorries, all pre-existing).

## The specs

- **Callback contract** (`Proof/go_etcd_io/raft/v3/InvRaftPhys.lean`, `pfcbSpec`/`pfcbImpl`/`pfcbIs`):
  `pfcbImpl f none` is `f = nil`; `pfcbImpl f (some p)` is `f ≠ nil` and, for every message pointer
  `l` and every ownership of the message (`msgPtsC l dq dqe cap ms`, at any fractions), `f(l)`
  terminates without panicking, returns `p ms` (a function of the message's contents) and gives the
  message back unchanged. It is persistent: it may use invariants but not resources raft holds, so it
  cannot call back into the raft struct or the node loop (which is blocked in `Step`).
- **`stepFollower`, old** (`lean`, `Spec/go_etcd_io/raft/v3/stepFollower.lean`): a `MsgProp` with a
  leader known is forwarded (`propForward`), never dropped.
- **`stepFollower`, new**:
  - `stepFollower.spec_cb p`: precondition adds `pfcbIs r p` (the struct's callback implements `p`);
    a `MsgProp` with a leader known is dropped with `ErrProposalDropped` and the state unchanged iff
    `pfcbDrops p ms` (the callback returns true), else forwarded as before.
  - `stepFollower.spec` (what `raft.Step` uses): the same precondition as before; a `MsgProp` with a
    leader known is either forwarded or dropped with the state unchanged (`FollowerStepResultC`).
  - `stepFollower.spec_nil_old`: from `spec_cb` with a nil callback, the old postcondition
    (`FollowerStepResultCOld`) exactly. Holds of the new code only; the PR changes nothing for a nil
    callback.
- **`newRaft`, old/new** (`Spec/go_etcd_io/raft/v3/newRaft.lean`): the new precondition
  `pfcbImpl cv.DisableProposalForwardingCallback' pcb`; the postcondition adds `pfcbIs r pcb` (the
  struct holds that callback for good), so a proof holding the struct can use `spec_cb` at the
  caller's `pcb`. Inside `ownRaftPhys` the callback is kept only as `∃ p` (`raftOwn`; read out by
  `ownRaftPhysCV_pfcb` for `stepFollower.spec`).

## Callers (step 6)

- `stepFollower` → `raft.Step` (via `r.step`): `raft.Step.spec` already allows a `MsgProp` to be
  dropped (`ErrProposalDropped`, a stuttering step `StepC.refl`); its `MsgProp` arm
  (`Proof/go_etcd_io/raft/v3/raft__Step/MsgProp.lean`) takes the new drop as the leaderless one.
  Absorbed: `raft.Step.spec` unchanged, every other arm rebuilt unchanged. Nothing above `Step`
  changes.
- `newRaft` → `NewRawNode` → `setupNode` → `StartNode`, and `NewRawNode` → `RestartNode`: each spec
  gains the same `pfcbImpl` precondition for any `pcb` (exported API: a user-visible new field,
  which the PR documents in the `Config` comment).
- `StartNode` → etcd's `bootstrappedRaft.newRaftNode` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/`)
  and the server's `NodeStartSpec` (`NodeStart.lean`): a pure premise
  `cv.DisableProposalForwardingCallback' = func.nil` (etcd sets no callback), discharged into
  `pfcbImpl _ none`. `RestartNode` → the register example (`examples/register/Main.lean`): its
  `Config` sets the field nil.
- `Config.validate`: `ConfigPreserved` gains the field (the proof's `rfl`).

## Trust base (step 7)

`etc/tcb-collections/pr-raft-88.txt` (roots: `wp_stepFollower`, `wp_stepFollower_cb` (new, in
`Proof/go_etcd_io/raft/v3/Results.lean`), `wp_newRaft`, `raft.wp_Step`, `wp_NewRawNode`,
`wp_setupNode`, `wp_StartNode`, `wp_RestartNode`, `Config.wp_validate`,
`bootstrappedRaft.wp_newRaftNode`): ten axioms, all raft's existing trust boundary
(`proto.*`, `fmt.Errorf`, `DescribeConfChange`, `raftpb.ConfChangeType.String`), no `sorry`. This
work adds no postulate.

## Findings

Bugs in the PR. These are not recorded in `issues/`, since the code is unmerged. Both are
documentation and API-contract gaps, not wrong results under a well-behaved callback. Tests are in
`notes/pr-verify/raft-88/` (README there).

1. **A callback that calls into the node deadlocks it.** The callback runs on `node.run`'s
   goroutine, inside `Step`. One that consults the node, for example `n.Status()` to ask "am I
   still the leader?" (the question issue #73 is about), waits for the loop that is running it.
   `Propose` times out, and the node never answers again. Test:
   `pr88_reentry_probe_test.go`, which fails at the PR head with `node wedged`.
   The doc comment should say that the callback runs on raft's goroutine, must not block, and must
   not call the `Node`/`RawNode`.
2. **A callback can change the proposal it lets through.** `pb.Message` is passed by value, but
   `Entries` and each entry's `Data` share storage with the message raft forwards and with the
   proposer's slice. A callback that edits an entry and returns false changes the proposal the
   leader appends. Edits of scalar fields are silently lost. Test:
   `pr88_review_mutation_test.go` (written by the reviewer), which fails with
   `ents="mutated","Xbc"`. With the base's pointer messages (the verified fork), every edit
   survives. The doc should say the callback must not modify the message.
3. Minor documentation points:
   - "called for each MsgProp message on nodes which are in follower state" is imprecise. The
     callback is not called without a known leader, or with `DisableProposalForwarding` set. It is
     called for `MsgProp`s relayed from other nodes, and for `ProposeConfChange`'s proposals (whose
     entries are conf changes, which etcd's intended callback would try to unmarshal as requests).
   - At a candidate, proposals are dropped anyway. At a stale *leader* (raft still leader), the
     callback is never consulted. That is the second root cause ahrtr raised on the PR, which the
     PR does not address.

Bugs in the existing (pinned) code: none found.

Reviewer (fresh subagent) points, and how each was resolved:

- F2: the caller's `pcb` was forgotten by the struct. Partly fixed: `newRaft` now returns
  `pfcbIs r pcb`. Still open above `newRaft` (`RawNode`/`node` predicates).
- F3: `stepFollower.spec` weakened even for a nil callback. Accepted: `raft.Step` absorbs it.
  `spec_nil_old` gives the old behavior for a nil callback, but no caller uses it, and the
  server's nil premise only discharges `pfcbImpl`.
- F5: `p` may depend on the `Responses` pointers. The comment is corrected.
- The rest confirmed the specs, the persistence of the field (written only in `newRaft`), and the
  proof's handling of the message.

## Draft review comment (for the user to edit and post)

> I went through the change in detail. The new check sits where the description says: it is
> consulted only by a follower that knows a leader and has `DisableProposalForwarding` off, a
> `true` result drops the proposal with `ErrProposalDropped` and leaves the state untouched, and a
> nil callback behaves exactly as before. Two things the `Config` comment should spell out, because
> both bite in practice:
>
> 1. The callback runs on raft's goroutine inside `Step`. If it calls back into the node (e.g.
>    `n.Status()` to check leadership), the node deadlocks: `Propose` times out and `Status` never
>    returns again. A test reproducing it is attached [pr88_reentry_probe_test.go].
> 2. Although `pb.Message` is passed by value, `Entries` and each entry's `Data` are shared with the
>    message that gets forwarded (and with the caller's slice), so a callback that edits entries
>    and returns false changes what the leader appends [pr88_review_mutation_test.go].
>
> Suggested wording: "The callback is invoked synchronously on the raft goroutine; it must not
> block, must not call into Node or RawNode, and must not modify the message." It might also be
> worth noting that it is not consulted when no leader is known, applies to conf-change proposals
> too, and sees proposals relayed from other members as well as local ones.

## Not done

- `etc/verified-code.py` before/after: not run. It counts the pinned Go source, not the PR's, and
  both changed functions were verified before and are verified after, with no `sorry`.
- The Go probes run against upstream's PR head (by-value message), not the fork.
