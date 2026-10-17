# etcd-io/raft#132: track follower commit index

- PR: https://github.com/etcd-io/raft/pull/132, "raft,tracker: track follower commit index",
  open, head `e246b8d2f5d8eeae0bdbacfaf89a005cb0f2e705` (five commits, base `d475d7e4a`). It
  resolves etcd-io/raft#131.
- Verified at: fork branch `pr-raft-132-goose-lean`, commit `471242c60` (worktree
  `~/etcd-pr/raft-132`). That is the pinned `raft37-goose-lean` `509271dac` plus the PR's last
  two commits.
- Proof branch: `pr-verify/raft-132` (worktree `/shared/etcd-grove-pr/raft-132`).

## Verdict

The change is safe as far as it was verified. Every changed function is proved, against new
specs where the behavior changed, and no axiom or `sorry` was added. The full trust base is
unchanged (229 axioms, 12 `sorry`s).

- **Follower side (proved).** `handleAppendEntries` and the leader's self-acknowledgement
  (`appendEntry`) put the sender's commit index into the `MsgAppResp`'s `Commit`: the stale
  reply carries `committed`, and the accept reply carries `committed` after `maybeAppend`. The
  protocol model's messages were changed to match. The protocol proofs still go through,
  because no invariant reads an `appResp`'s `Commit`.
- **Leader side (proved only in part).** `Progress.UpdateCommit` is proved exact
  (`Commit = max(Commit, min(index, Match))`, nothing else written). From that, `Commit` never
  regresses within a `Progress` and stays at most `Match` under every `Progress` method.
  `stepLeader`'s `MsgAppResp` arm is re-proved with the new call, against its unchanged spec.
  That spec says nothing about `Commit`, so it does not establish that the leader's tracked
  value is what the follower reported.
- **The PR's documentation is wrong in two places.** Of the invariants the PR writes on the new
  field, "`Commit <= leader's commit index`" and "`sentCommit >= Commit`" are **false**. A Go
  test at the PR head shows both (Findings).
- **Nothing reads `Commit` yet.** Apart from `UpdateCommit`, it is read only by `String`, so
  the PR changes no decision. The description's "send an empty `MsgApp` only if the tracked
  index is behind" refers to `CanBumpCommit`, which is already upstream and uses
  `sentCommit`, not `Commit`.

## Applying the PR

- **Only the last two commits were applied.** The PR's first three commits (`cf5cadfd`,
  `4399f8f0`, `8b05a9d0`) landed upstream separately (`7929e3dd`, `6e9aba70`, `0f9fe526`) and
  are in the base. What was applied is `git diff 8b05a9d0 e246b8d2` (`c916c15e`, `e246b8d2`).
- **Conflicts resolved in the base's protobuf-go v2 style, with no behavior change:**
  - `raft.go`, all three message literals (`appendEntry`, both `handleAppendEntries` replies):
    pointer fields `Commit: new(...)` and `&pb.Message{...}`.
  - `stepLeader`: `m.GetIndex()`/`m.GetCommit()`.
  - `tracker/progress.go`: the base's `sentCommit` comment ("can regress in some cases") is
    kept, and the PR's added line `Invariant: sentCommit >= Commit` is kept after it, verbatim.
  - `raft_paper_test.go`'s `TestFollowerCheckMsgApp`, in the base's pointer style: `Commit`
    is expected only on accepting replies, which is exactly when the code sets it.
- The testdata changes applied cleanly. `go build ./...` and `go test ./...` pass in the fork
  worktree.

## Changed functions, types and fields

| Item | Kind | Before (lean) | After | Outcome |
|---|---|---|---|---|
| `tracker.Progress.UpdateCommit` | new | n/a | verified | new spec, exact record update; lemmas below |
| `stepLeader` | behavior change (calls `UpdateCommit`) | verified | verified | old spec re-proved, unchanged (it constrains only `Match`) |
| `raft.handleAppendEntries` | behavior change (reply `Commit`) | verified | verified | new spec, incompatible (message field); caller `raft.Step` and the model checked |
| `raft.appendEntry` | behavior change (self-ack `Commit`) | verified | verified | new spec, incompatible (message field); callers re-proved |
| `tracker.Progress.String` | output format | translated | translated | not verified (as before) |
| type `tracker.Progress` | field `Commit` added | n/a | n/a | the `Progress` record gains `commit`, tied to the field by `progressAbs` |

`etc/verified-code.py --functions --package go.etcd.io/raft/v3` reports 260 of 327 functions
verified, the same as `lean`. The script counts against the pinned Go source, which has no
`UpdateCommit`, so that function is listed as verified but not counted.

### The specs, old and new

- **`UpdateCommit`** (`Spec/go_etcd_io/raft/v3/tracker/Progress__UpdateCommit.lean`).
  - `ownProgress pr p` becomes `ownProgress pr (progressUpdateCommit p index)`.
  - Lemmas in `Proof/go_etcd_io/raft/v3/Defs.lean`:
    - `progressUpdateCommit_mono`: `Commit` does not regress.
    - `progressUpdateCommit_ok`: `Commit <= Match` is kept.
    - `progressUpdateCommit_ge`: `min(index, Match) <= Commit`.
    - `progressUpdateCommit_only`: no other field is written.
    - `progressMaybeUpdate_matched_mono`: `Match` does not regress.
    - `progressMaybeUpdate_ok`, and the `*_commit` simp lemmas: every other method leaves
      `Commit` alone.
- **`handleAppendEntries`** (`Spec/go_etcd_io/raft/v3/raft__handleAppendEntries.lean`,
  `HandleAppResult`).
  - **Old:** both accepting replies had `Commit = 0`.
  - **New:** the stale reply has `Commit = committed`, and the accept reply has
    `Commit = ls'.committed` (after `maybeAppend`). The reject reply still has 0, as in the
    code.
  - `appResp` takes the commit as a trailing argument, defaulting to 0.
- **`appendEntry`** (`Spec/go_etcd_io/raft/v3/raft__appendEntry.lean`, through `selfAck`,
  `Defs.lean`).
  - **Old:** the self-ack had `Commit = 0`.
  - **New:** the self-ack has `Commit = s.logst.committed`.
- **`stepLeader`** (`Spec/go_etcd_io/raft/v3/stepLeader.lean`): unchanged. The proof
  (`Proof/go_etcd_io/raft/v3/stepLeader/Rest.lean`, `wp_stepLeader_appresp`) now carries the
  sender's record as `progressUpdateCommit (progressMaybeUpdate p m.Index) m.Commit`, whose
  `Match` is `MaybeUpdate`'s.
- **No `spec_implies_old` lemmas.** The two message changes are incompatible by construction:
  the old postconditions pin `Commit = 0`, which the new code falsifies.

### Shared state

- **The `Progress` record** (`Defs.lean`) gains `commit`, and `progressAbs_Some` gains the
  conjunct `pv.Commit' = p.commit`. Adapted:
  - every `Progress` method proof;
  - the record constructions in `InvTracker.lean` (`progressOf`), `InvApplyConf{,C}.lean`
    and `confchange/Restore.lean`;
  - `raft__reset.lean`, whose Go literal sets no `Commit`, so `Commit' := 0`;
  - `confchange/checkInvariants.lean`'s field list.
- **The protocol model** (`Protocol/Model.lean` `Step`, and its copies `StepC`, `StepCF`
  (`StepLemmasR.lean`) and `StepR`): `appAccept`'s and `appStale`'s replies and `pselfAck`
  carry the commit index.
  - `Protocol/Refinement.lean`: `isMessage_appResp` and `ownRaftGhost_step_stale` are
    generalized over the reply's `Commit`. `snapStale` keeps 0, as `handleSnapshot` does.
  - `isMessage`'s `.appResp` arm (`Protocol/GhostState.lean`) does not mention `commit`, so no
    invariant changed.

## Callers (step 6)

- `raft.Step` (`raft__Step/repl_lemmas.lean`, `step_handle_app`): its refinement of
  `HandleAppResult` into `StepCF.appStale`/`appAccept` goes through unchanged against the new
  model.
- `raft.becomeLeader`, and the `MsgProp` arm of `stepLeader`/`raft.Step` (through `selfAck`
  and `pselfAck`, `Defs.lean`'s `becomeLeader` lemma, `raft__Step/MsgProp.lean`): rebuilt
  unchanged.
- The protocol results (`Protocol/Refinement*`, `Results.lean`): rebuilt with the two
  generalizations above.
- etcd's server, the register example, and the rest of the repository: `lake build`
  (everything) passes.

Every path stops at an unchanged spec, except the user-visible change: `MsgAppResp`s now carry
`Commit`, and `Progress` has an exported `Commit` field. The PR's description says both.

## Trust base (step 7)

- `etc/tcb-report.py --check`, after a full `lake build` of the worktree: matches
  `etc/tcb-baseline.txt` (229 axioms, 12 `sorry`s).
- Collection `etc/tcb-collections/pr-raft-132.txt` (`UpdateCommit`, `stepLeader`,
  `appendEntry`, `handleAppendEntries`, `raft.Step`, `becomeLeader`): 10 axioms and no
  `sorry`. All 10 are already in `etc/tcb-collections/raft.txt`: `DescribeConfChange`,
  `fmt.Errorf`, the `proto.*` clones/equal/size/unmarshal, and `ConfChangeType.String`. The
  raft collection's check still matches (13 axioms, 0 `sorry`s).
- No postulate or `sorry` was added.

## Findings

- **False documented invariants in the PR (doc bug, no behavior impact).** `Progress.Commit`
  is documented with "Invariant: Commit <= leader's commit index" and `sentCommit` with
  "Invariant: sentCommit >= Commit". Both fail when a follower learned a higher commit index
  from the previous leader than the new leader has.
  - The Go test `notes/pr-verify/raft-132/commit_track_pr132_test.go` (run against the PR
    head; output in `notes/pr-verify/raft-132/test-output-pr-head.txt`) uses 5 nodes. Leader 1 commits index 2, and only node 3 hears of it. Node 2
    wins term 2 with `committed=0`, and node 3's acceptance reports `Commit=2`. After that the
    leader has `committed=0` while 3's progress has `commit=2` and `sentCommit=0`.
  - True replacements: `Commit <= Match` (proved here per method); and "`Commit` is a
    committed index", which is provable if `isMessage`'s `.appResp` arm carried `isCommitted`
    up to `m.commit`. Not done here.
- **Incomplete tracking (low, informational; from review, confirmed by the reviewer's Go
  tests `notes/pr-verify/raft-132/review_commit_lag_test.go`).**
  - `handleSnapshot`'s `MsgAppResp`s carry no `Commit`, so a follower restored from a
    snapshot at `committed=11` reports 0.
  - `MsgHeartbeatResp` carries none either, so a commit learned from a heartbeat is not
    reported.
  - The leader's own `Progress.Commit` lags its `committed`: the self-ack carries the commit
    index from before `maybeCommit`.
  - None of this matters while nothing reads `Commit`. It will matter for any follow-up that
    uses `Commit` to skip sending commit updates.
- **"Commit does not regress" holds only within one `Progress` object.** `reset` (every term
  change) and re-adding a node start it at 0.
- **Durability (reviewer, by reading).** A `MsgAppResp` is released only after the storage
  append, which carries a `HardState.Commit` at least as high (`msgsAfterAppend`). So the
  reported `Commit` is durable on the follower when it is sent.
- No bug was found in the existing (pinned) code, so nothing was added to `issues/`.

### Open points (not verified)

- **`stepLeader`'s spec does not export `Commit`.** It constrains only `Match`, so the leader
  side of "the leader tracks each follower's commit index" is proved only inside the proof,
  not as a spec. Exporting it means adding a `commit` clause to `AppRespAcceptedC`, which then
  has to be threaded through the specs of `maybeCommit`, `bcastAppend`, `sendAppend` and
  `maybeSendAppend` (which today say only `prvalsMatch pvs' = prvalsMatch pvs`).
- **`PrCommitOk` (`Commit <= Match`) is a lemma per method, not a conjunct of `PrOk` or of the
  tracker invariant.**

## Draft review comment

> Thanks. Two of the invariants documented on the new fields don't hold:
> `Commit <= leader's commit index` and `sentCommit >= Commit`. A follower can learn a higher
> commit index from the previous leader than the new leader has. Example with 5 nodes: leader 1
> commits index 2, and only node 3 learns it. Node 2 then wins term 2 with committed=0. Node 3's
> MsgAppResp carries Commit=2, so the new leader ends up with `committed=0` and, for node 3,
> `Commit=2, sentCommit=0`. I can share a test. `Commit <= Match` and the monotonicity do hold.
>
> Also, `Commit` is not reported on the `MsgAppResp`s from `handleSnapshot`, or on heartbeat
> responses. And the leader's own entry lags `committed`, because the self-ack carries the
> commit index from before `maybeCommit`. That's harmless while nothing reads `Commit`, but
> worth fixing before it is used to skip commit-index updates.
