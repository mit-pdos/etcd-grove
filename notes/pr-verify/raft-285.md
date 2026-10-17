# etcd-io/raft#285: `quorum.JointConfig` as a struct

- **PR**: etcd-io/raft#285, "refact JointConfig to To improve code understandability",
  https://github.com/etcd-io/raft/pull/285, head `aa1073bb101b9cc22b035a0d9a9c0019dbbb6ecd`
  (open; the bot says it needs a rebase; CI never ran, no `/ok-to-test`).
- **Verified at**: fork commit `e3670378d` on branch `pr-raft-285-goose-lean` (worktree
  `~/etcd-pr/raft-285`). That is the pinned `raft37-goose-lean` (`509271dac`: raft v3.7.0 plus the
  single-voter read-index fix) with the PR's diff against its merge base `8fa0e55da` applied,
  tests included.
- **Proofs**: branch `pr-verify/raft-285` (worktree `/shared/etcd-grove-pr/raft-285`).

## Verdict

The PR is a sound refactor of the code this repository verifies. Every function it changes that
had a proof before still meets its old spec, re-proved against the new translation without
`sorry`. Those functions are the whole joint-config path: `confchange`'s `EnterJoint`,
`LeaveJoint`, `Simple`, `apply`, `makeVoter`, `makeLearner`, `remove`, `initProgress`,
`checkInvariants` and `joint`; `quorum.JointConfig`'s `IDs`, `CommittedIndex` and `VoteResult`;
`tracker`'s `Config.Clone`, `ConfState` and `IsSingleton`; and `stepLeader`'s `alreadyJoint`
read. Above them, the whole raft proof (`Proof.go_etcd_io.raft.v3.Link`/`Results`) rebuilds over
the new code with the same trust base. No `[0]`/`[1]` was swapped for the wrong field.

Two problems are not about behaviour:

1. **`go vet` finds three unkeyed `quorum.JointConfig{...}` literals.** They are at
   `tracker/tracker.go:108` (`Clone`), `tracker/tracker.go:134` (`MakeProgressTracker`) and
   `rawnode_test.go:733`. They come from the vet `composites` analyzer, which flags a struct from
   another package built without field names. The repository's golangci `govet` uses the default
   analyzers, and `composites` is on by default, so lint would most likely fail. The merge base is
   vet-clean.
2. **The exported type changes shape.** `quorum.JointConfig`, `tracker.Config.Voters` and
   `raft.Status().Config.Voters` go from an array to a struct. Outside code that indexes
   `Voters[0]` stops compiling. etcd itself does not (checked on `main` and `goose-lean`). The PR
   does not say this, and has no CHANGELOG entry.

**Not covered:**
- `JointConfig.String` and `Describe` are translated but have no spec, before or after.
- `state_trace.go` is built only with the `with_tla` tag, so it is not translated.
- The test changes (`quorum/datadriven_test.go`, `raft_test.go`) were checked only by `go test`.

## Applying the PR to the fork

- `confchange/confchange.go`: one conflict. The fork's `Describe` comment says "NodeId" and its
  signature is `...*pb.ConfChangeSingle`; the PR deletes the three helpers just above it.
  Resolved by keeping the fork's `Describe` and deleting the helpers.
- `tracker/tracker.go`: one conflict in `ConfState`. The fork returns `*pb.ConfState` with
  `AutoLeave: new(p.AutoLeave)` (protobuf-go v2). Resolved by keeping the fork's version with the
  PR's field names (`p.Voters.Incoming/Outgoing.Slice()`).
- `raft.go:2144`: the fork's own read-index fix
  (`issues/raft-readindex-singleton-stale.md`) reads `r.trk.Voters[0][r.id]`, which the PR does
  not know about. It is rewritten to `r.trk.Voters.Incoming[r.id]`. This is the only line of the
  verified code that is not in the PR.
- The PR depends on no upstream commit the fork lacks.
- `go build ./...` and `go test ./...` (all six packages) pass in the fork worktree and at the
  PR's head upstream.

## Changed functions

Found by comparing the `go/ast` of the two revisions function by function (`notes/pr-verify/raft-285/astdiff/main.go`, output in `astdiff.log`). All
are refactors (the PR claims no behaviour change). "Before" is the state on `lean`; "verified"
means proved with no `sorry` of its own.

| Package | Function | Before | After | Outcome |
|---|---|---|---|---|
| quorum | type `JointConfig` | | | `[2]MajorityConfig` becomes `struct{Incoming, Outgoing}`; the spec indices follow (below) |
| quorum | `JointConfig.IDs` | verified | verified | old spec re-proved; proof rewritten for two loops (`wp_idset_for_range`) |
| quorum | `JointConfig.CommittedIndex` | verified | verified | old spec re-proved (field access instead of array element) |
| quorum | `JointConfig.VoteResult` | verified | verified | old spec re-proved |
| quorum | `JointConfig.String` | translated | translated | no spec (not needed by any caller) |
| tracker | `Config.Clone` | verified | verified | old spec re-proved |
| tracker | `ProgressTracker.ConfState` | verified | verified | old spec re-proved |
| tracker | `ProgressTracker.IsSingleton` | verified | verified | old spec re-proved |
| confchange | `Changer.EnterJoint` | verified | verified | old spec re-proved |
| confchange | `Changer.LeaveJoint` | verified | verified | old spec re-proved |
| confchange | `Changer.Simple` | verified | verified | old spec re-proved |
| confchange | `Changer.apply` | verified | verified | old spec re-proved |
| confchange | `Changer.makeVoter` | verified | verified | old spec re-proved |
| confchange | `Changer.makeLearner` | verified | verified | old spec re-proved |
| confchange | `Changer.remove` | verified | verified | old spec re-proved |
| confchange | `Changer.initProgress` | verified | verified | old spec re-proved |
| confchange | `checkInvariants` | verified | verified | old spec re-proved (only error strings changed) |
| confchange | `joint` | verified | verified | old spec re-proved |
| confchange | `incoming`, `outgoing`, `outgoingPtr` | verified | removed | specs and proofs deleted; removed as callees from `etc/link-lean-first-raft.txt` |
| raft | `stepLeader` (`MsgProp`: `alreadyJoint`) | verified | verified | old spec re-proved (`stepLeader/MsgProp.lean`) |
| raft | `sendMsgReadIndexResponse` | verified | verified | old spec re-proved (the fork's line, above) |
| raft | `traceEvent`, `traceConfChangeEvent` (`state_trace.go`) | not translated | not translated | `with_tla` build tag |

**How the specs changed (in form only).** The specs used to state a `JointConfig` value's two
halves as `a.arr = [v0, v1]` (the array's elements 0 and 1). They now state them as
`a.halves = [v0, v1]`. Here `quorum.JointConfig.halves a := [a.Incoming', a.Outgoing']`
(`Proof/go_etcd_io/raft/v3/Base.lean`), and the simp lemma `halves_eq` turns it into
`a.Incoming' = v0 ∧ a.Outgoing' = v1`.

These are the same statement: index 0 was the incoming half everywhere, and the Goose struct keeps
`Incoming` first. The reviewer checked this with a word diff of `Spec/`: apart from the three
deleted files, every change is `.arr` → `.halves` or a comment. No premise or conjunct was added
or dropped. The shared predicates using it changed the same way: `ownCfgCC` (`InvConfchange.lean`),
`ConfigVotersOnly`, `ownTracker`/`ownTrackerC` (`InvTracker.lean`, `InvTrackerC.lean`),
`LemmasStepR.lean` and `newRaft.lean`.

The new access lemmas (`jointConfig_acc_Incoming/Outgoing`, `config_acc_Incoming/Outgoing`) are
proved from the generated `AccessStrict` instances. They are not axioms.

## Callers (step 6)

No spec changed in substance, so nothing propagates. The callers that were rebuilt are:

- in `confchange`: `Restore` and `checkAndReturn`;
- in `tracker`: `Committed`, `QuorumActive`, `TallyVotes`, `VoterNodes`;
- in raft: `campaign`, `switchToConfig`, `applyConfChange`, `readOnly.maybeAdvance`,
  `newRaft`, `releasePendingReadIndexMessages`, and up to `Step`, `RawNode` and `node`;
- outside raft: the etcd server (`Proof/go_etcd_io/etcd/server/v3/etcdserver`) and the register
  example.

All of them come from the full `lake build` on the branch (see the trust base).

## Trust base (step 7)

- No axiom or `sorry` was added, and none removed: the three deleted helper proofs had none.
- On the branch, `etc/tcb-report.py --check` matches `etc/tcb-baseline.txt` (229 axioms,
  12 `sorry`s, the same file as on `lean`), and `--collection etc/tcb-collections/raft.txt --check`
  matches (13 axioms, 0 `sorry`s).
- The new collection `etc/tcb-collections/pr-raft-285.txt` (roots `confchange`, `quorum`,
  `tracker`, `stepLeader`, `sendMsgReadIndexResponse`) rests on 8 axioms. All of them are
  pre-existing trust-boundary axioms: `DescribeConfChange`, `fmt.Errorf`,
  `proto.CloneEntry/CloneSnapshot/SizeEntry/UnmarshalConfChange/UnmarshalConfChangeV2` and
  `raftpb.ConfChangeType.String`. None of them is about `JointConfig`.
- `etc/verified-code.py --package go.etcd.io/raft/v3` after the change: 257 of 327 functions
  verified, 0 unfinished. By package: `confchange` 19/23, `quorum` 7/12, `tracker` 31/35.
  On `lean`, `confchange` had three more functions, `incoming`, `outgoing` and `outgoingPtr`, all
  verified; the PR deletes them. This was not re-run on `lean`, because the script would write
  `/shared/etcd-grove/.lake/tcb.json`.
- A full `lake build` on the branch succeeds (5098 jobs), including the etcd server and the
  register example, which import the raft proofs.
- `etc/goose.py --check` fails on this branch, as expected: the raft translation is of the
  unpushed fork commit.

## Findings (step 8)

- **No bug in the PR's behaviour.**
- **Lint** (`notes/pr-verify/raft-285/vet-pr-head.log`, `vet-base.log`): `go vet ./...` at the PR's head reports `tracker/tracker.go:108:17`,
  `tracker/tracker.go:134:12` and `rawnode_test.go:733:35`, each "quorum.JointConfig struct
  literal uses unkeyed fields". The merge base `8fa0e55da` reports nothing. Fix: key them,
  `quorum.JointConfig{Incoming: ..., Outgoing: ...}`. That would also keep a later field reorder
  from silently swapping the halves.
- **API break**: the type of the exported `quorum.JointConfig` changes (see the verdict).
- **Test nit** (reviewer): `quorum/datadriven_test.go:177` changed the "zero-joint" case from an
  empty map `{}` to `nil`. The result is the same, but the empty-but-not-`nil` half is no longer
  exercised.
- **Existing findings the PR does not touch**: `issues/raft-changer-nil-incoming.md` (a `nil`
  incoming map panics in `makeVoter`/`initProgress`; now `cfg.Voters.Incoming[id] = ...`, same
  behaviour) and `issues/raft-config-clone-autoleave.md` (`Clone` drops `AutoLeave`) are both still
  there. Their premises in the specs are unchanged.
- **No new bug** was found in the existing code.
- **Reviewer's open points**: none beyond the above. Its nit about a stale comment in
  `Spec/.../JointConfig__IDs.lean` was fixed.

## Draft review comment (for the user to edit and post)

> I went through this change function by function against the current code. Every `[0]` became
> `Incoming` and every `[1]` became `Outgoing`, including the `*outgoingPtr(&cfg.Voters) = ...`
> writes in `EnterJoint`/`LeaveJoint`, which now assign the field of the same local `Config`. The
> rewrite of `IDs` into two loops builds the same set. I found no behaviour change.
>
> Two things before merging:
>
> 1. `go vet` (the `composites` check, enabled by the default `govet` in `.golangci.yaml`) now
>    flags `tracker/tracker.go:108` and `:134` and `rawnode_test.go:733`: "quorum.JointConfig
>    struct literal uses unkeyed fields". Writing them as
>    `quorum.JointConfig{Incoming: ..., Outgoing: ...}` fixes it, and also protects the literals
>    against a future reordering of the fields.
> 2. `quorum.JointConfig` is exported and reachable through `Status().Config.Voters`, so this
>    changes a public type: code that does `Voters[0]` or `len(cfg.Voters[1])` no longer compiles.
>    etcd itself doesn't do this, but it probably deserves a CHANGELOG note for v3.7/v3.8.
>
> Minor: in `quorum/datadriven_test.go` the "zero-joint quorum" case went from `{c, {}}` to
> `{c, nil}`, so the empty-but-non-nil half is no longer tested.
