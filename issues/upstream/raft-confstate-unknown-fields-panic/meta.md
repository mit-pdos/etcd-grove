# raft-confstate-unknown-fields-panic

## Security

Not a security report: the unknown field reaches raft only in a snapshot from a peer (raft's transport) or in the
node's own storage, never from a client. The panic needs a mixed-version cluster with a raft that adds a field to
`ConfState`, which no version does yet; the issue says so.

## Candidate

- **Finding**: `issues/raft-confstate-unknown-fields-panic.md`
- **Target**: etcd-io/raft, `main` (raftpb on protobuf-go v2; v3.7.0 has the same `Equivalent`, `proto.Equal` at
  `raftpb/confstate.go:48`)
- **Branch**: `fix/raft-confstate-unknown-fields-panic` in `~/etcd-fixes/raft-confstate-unknown-fields-panic`, three
  commits (rebuilt 2026-10-18): b079b42 adds the test, which fails there; 71ca492 is the fix; 98c66a9 adds the
  changelog entry. Not pushed: the fork's branch
  (`https://github.com/upamanyus/etcd-raft/tree/fix/raft-confstate-unknown-fields-panic`, the branch the links in
  `issue.md` name) still has the earlier single commit c6921dd (test and fix together) until the user approves
  `git -C ~/etcd-fixes/raft-confstate-unknown-fields-panic push --force-with-lease=fix/raft-confstate-unknown-fields-panic:c6921dd origin fix/raft-confstate-unknown-fields-panic`.
  After the push, lines 2757-2776 of `raft_test.go` are the test (the link in `issue.md`); check on GitHub.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft, revised to the skill's standard (2026-10-18)
- **Upstream issue**: —
- **PR**: — (then replace `pull/TODO` in the changelog commit's `CHANGELOG/CHANGELOG-3.8.md` entry with its number)

etcd-io/raft has no issue template (`.github/` holds only `dependabot.yml` and `workflows`): the issue uses etcd's
bug-report sections, with "Raft version" for etcd's version and configuration sections.

## Duplicates checked (2026-10-16, again 2026-10-18)

Searches on `repo:etcd-io/raft`: `"not equivalent"`, `unknown fields`, `ConfState Equivalent`; on `repo:etcd-io/etcd`:
`"ConfStates not equivalent"` (2026-10-18). No duplicate, no open PR. Related, closed: #423 (remove
`gogoproto.nullable` from `ConfState`), #432 (pass `ConfState` as pointer); neither about unknown fields.

## Verification (go1.26.9 linux/amd64)

`TestRestoreFromSnapMsgUnknownField` (in `raft_test.go`, after `TestRestoreFromSnapMsg`, whose message it copies) is
the issue's example: a follower with peers 1, 2 steps a `MsgSnap` (index 11, term 11) whose `ConfState` is
`{Voters: [1, 2]}` plus an unknown varint field 99 (`SetUnknown`); it asserts the follower's last index is 11, i.e.
that it restored the snapshot (only the guarantee: not the configuration's details, which were `[1, 2]` before too).

- At the test commit b079b42 (`go test . -run 'TestRestoreFromSnapMsgUnknownField$'`): panics, "ConfStates not
  equivalent after sorting", from `assertConfStatesEquivalent` in `raft.restore` (`raft.go:1936`):
  `--- FAIL: TestRestoreFromSnapMsgUnknownField (0.00s)` / `panic: ConfStates not equivalent after sorting:`.
- The same message without the unknown field, at the base (a temporary test by `go test -overlay`): restores the
  snapshot (last index 11). This backs the issue's "the same snapshot without that field is restored".
- At the fix commit 71ca492: the test passes; `go test ./...` (raft, confchange, quorum, raftpb, rafttest, tracker)
  ok; `gofmt -l .` empty; `go vet ./...` clean.
- The restart path, not on the branch (the issue's "Anything else"): a temporary test applying the same snapshot to
  an empty `MemoryStorage` and calling `newTestRaft` panics at the base (from `newRaft`, `raft.go:479`; `raftpb/confstate.go`
  overlaid with the base's) and passes with the fix (voters `[1 2]`).

Not run: etcd's tests, `make verify`. Not reproduced with a real newer raft: none adds a field to `ConfState` today.

## Why the test is a direct `Step`

The trigger is a message from a node of a newer version, which the `network` harness cannot produce: its peers run
this version, and a leader holding such a `ConfState` in its own storage would itself panic in `newRaft` first. So the
test hand-delivers the message, as `TestRestoreFromSnapMsg` next to it does; nothing else in the scenario needs an
order. One test: the restart path is the same check failing on the same `ConfState`, fixed by the same line.

## If a reviewer asks

- Why the fix works: `newRaft` and `restore` rebuild the configuration from the `ConfState`'s known fields
  (`confchange.Restore`), then compare the result (`ProgressTracker.ConfState`, no unknown fields) with the input
  through `Equivalent`, which, at the base, compares sorted clones with `proto.Equal`, and `proto.Equal` also compares
  unknown fields ("the same set of unknown fields values", protobuf-go `proto/equal.go`). The fix clears the clones'
  unknown fields; the inputs are not changed, and the error message still prints them with their unknown fields.
- Why ignore unknown fields: the comparison is between a `ConfState` and the configuration this raft built from it;
  this raft never reads a field it does not know, so the field cannot make the two configurations differ for it.
  If a newer version adds a field that changes what the configuration means (a new kind of member), an older node
  restoring it is wrong either way; panicking there is a version-compatibility policy, not what `Equivalent`
  ("the inputs describe the same configuration") is for.
- Callers: `Equivalent`'s only callers are `newRaft` and `restore` (through `assertConfStatesEquivalent`); etcd
  (`main` 22cc5d9ac, `server/`, `client/`, `pkg/`, `etcdutl/`) does not call it. The only other `proto.Equal` in
  non-test raft code is `rafttest`'s empty-snapshot check, not affected.
- Alternative: compare the four sorted slices and `GetAutoLeave()` directly instead of `proto.Equal`. Same effect,
  more code, and a field added later to `ConfState` would have to be added there by hand.
- Alternative: strip unknown fields where raft receives a snapshot (or in the application). Fixes only the callers
  that do it; `newRaft` reads the storage's `ConfState` as is.
- The fix's comment ("Unknown fields, which a newer version may add, are not part of the configuration raft builds
  from a ConfState") says why they can be ignored; drop it if the maintainers prefer the line bare.
- History: before raftpb moved to protobuf-go v2, `Equivalent` compared the gogoproto structs with
  `reflect.DeepEqual`, and the generated raftpb kept no unknown fields (`goproto_unrecognized_all = false`), so this
  could not happen (checked at tag v3.6.0: `raftpb/confstate.go`, `raftpb/raft.proto`).
- Backports: v3.7.0 has the same `Equivalent`; not tried on a release branch. The changelog entry is in
  `CHANGELOG-3.8.md` (v3.8.0, Bug Fixes): v3.7.0 was released 2026-06-21, `main` is the 3.8 line, and raft keeps its
  changelogs on `main` only (`release-3.6` removed its copy; `release-3.7`'s is a stale alpha one). etcd uses v3.7.0,
  so the fix reaches etcd only with v3.8.0 or a v3.7.1 patch release, which raft has never made (3.6 stopped at
  v3.6.0; `release-3.7` has only Go bumps since v3.7.0): the maintainers' call; if wanted, cherry-pick the fix commit
  to `release-3.7` in a separate PR and add a v3.7.1 section to `CHANGELOG-3.7.md` on `main`. Since no raft version
  adds a field to `ConfState` yet, a backport matters only before a version that adds one is released.
