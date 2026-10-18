# raft-confstate-unknown-fields-panic

- **Finding**: `issues/raft-confstate-unknown-fields-panic.md`
- **Target**: etcd-io/raft, `main` (raftpb on protobuf-go v2; v3.7.0 has the same `Equivalent`)
- **Branch**: `fix/raft-confstate-unknown-fields-panic` in `~/etcd-fixes/raft-confstate-unknown-fields-panic` (commit c6921dd56), pushed 2026-10-18 to `upamanyus/etcd-raft`
  (`https://github.com/upamanyus/etcd-raft/tree/fix/raft-confstate-unknown-fields-panic`), the branch the links in `issue.md` name.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

etcd-io/raft has no issue template (`.github/` holds only `dependabot.yml` and `workflows`): the issue uses etcd's
bug-report sections, with "Raft version" for etcd's version and configuration sections.

## Duplicates checked (2026-10-16)

Searches on `repo:etcd-io/raft`: `"not equivalent"`, `unknown fields`, `ConfState Equivalent`. No duplicate. Related,
closed: #423 (remove `gogoproto.nullable` from `ConfState`), #432 (pass `ConfState` as pointer); neither about
unknown fields.

## Verification

`TestRestoreFromSnapMsgUnknownField` (in `raft_test.go`, next to `TestRestoreFromSnapMsg`) is the issue's example: a
follower with peers 1, 2 steps a `MsgSnap` (index 11, term 11) whose `ConfState` is `{Voters: [1, 2]}` plus an
unknown varint field 99 (`SetUnknown`); it asserts the follower's last index is 11.

- At the base (fix reverted, test kept): `go test . -run 'TestRestoreFromSnapMsgUnknownField$'` panics, "ConfStates not
  equivalent after sorting", in `assertConfStatesEquivalent` from `raft.restore` (`raft.go:1936`).
- With the fix: the test passes; `go test ./raftpb/ .` ok; `gofmt -l raftpb raft_test.go` empty; `go vet ./raftpb/ .`
  clean (go1.26.9 linux/amd64).
- The restart path, not on the branch: a temporary test applying the same snapshot to a `MemoryStorage` and calling
  `newTestRaft` panics at the base (from `newRaft`, `raft.go:479`) and passes with the fix (voters `[1 2]`).

Not run: the rest of the module (`rafttest`, `confchange`, `quorum`, `tracker`; the fix is in `raftpb` only, which
they do not reach except through `Equivalent`'s two callers in package `raft`), etcd's tests, `make verify`. Not
reproduced with a real newer raft: none adds a field to `ConfState` today.

## If a reviewer asks

- Why ignore unknown fields: the comparison is between a `ConfState` and the configuration this raft built from it;
  this raft never reads a field it does not know, so the field cannot make the two configurations differ for it.
  If a newer version adds a field that changes what the configuration means (a new kind of member), an older node
  restoring it is wrong either way; panicking there is a version-compatibility policy, not what `Equivalent`
  ("the inputs describe the same configuration") is for.
- Alternative: compare the four sorted slices and `GetAutoLeave()` directly instead of `proto.Equal`. Same effect,
  more code, and a field added later to `ConfState` would have to be added there by hand.
- Alternative: strip unknown fields where raft receives a snapshot (or in the application). Fixes only the callers
  that do it; `newRaft` reads the storage's `ConfState` as is.
- History: before raftpb moved to protobuf-go v2, `Equivalent` compared the gogoproto structs with
  `reflect.DeepEqual`, and the generated raftpb kept no unknown fields (`goproto_unrecognized_all = false`), so this
  could not happen (checked at tag v3.6.0: `raftpb/confstate.go`, `raftpb/raft.proto`).
- The error message still prints the inputs with their unknown fields; the sorted clones no longer show them.
