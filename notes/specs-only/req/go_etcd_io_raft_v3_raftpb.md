# Requirements on `go.etcd.io/raft/v3/raftpb` (batch 3h)

## from R1

R1's statements need the Go ownership of raftpb's messages over R1's pure models
(`Spec/go_etcd_io/raft/v3/Model.lean`). Until 3h states them, R1 declares them provisionally in
`Spec/go_etcd_io/raft/v3/Api.lean` (section "raftpb's Go ownership (provisional)"); please state
yours over the same models (or give R1 a mapping), so integration only renames:

| R1's provisional predicate | meaning |
|---|---|
| `entriesRO sl k es` | `[]*Entry` slice, read-only for good (persistent), entry `j` at index `k + j` with `es[j]`'s term, type, data |
| `msgPts p dq m` | `*Message` holding `m : Msg` (type, to, from, term, logTerm, index, entries, commit, vote, snapshot, reject, rejectHint, context; `Responses` empty) |
| `hardStatePts p dq hs` | `*HardState` |
| `snapshotPts p dq s` | `*Snapshot` with its metadata (index, term, `ConfState`) and data |
| `confStatePts p dq cs` | `*ConfState` (lists and auto-leave) |
| `confChangePts v dq c` | a `ConfChangeI` interface value: `*ConfChange` (`c = .v1 _`) or `*ConfChangeV2` (`.v2 _`) |

And these functions, specified over them:
- `MarshalConfChange(c)`: the entry type `c.entryType` and bytes `bs` with
  `decodeConfChange c.entryType bs = some c` (R1's opaque `decodeConfChange` is protobuf's
  unmarshalling of a `ConfChange`/`ConfChangeV2`: please make it your wire model); no error for a
  change built by a client. Used by `confChangeToMsg.spec`, `node.ProposeConfChange.spec`.
- `ConfChange.AsV2`, `ConfChangeV2.AsV2` (pure over `ConfChangeI`). Used by `node.ApplyConfChange.spec`.
- `EnsureSnapshot`, `EnsureConfState`, the getters through `nil` (`GetMetadata().GetIndex()`), and
  `proto.Clone` of a `Snapshot`/`ConfState` (fresh, equal model). Used by `IsEmptySnap.spec`,
  `MemoryStorage.*.spec`, `MustSync.spec`.
- A message received over the wire decodes to the `Msg` that was encoded (rafthttp, 2f, needs the
  same round trip: `msgSent γ m` travels with the bytes).
