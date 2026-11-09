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

### from R1, round 1

- **`bootEntryData id ctx`** (R1's `Model.lean`, opaque): the bytes `proto.Marshal` gives
  `ConfChange{Type: AddNode, NodeId: id, Context: ctx}` (presence included; `Id` absent), a
  function of the message; and the law `bootEntryData_decode.spec` (`Api.lean`): for a non-empty
  `ctx` it decodes to `.v1 ⟨AddNode, id, ctx, 0⟩`. Used by `BootLog` (`StartNode.spec`,
  `RawNode.Bootstrap.spec`): founders must append the same bytes.
- **Presence**: the ownership predicates (`snapshotPts`, `confStatePts`, `hardStatePts`, `msgPts`)
  imply every optional sub-message and field `Ensure*` would fill is present (so `EnsureSnapshot`/
  `EnsureConfState` write nothing, and `MemoryStorage.InitialState` reads without the lock), and
  `msgPts` a non-nil pointer.

## from R3

Batch R3 (raft's log: `Spec/go_etcd_io/raft/v3/ApiLog.lean`, `raftLog__*`, `unstable__*`, util)
declares one more provisional predicate, over R1's `LogEntry`:

| R3's provisional predicate | meaning |
|---|---|
| `entryRO p k e` | one `*Entry`, read-only for good (persistent), at index `k` (its `Index` field `W64 k`), with `e`'s term, type and data: the element of R1's `entriesRO` (`entriesRO sl k es ⊣⊢ ∃ ps, sl ↦*□ ps ∗ [∗list] j ↦ p ∈ ps, entryRO p (k + j) es[j]`, a law R3's sketches use to index a slice) |

And these, specified over them:
- the getters `GetIndex`, `GetTerm`, `GetData`, `GetType` of an `entryRO` (no panic, its fields).
  Used by `pbEntryID.spec`, `payloadSize.spec`, `unstable.acceptInProgress.spec` (the last entry's
  `GetIndex() + 1` is `offset + |ents|`), `raftLog.findConflict.spec`.
- `(*ConfState).Equivalent(cs2)`: `nil` exactly when the two list the same configuration
  (`ConfState.Equiv` in `ApiLog.lean`: each list a permutation of the other's, the same
  `AutoLeave`); it must not mutate either (it sorts copies). Used by
  `assertConfStatesEquivalent.spec`.
- `proto.Clone` of a `*Snapshot` held by `snapshotPts p dq s` (any `dq`): a fresh
  `snapshotPts p' (own 1) s` (R1 asked the same). Used by `raftLog.restore.spec` (`unstable.restore`),
  `raftLog.snapshot.spec`, `raftLog.nextUnstableSnapshot.spec`.
- `ConfChangeI.AsV2()` and `ConfChangesToString` without panic on a `confChangePts` value. Used by
  `DescribeConfChange.spec`.

## from R2

- `ConfChange.AsV2`/`ConfChangeV2.AsV2`: a law `Membership.applyChange (.v2 (asV2 c)) =
  Membership.applyChange c` (R2's `raft.applyConfChange.spec` takes it as a premise over the
  `*ConfChangeV2`), and an ownership predicate for a `*ConfChangeV2` (R2 uses R1's `confChangePts`
  at the pointer as a `ConfChangeI` interface value).
- `entryPtrs sl dq es` (R2's provisional, `ApiCore.lean`): a `[]*Entry` with the terms, types and
  data of `es`, any `Index` (a proposal's entries before numbering).
- `MarshalConfChange(nil)` (the auto-leave proposal, `appliedTo`): type `EntryConfChangeV2`, no
  data, and `decodeConfChange EntryConfChangeV2 [] = some (.v2 ⟨0, [], []⟩)` (R2's `stepIn` asks
  conf entries to decode).
- `msgPts`: splitting off a received message's snapshot (`handleSnapshot` → `restore`, read-only)
  and entries (`handleAppendEntries` adopts the entry pointers read-only); a message built with a
  shared read-only snapshot or entry slice (`newStorageAppendRespMsg`, `newStorageApplyRespMsg`).
- `EnsureSnapshot`, `EnsureConfState`, the getters through `nil` (`GetMetadata().GetIndex()`).

### from R1, round 2

- **`proto.Clone` of a `*Message`**: from `msgPts p dq m`, a fresh `msgPts p' (DFrac.own 1) m`
  (`examples/specreq/raftnode/transport.go`'s `ReqDeliver` steps a copy, as the examples'
  `copyMsg` does).
