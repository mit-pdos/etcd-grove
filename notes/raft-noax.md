# Raft with no axioms (`raft-noax`)

Started 2026-11-17. Branch `raft-noax` (this repository); fork branch `raft37-goose-lean-noax` of
`upamanyus/etcd`.

## Purpose

The user's request: "I want a version of the raft proof that has NO axioms. Create a branch of the
raft repo and change the code that's currently axiomatized (e.g., delete fmt.Prints we don't have
proofs for, simplify marshalling code to avoid reflect and unsafe) so that we can prove a new
version of that axiomatized code. We should end up with a proof of raft_kvdurable_porcupine_safe
for modified code that has NO axioms." Axioms Goose itself emits for untranslatable declarations
may stay; no hand-written axiom (wp axiom or model axiom) may.

`raft_kvdurable_porcupine_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/
Results.lean`) rests, through the Go code, on these hand-written axioms: the wp axioms of
`proto.Clone` of a snapshot, a conf state and an entry (`ClonePb`, `CloneSnapshot`,
`CloneConfState`); `proto.Size` with the entry encoding model (`SizePb`, `entryEncC_ok`,
`pbEntryC_reg`); `proto.Marshal` and `proto.Unmarshal` of `ConfChange`/`ConfChangeV2`
(`MarshalConfChange(V2)`, `UnmarshalConfChange(V2)`, `ccDecodeV2_nil`); the repository's
`fmt.Errorf` specs; `DescribeConfChange`'s; and Perennial's `time.Now` (reached by
`context.WithTimeout`). The change below removes each from the Go code instead of proving
protobuf-go (reflection and `unsafe`) or the clock.

## The fork branch

`raft37-goose-lean-noax` of `github.com/upamanyus/etcd`, on project `raft`'s pin `d2c16c5`
(`etc/goose.py`, raft v3.7.0 plus the fixes), two commits, pushed:

- `4306f00` raftpb: hand-written clones, Entry size and conf change codecs (`raftpb/noax.go`,
  `raftpb/noax_test.go`);
- `91e2ea7` raft: use them, no `fmt.Errorf`, log lazily (the call sites).

Go pseudo-version: `github.com/upamanyus/etcd/v3 v3.0.0-20261117222007-91e2ea70f483`. The raftpb
message structs (protobuf-go's generated `raft.pb.go`) are unchanged, and so is every other line,
so that the existing proofs carry over.

### `raftpb/noax.go` (new)

Byte slices and integer arithmetic only; no reflect, no unsafe, no `proto`.

| Function | Replaces | Axiom removed |
|---|---|---|
| `CloneEntry(e *Entry) *Entry` | `proto.Clone` of an entry (`appendEntry`) | `proto.ClonePb` |
| `CloneConfState(cs *ConfState) *ConfState` | `proto.Clone` of a conf state | `proto.CloneConfState` |
| `CloneSnapshot(s *Snapshot) *Snapshot` | `proto.Clone` of a snapshot | `proto.CloneSnapshot` |
| `EntrySize(e *Entry) int` | `proto.Size` of an entry (`entsSize`, `limitSize`) | `proto.SizePb`, `entryEncC_ok`, `pbEntryC_reg` |
| `MarshalConfChangeV1(c *ConfChange) []byte` | `proto.Marshal` of a `ConfChange` | `proto.MarshalConfChange` |
| `MarshalConfChangeV2(c *ConfChangeV2) []byte` | `proto.Marshal` of a `ConfChangeV2` | `proto.MarshalConfChangeV2` |
| `UnmarshalConfChangeV1(data []byte, c *ConfChange) error` | `proto.Unmarshal` into a `ConfChange` | `proto.UnmarshalConfChange` |
| `UnmarshalConfChangeV2(data []byte, c *ConfChangeV2) error` | `proto.Unmarshal` into a `ConfChangeV2` | `proto.UnmarshalConfChangeV2`, `ccDecodeV2_nil` |

Helpers (unexported): `cloneUint64`, `cloneBool`, `cloneBytes`, `cloneUint64s`, `cloneUnknown`,
`cloneSnapshotMetadata`, `sizeVarint`, `appendVarint`, `appendEnum`, `appendBytes`,
`marshalConfChangeSingle`, `consumeVarint`, `consumeEnum`, `consumeField`, `consumeBytes`,
`unmarshalConfChangeSingle`; the error `errDecodeConfChange`; the tag constants.

**The clones** copy exactly what protobuf-go v1.36's `proto.Clone` copies (`internal/impl/merge.go`,
`merge_gen.go`): a nil message gives a typed nil; every set (non-nil) scalar pointer field a fresh
pointer; a bytes field nil stays nil, any other (empty included) becomes a fresh non-nil slice
(`append(emptyBuf[:], ...)`); a repeated field becomes `append(nil, s...)`, so an empty one, nil or
not, becomes nil; a set message field a fresh message, recursively; the unknown fields
(`unknownFields`, reachable from package raftpb) `append(nil, u...)`, nil when empty; the message
state and size cache zero.

**`EntrySize`** is protobuf's size formula for `Entry`: per set field a one-byte tag and the value
(an enum as the varint of its sign extension, so a negative `EntryType` takes 10 bytes; `Data`,
when non-nil, its length's varint and its bytes), plus `len(unknownFields)`.

**The encoders** emit the known fields as protobuf-go's (deterministic) `proto.Marshal` does: in
field-number order (`ConfChange`: id, type, node_id, context; `ConfChangeV2`: transition, each
change as a length-delimited field 2, context; `ConfChangeSingle`: type, node_id), only the set
ones, a nil change as an empty message. A nil message gives nil, a message with no field set a
non-nil empty slice, as `proto.Marshal`. Deliberate simplification: **unknown fields are not
encoded** (of the message or of its changes). Raft and kvdurable never make a conf change with
unknown fields; an application that passes one to `ProposeConfChange` loses them, where
protobuf-go would carry them.

**The decoders** are deliberately strict, to be simple to verify: they accept exactly the
encoders' outputs, each field at most once (the changes any number of times) in field-number
order, every varint in its shortest form (and at most 64 bits), an enum value only as the
encoding of an `int32` (below `2^31`, or the 10-byte sign extension of a negative one); anything
else (unknown fields, other orders, repeated scalars, non-canonical varints, truncation) is an
error, never a panic. The empty input gives the empty message. They reset the message first, as
`proto.Unmarshal`, copy the context out of the input (non-nil when present, even if empty) and
leave `Changes` nil when there are none. So `Unmarshal(Marshal(m))` is `m` (up to an empty
`Changes` becoming nil and a nil change an empty one), and `Marshal(Unmarshal(b)) = b` for every
accepted `b`. On what they accept they agree with `proto.Unmarshal` (which also keeps an
out-of-range value of these proto2 enums in the field, measured). Behaviour change: `stepLeader`
panics on a proposed conf change entry the strict decoder refuses (it panicked on what
`proto.Unmarshal` refused); an application proposing through `ProposeConfChange`/
`MarshalConfChange`, as etcd and kvdurable do, only ever proposes what it accepts.

### The call sites (`91e2ea7`)

- `storage.go:213,234,262` `pb.CloneSnapshot`, `:259` `pb.CloneConfState`; `log.go:295`,
  `log_unstable.go:114,196` `pb.CloneSnapshot`; `raft.go` (`appendEntry`) `pb.CloneEntry`;
  `raftpb/confstate.go` (`Equivalent`) `CloneConfState` (its comparison was already
  field-by-field, `d2c16c5`): the clone axioms.
- `util.go` (`entsSize`, `limitSize`) `pb.EntrySize`: the size axiom and the entry encoding model.
- `raftpb/confchange.go` (`MarshalConfChange`) `MarshalConfChangeV1/V2` (its error is now always
  nil); `bootstrap.go` (`Bootstrap`) `pb.MarshalConfChangeV1` (the error check removed): the
  marshal axioms.
- `raft.go` (`stepLeader`) and `util.go` (`DescribeEntry`) `pb.UnmarshalConfChangeV1/V2`: the
  unmarshal axioms and `ccDecodeV2_nil`.
- Every `fmt.Errorf` of the root package, `confchange`, `raftpb` (non-test, hand-written)
  replaced by `errors.New` with a constant message: `confchange.go` (`apply`'s unexpected type,
  `checkInvariants`' nine), `log.go` (`scan`), `types.go` (`logSlice.valid`), `raftpb/confchange.go`
  (`ConfChangesFromString`), `raftpb/confstate.go` (`Equivalent`). The messages lose their
  numbers; no test depended on them. Removes the `fmt.Errorf` specs.
- Logging only: `stepLeader`'s refused conf change passes `describedConfChange{cc}` instead of
  calling `DescribeConfChange(cc)`, and its reason is a `fmt.Stringer` (`lazySprintf`) instead of a
  string built by `fmt.Sprintf`; `newRaft` passes `hexIDs(r.trk.VoterNodes())` instead of joining
  `fmt.Sprintf("%x")`s. The three types (`util.go`) format in their `String` methods, which the
  Logger calls only if it prints (kvdurable's discards): the output is the same, and raft calls no
  formatting function on these paths. Removes `DescribeConfChange`'s axiom (and the `Sprintf`s).
  `panic(fmt.Sprintf(...))` stays (panic paths are proved unreachable).

The root package, `confchange`, `quorum` and `tracker` no longer import
`google.golang.org/protobuf/proto` (`raftpb`'s generated code still imports `protoimpl`;
`rafttest`, a test harness, still uses `proto`).

## The example: `examples/raft/kvdurablenoax`

A Go module of its own (`go.mod` replaces `go.etcd.io/raft/v3` by the fork commit above, porcupine
and lintest as `kvwitness`'s, and requires the examples' module, `=> ../..`, for
`examples/lib/durable`), a copy of `examples/raft/kvdurable` (all files, tests, `cmd/`), package
`kvdurablenoax`. Changes:

- `proto.Clone` of a snapshot (`storage.go` `image.applySnapshot`, `cluster.go` `copyMsg`) and of a
  conf state (`storage.go` `Storage.InitialState`, `kv.go` `newReplica`, `Replica.install`) by
  `pb.CloneSnapshot`/`pb.CloneConfState`; `proto.Unmarshal` of conf changes (`kv.go`
  `applyEntry`) by `pb.UnmarshalConfChangeV1/V2`. `proto.Equal` stays in `Cluster.agree`
  (`Converged`'s check, test-only, not proved).
- `context.WithTimeout(context.Background(), d)` (`Cluster.step`, `Replica.propose`,
  `Replica.read`, `Cluster.Reconfigure`, `Cluster.Disrupt`) by `withTimeout(d)` (`cluster.go`):
  `context.WithCancel(context.Background())` and `time.AfterFunc(d, cancel)`. `WithTimeout`
  computes a deadline from `time.Now`, an axiom of Perennial (`Perennial/Proof/time/Now.lean`);
  `WithCancel`, `Background` and `AfterFunc` are proved there (`context.WithCancel.wp_proof`,
  `wp_WithCancel_Background_of`, `time.AfterFunc.wp_proof` over `time.when` and
  `time.runtimeNano`, theorems). Differences, none observed by the program: `ctx.Deadline()`
  reports none, and `ctx.Err()` after the time is `Canceled`, not `DeadlineExceeded` (the code
  only tests `ctx.Err() == nil` and `ctx.Done()`); the timer is not stopped by `cancel`, and
  cancels an already canceled context when it fires.

## Test evidence (2026-11-17, go1.27.3, protobuf-go v1.36.11)

- Fork: `go vet ./...` (and with `-tags with_tla`) clean; `go test ./...` passes (all packages,
  also with `-tags with_tla`); no datadriven golden file changed (the logged texts are the same,
  and no golden file prints the reworded errors).
- `raftpb/noax_test.go`, 20000 random messages per test and run, three runs: the clones equal
  `proto.Clone` field by field, with the nil-ness of every pointer and slice and the unknown
  fields (random bytes and well-formed unknown fields), share no pointer or slice with the
  original, and are `proto.Equal` to it; `EntrySize = proto.Size`; the encoders' output equals
  deterministic `proto.Marshal` (and its nil-ness) for messages without unknown fields, nil
  changes included; decoding the encoding gives the message back and the same as `proto.Unmarshal`,
  for every presence combination, nil and empty slices, enum values in and out of range (negative
  too); garbage, mutated encodings and encodings with unknown fields are rejected or, when
  accepted, decoded as `proto.Unmarshal` does and re-encoded to the same bytes; specific
  non-canonical inputs are rejected. `FuzzUnmarshalConfChange` (the same check) ran 60 s,
  1.18 million inputs, no failure.
- `examples/raft/kvdurablenoax`: `go build`, `go vet ./...` clean. `TestAppliedAboveConfState`,
  `TestEncode`, `TestStorageRoundTrip` pass. The cluster tests (`TestPutGetRead`, `TestMain_`,
  ...) did **not** finish on 2026-11-17, and neither did the unchanged `examples/raft/kvdurable`'s
  on the same machine (both timed out at 50 min in `TestPutGetRead`, run side by side, data on
  tmpfs; one earlier run of the original passed it in 90 s, and one of the copy with `withTimeout`
  reverted to `context.WithTimeout` in 13 s). A 20 s probe of a fresh 3-voter cluster showed the
  same livelock for the original, the copy and the copy with `context.WithTimeout`: no leader,
  1250-1280 terms in 20 s (candidates never win). So the hang is not this change's (an election
  liveness problem of the randomized test under this machine's timing, to look into
  separately); the cluster tests of the copy still need a run where the original passes.
