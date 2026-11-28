<!-- Copied from /shared/tmp/mpb-review/report.md (MPB-1's review, 2026-11-28). The /shared/tmp paths it names are not kept. Since then (MPB-2): its suggested hardening applied, pre `⌜l ≠ null⌝`, post `⌜d ≠ slice.nil⌝`; approved by coordinator-E (#50). -->

# Review: `proto.MarshalPb.spec` (trust-boundary axiom), incl. the new `⌜l ≠ null → d ≠ slice.nil⌝`

Repository `/shared/etcd-grove-deltanow`, branch `etcd-safe-crash-delta-now/2026-11-27` @ `e332fa0542`.
Axiom: `proto.MarshalPb.wp_proof` (`Proof/google_golang_org/protobuf/proto/MarshalPb.lean`), statement
`Spec/google_golang_org/protobuf/proto/MarshalPb.lean`. Go: protobuf-go v1.36.12 (module cache
`/shared/tmp/mpb-review/modcache/google.golang.org/protobuf@v1.36.12`), raft/etcd at the forks pinned by
`examples/go.mod`, go1.27.3. Read-only review: nothing edited or built in the repository.

## Verdict

**Survives (sound as stated)** for the five registered instances (`raftpb.HardState`, `raftpb.Entry`,
`raftpb.Message`, `walpb.Record`, `walpb.Snapshot`). No Go program found that marshals a non-nil `*T`
meeting the premises and gets a nil slice, a non-nil error, other bytes, or shared mutable memory.
One hardening suggestion (below): the `l ≠ null` it relies on comes from each instance's `roC`, not from
`PbModelC`; a future instance whose `roC` holds at `null` would make the *main* post (`d ↦* pbEncC I c`)
false, since Go returns `nil` for a nil `*T`.

## Evidence (protobuf-go v1.36.12)

- `proto/encode.go:105-116` `Marshal`: `m == nil` (nil interface) → `nil, nil`; otherwise
  `MarshalOptions{}.marshal(nil, m.ProtoReflect())`, and if `len(out.Buf) == 0 && err == nil`,
  `out.Buf = emptyBytesForMessage(m)`.
- `proto/encode.go:141-146` `emptyBytesForMessage`: `nil` iff `!m.ProtoReflect().IsValid()`, else
  `emptyBuf[:]`; `proto/decode_gen.go:603` `var emptyBuf [0]byte`. A non-nil generated `*T` is valid
  (test: `(*HardState)(nil).ProtoReflect().IsValid() == false`; every non-nil one gave a non-nil result).
- `proto/encode.go:174-208` `marshal`: fast path (`methods.Marshal`), `Size` first, then
  `make([]byte, 0, growcap(0, size))` when `size > 0` (`growcap(0,w) = w`, `:218`), so the buffer is
  fresh with `cap = len` (test `TestCapExact`); `MarshalUseCachedSize` is set only after the fresh
  `Size`. Errors: a `SizeMismatchError` (message changed during encoding: excluded by frozen `roC`) or
  `checkInitialized` (required fields: `raft.proto` and `walpb/record.proto` are proto2 with no
  `required` field, no strings, no maps, so no UTF-8 check and no map-order nondeterminism).
- `internal/impl/encode.go:47-129`: sizes are recomputed (`sizePointerSlow`) and cached atomically in
  `sizeCache` (`0` if `> MaxInt32-1`, forcing recomputation); `p.IsNil()` → size 0 / nothing appended.
  The writes to `state`/`sizeCache` are in raft's `pbMsg` invariant (`Proof/go_etcd_io/raft/v3/InvPbCore.lean:39`,
  existential cells), so they do not contradict the frozen cells.
- Options: `proto.Marshal` fixes `MarshalOptions{}`; `Deterministic`, `UseCachedSize`, `AllowPartial`
  are reachable only through `MarshalOptions.Marshal` (not this axiom). Tested anyway on the empty and
  small messages: identical non-nil results.

## Attacks tried (all failed)

| Attack | Result |
|---|---|
| Empty message of each type (`HardState{}`, `Entry{}`, `Message{}`, `Record{}`, `walpb.Snapshot{}`) | `nil=false len=0 cap=0`, err nil |
| Empty after `Unmarshal(nil)` | non-nil, len 0 |
| Unknown fields only (`HardState` from `38 01`) | `3801`, non-nil |
| proto2 presence of zero (`Term: &0`), empty non-nil `Data`, empty sub-entry, empty `Snapshot` | `0800`, `2200`, `3a00`, `4a00` |
| nil `*T` | `nil, nil`: excluded by the premise, every instance's `roC` has `⌜l ≠ null⌝` (`hsCells`, `entRoC`, `msgFRoC`, `walSnapRoC`, `recPtsCC`) |
| `emptyBuf` aliasing (two results, and a decoded empty `bytes` field, share `&emptyBuf`) | real, but `cap = 0`: nothing can be written; in the model `ownSlice`/`ownSliceCap` of a non-null cap-0 slice are free (`Perennial/Golang/Theory/Slice.lean:38-61`, `Array.lean` `array_empty`: an empty array points-to holds from nothing), so duplicate "own 1" copies give no contradiction |
| `append` to a returned empty slice | reallocates; a later `Marshal` still `len 0 cap 0` |
| Concurrent marshals of one frozen message sharing an `*Entry` with another parent (16 goroutines x 20000, `-race`) | 0 mismatches, no race report |
| Deep nesting / cycles (stack overflow) | only through `Message.Responses`, excluded by `marshals` (`MsgMarshals: st.resps = []`, `Proof/go_etcd_io/raft/v3/PbMessage.lean:91`) |
| Huge sizes | premise `size < 2^48`; `make` of `size` bytes below `maxAlloc` |
| Uninitialized message package (`file_raft_proto_init` not yet run) | the pre has only `isPkgInit proto`, not the message package's; in Go reachable only from raftpb/walpb's own package-variable initializers (an importer always runs after the imported package's `init`); no caller does this. Not a counterexample, noted. |
| `ProtoReflect` invalid for a non-nil `*T` | not possible for protoc-gen-go messages (`IsValid` = pointer non-nil) |

Program and output: `/shared/tmp/mpb-review/prog/mpb/mpb_test.go` (module `/shared/tmp/mpb-review/prog`,
`GOTOOLCHAIN=go1.27.3 GOFLAGS=-mod=mod go test -race -v ./mpb/`): all five tests PASS; excerpts:

```
Marshal HardState{}          nil=false len=0 cap=0 ptr!=nil=true err=<nil> bytes=
Marshal Message{}            nil=false len=0 cap=0 ptr!=nil=true err=<nil> bytes=
Marshal walpb.Record{}       nil=false len=0 cap=0 ptr!=nil=true err=<nil> bytes=
Marshal Entry{Data:[]byte{}} nil=false len=2 cap=2 ptr!=nil=true err=<nil> bytes=2200
Marshal (*HardState)(nil)    nil=true  len=0 cap=0 ptr!=nil=false err=<nil> bytes=
HardState{uf=[38 01]}        nil=false len=2 cap=2 ptr!=nil=true err=<nil> bytes=3801
same backing pointer: true, cap 0 0
decoded empty Data: nil=false same ptr as Marshal's empty: true
n=5000 len=5007 cap=5007
concurrent marshals: 0 bad of 320000, want len 28
```

## Callers

`grep MarshalPb` over `Proof/`: `encoder__encode.lean` (Record, `wp_Marshal` hypothesis at :54, :291,
:311), `pbutil/MustMarshalMessage*.lean`, `RaftModel/LawsHsMarshal.lean` (`walRaftP_marshalHs`,
`walRaftP_marshSt`), `RaftModel/LawsEnt.lean`, `RaftModel/Srv.lean`, linked in
`storage/wal/Link.lean:868`, `etcdserver/Link.lean:1280`, `RnNewStorageLinked.lean`,
`RaftModel/Laws.lean`; the WalTester copy. Each instantiates the registered instance with its
registration axiom, `marshals` trivially (`True` for the four non-Message types), the size bound by
`omega` from the encoder's length. The only user of the new conjunct is `walRaftP_marshSt`
(`LawsHsMarshal.lean:~95`), which applies it with `hn : hp ≠ null` and a frozen `hsRoC`: the Go it
models, `pbutil.MustMarshalMessage(&st)` into a `walpb.Record`'s `Data` (`wal.go`), does see a
non-nil empty slice for an all-nil hard state, which makes the record encode `Data` as present
(`1a00`); the conjunct describes that correctly. No caller violates a premise.

## Suggested hardening (not a soundness fix for today's instances)

The post's main conjunct `d ↦* pbEncC I c` is false at `l = null` for any `c` with a non-empty
encoding (Go returns `nil`). It is safe now only because every registered `roC` implies `l ≠ null`;
`PbModelC` does not require it. Either add a proved field `roC_nonnull : ∀ l c, roC l c ⊢ ⌜l ≠ null⌝`
to `PbModelC` (then the conjunct can be `⌜d ≠ slice.nil⌝`, no implication), or add `⌜l ≠ null⌝` to the
pre. Optionally also name the message package's `isPkgInit` in the pre (it is what `ProtoReflect`
reads); unreachable from a client package, so low priority.
