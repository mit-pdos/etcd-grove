# Batch 3h, review round 1 (provability and completeness)

Reviewer: independent of the author. Commit under review: `a04eb12a12` (the 3h draft; round 1, so
nothing is stale). Read: `notes/specs-only/{README,review-brief,batch-3h}.md`, every file of
`Spec/go_etcd_io/raft/v3/raftpb/`, `Spec/go_etcd_io/etcd/api/v3/{etcdserverpb,version}/` (Api,
Realize, the Ensure/Marshal/Equivalent/AsV*/EnterJoint specs, a sample of getters, stubs, handlers,
registrations), 2a's `Spec/google_golang_org/protobuf/proto/*.lean`, W0's `api/v3/Wire.lean`, the
`req/` files addressed to 3h, the snippets, and the Go code (raft `565c2bd`, etcd `a4d2bb17`,
protobuf-go v1.36.12). I did not rebuild (the `.olean`s of the batch are present).

## Verdict

The design is right and the old bug does not recur in the form it had: no wire model is built by a
caller, no encoding is keyed by an address, decoding is a function only through `Proto.encodes_fun`,
and every relation (`entryIs`, `msgIs`, `reqHolds`, ...) is functional in the content and keeps the
integer ranges and presence that would otherwise break functionality (W0's range premises; the
bootstrap literal's non-empty context). But the content-keyed design moves the consistency question
to **2a's generic specs over `msgAt`**: once 3h's relation laws say what `msgAt` of a raftpb message
is (read-only-for-good submessages and slices without capacity), 2a's `Merge.spec`, instantiated at
those types, is false of protobuf-go. That is the one soundness finding; it is fixable with a premise.
The rest is a small hole in `MarshalConfChange`'s post (R2's request not met), snippets that call
untranslated or unspecified functions, and getters stated over `msgAt` with no law to prove them.
**Not done**: one first-tier soundness finding (F1), one first-tier user-not-served (F2), snippet
repairs (F3), and the recorded open dependencies (F4).

Note on what is provable here: `Proto.msgAt` is 2a's opaque trust-boundary predicate, and the
repository has no realization of it. So 3h's relation laws (`*_msgAt`) can't be proved in this
repository: like 2a's specs, they are assumptions about protobuf-go's generated code. The header's
"obligations of that realization" wording hides this. It matters because it makes the whole set
(2a's specs together with 3h's and W0's relation and unfold laws) one body of assumptions, which
must be **jointly** true of the Go code. F1 is a failure of that joint truth.

## First tier

### F1. `Merge.spec` (2a) with the raftpb and W0 relation laws gives a wrong program-level fact (unsound)

*Principle*: assumptions must be true of the code at every instance; a generic trust-boundary spec is
true only of the realizations its owners give it.

*Evidence*. `proto.Merge(dst, src)` writes `dst` **in place**:
- a set submessage of `dst` is merged into the existing one, not replaced
  (`google.golang.org/protobuf@v1.36.12/internal/impl/merge.go:159-171`, `mergeMessage`:
  `f.mi.mergePointer(dst.Elem(), ...)`);
- a repeated field is appended in place (`merge.go:175-184`, `AppendPointerSlice`, `pointer_unsafe.go:137`:
  `*(*[]pointer)(p.p) = append(...)`; `merge_gen.go:130`, `mergeUint64Slice`: `*ds = append(*ds, *ss...)`),
  which writes into the destination slice's spare capacity when it has some.

2a's `Merge.spec` (`proto/Merge.lean`) takes only `msgAt t p (own 1) c`, for every `t`. 3h's
`msgPts_msgAt` with `msgPts_unfold` (`raftpb/Api.lean`) says that `msgAt Message.ty p (own 1) c` holds
its `Snapshot` at `DFrac.discard` (`snapshotPts sp DFrac.discard s`) and its `Entries` slice as
`sl ↦*□ eps`, with no capacity. A `MsgApp`'s `Entries` is a sub-slice of the leader's log with
capacity beyond `len` (`util.go:286-297`, `limitSize` returns `ents[:limit]`). So the derivable triple
"`proto.Merge(m, m2)` with `msgPts m (own 1) _` leaves the persistent `snapshotPts sp □ s` and
`entriesRO` of the log unchanged" is false: Merge rewrites the shared snapshot's fields and overwrites
the log's entry pointers past `len`. The same holds for `ConfState` (`confStateGo`: `vs ↦*{dq}`
without capacity) and for W0's `rangeRespOwn` (`msgsOwn keyValueOwn kvs dq`: no capacity). On W0's
own path, `GetStreamToGetResponse`'s second `Merge` (`client/v3/kv.go:99-108`) appends into the
slice the first `Merge` allocated, whose capacity the predicate does not record.

No caller merges raft messages today, so nothing *wrong* is proved yet. But the assumptions are
inconsistent with the code, which is exactly the shape of the old `pbEnc_ok` bug.

*Callers affected*: W0's `GetStreamToGetResponse.spec`, snippet `etcdserverpb/merge-range`; potentially
any client of `raftpb`.

*Fix* (2a and 3h together): give `Merge.spec` a per-type premise that the owner discharges, e.g. an
opaque `Proto.mergeDst t p c` (or "`dst` is a fresh message or one built only by `Merge`"), with
3h stating it only for `RangeResponse` (a law `rangeRespOwn p (own 1) m ⊢ mergeDst ...` that needs
the `Kvs` capacity: either W0's unfold at `own 1` owns `own_slice_cap` of `Kvs`, or the law only
holds for `&pb.RangeResponse{}` and for what `Merge` returns). State in 2a's header that every
generic spec over `msgAt` is checked against each owner's relation laws (a line per spec: Clone
reads, Size and Marshal write only `sizeCache`, Unmarshal resets then writes fresh cells, Merge
writes in place).

### F2. `MarshalConfChange(nil)`: the post does not say "no data" (R2's request not met; snippet unprovable)

*Evidence*. `raftpb/MarshalConfChange.lean`: for `o = none` the post is `∃ bs, b ↦* bs ∗ ⌜t = ... ∧
decodeConfChange t bs = some (.v2 ⟨Auto, [], []⟩)⌝`. Nothing pins `bs = []` or `b = slice.nil`, though
the Go code returns `ccdata = nil` (`raftpb/confchange.go:42-46`) and the docstring says so. R2 asked
for "type `EntryConfChangeV2`, no data" (`req/go_etcd_io_raft_v3_raftpb.md`, "from R2"), because the
auto-leave entry's zero payload is what lets `increaseUncommittedSize` never refuse it (the code's
comment). The snippet `raftpb/auto-leave` panics on `len(data) != 0`: unprovable.

*Fix*: add `⌜o = none → b = slice.nil ∧ bs = []⌝` to the post (or split the two cases).

### F3. Snippets that are unprovable as written

- `etcdserverpb/kv-stub` (`resp.GetHeader()`), `etcdserverpb/nil-header` (`r.GetHeader()`),
  `etcdserverpb/txn-response-getters` (`rr.GetHeader()`) call `PutResponse.GetHeader` and
  `RangeResponse.GetHeader`, which are untranslated (`Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`
  lists only the four lease responses' `GetHeader`) and have no spec. No verified user calls them:
  the client and the cache read `resp.Header` directly. *Fix*: read the field (W0's unfold laws),
  or translate and specify the getters if a user needs them.
- `raftpb/auto-leave`: F2.
- `raftpb/bootstrap-bytes`: needs 2a's `marshalOut` (determinism), not yet in the boundary
  (recorded as open question 5). `etcdserverpb/sort-names` needs the two maps translated (open
  question 1). These are honest open dependencies; leave them listed, but they are unprovable today.
- `proto.Uint64`/`proto.Bool` (in `raftpb/field-write`, `marshal-decode`, `asv2`, `enter-leave`,
  `equivalent`, `ensure`, `bootstrap-bytes`) have no spec anywhere (2a's `proto` is names only, and
  2a specifies only Clone/Equal/Marshal/Merge/Size/Unmarshal). The verified code uses `new(x)`
  (raft `node.go:388`, `raft.go:1743`; etcd `storage/util.go:77`). *Fix*: write `new(id)` in the
  snippets, which the snippets' Go toolchain accepts, as raft's code shows.

### F4. Users not served, recorded as open questions (need a decision before integration)

- **2c's `irrOwn`, `alarmReqOwn`, and 2e's `irrIsRevoke`** (`ApiReq.lean:278,282`, `ApiBoot.lean:249`):
  nothing replaces them, nor the request "`proto.Marshal` of an `irrOwn` message ... every member's
  apply decodes back to `ir`" (`req/go_etcd_io_etcd_api_v3_etcdserverpb.md`, "from 2c"). This is the
  raft payload of every write: the request path (2c) and the apply thread (2d) both stand on it.
  The author's proposal (open question 4: move `IrrBody` down, add `irrHolds` with laws shaped like
  `reqHolds`) is sound; it should be decided now, not at integration.
- **2e's request 2** (`v3electionpb`/`v3lockpb` ownership: `campaignReq`, `lockReq`, ... in
  `V3election`/`V3lock` `Api.lean`): not mentioned in the batch report, not even as out of scope.
  Say whose it is.
- Translation gaps (open question 1): `Member*`/`StatusResponse`/`AlarmResponse` fields (1c's
  `Client.Sync`, `MemberList`, `Status`), `RangeStream` stub and handler (which `remoteKVAt_methods`
  includes: `NewKVClient.spec` can't be proved until it is translated),
  `NewClusterClient`/`NewMaintenanceClient`, `Event.IsCreate`/`IsModify` (1b, Kubernetes),
  `RangeRequest_Sort*_name` (W0). Recorded. Each one blocks a stated spec.

## Second tier

1. **Getters over `msgAt` with no law to prove them.** `LeaseGrantResponse.GetHeader`,
   `LeaseKeepAliveResponse.GetHeader`, `LeaseLeasesResponse.GetHeader`,
   `LeaseTimeToLiveResponse.GetHeader` take `Proto.msgAt T.ty p dq c` and return `optOwn respHeaderOwn h
   dq ho` with a wand back. Their proof sketch is "the realization of `msgAt` at this type", which
   this repository does not have (see the note under the verdict). The body is translated, so the
   proof needs a field-level law over `msgAt` for these types. *Fix*: state one law per type
   (`msgAt LeaseXResponse.ty p dq c ⊢ ∃ h ho, p.Header ↦{dq} h ∗ optOwn respHeaderOwn h dq ho ∗ (… -∗
   msgAt …)`), flagged as an assumption of the realization, or give these responses a 3h predicate
   with an unfold law and a relation law (as `replyOwn_lease` does for `replyOwn`).

2. **The `ConfState` getters take only `confStatePts`.** A holder of `confStateFull` (every snapshot's
   conf state: `SnapshotMetadata.GetConfState` returns it) must weaken to `confStatePts` to call
   `GetVoters`/`GetAutoLeave`/..., and gets back only `confStatePts`, so it can't close the
   `snapMetaGo` wand without splitting fractions by hand through the unfold laws (possible: half
   kept, field agreement). `ReqEnsure` (`s.GetMetadata().GetConfState().GetAutoLeave()` on an owned
   snapshot) is provable only that way. The `SnapshotMetadata` getters are already parametric in
   `full`. *Fix*: the same for the `ConfState` getters (over `confStateGo p dq cs full`), or two
   conjuncts. Likewise, `Snapshot.Get*` take only `snapshotPts` (full): no getter serves a
   `snapshotRaw` holder (a client-built snapshot before `EnsureSnapshot`; the snapshotter's decoded
   snapshot if 2e does not prove it full).

3. **`pbRest_zero` (and 2a's `msgAt_persist`) are pure entailments/`|==>`, but `Size`/`Marshal` store
   `sizeCache` atomically at any fraction** (`internal/impl/encode.go:67`, `atomic.StoreInt32`), also
   in a submessage shared at `DFrac.discard`. A realization that keeps `sizeCache` writable at `□`
   needs an invariant, which neither `⊢` nor `|==>` can allocate. *Uncertain*: it depends on how the
   untranslated callee's writes are modelled. *Fix*: `pbRest_zero.spec` as `⊢ |={E}=>` (and ask 2a for
   `msgAt_persist` under `|={E}=>`), or say in 2a's header that `sizeCache` is outside the Goose heap
   the specs talk about.

4. **2a's `Content` must carry its message type** for `holds_fun` to be consistent across types: an
   empty `AuthEnableRequest` and an empty `AuthDisableRequest` have equal fields, and `reqHolds c
   .authEnable ∧ reqHolds c .authDisable → .authEnable = .authDisable` would give `False` if `Content`
   forgot the type. "Up to `proto.Equal`" implies it (`Equal` compares descriptors first), but no law
   says so. *Fix*: one sentence in 2a's header (or a law `msgAt t p dq c ∗ msgAt t' p' dq' c ⊢ ⌜t =
   t'⌝`).

5. **`bootCC_lit` requires a non-empty context.** `RawNode.Bootstrap` passes `peer.Context`
   (`bootstrap.go:54`), which raft's API allows to be `nil` (raft's tests and examples do). R1's
   `bootEntryData_decode` is for non-empty `ctx` too, so this is consistent, but R1's `Bootstrap.spec`
   then needs `ctx ≠ []` for every peer. Either state the `nil` case (Context unset: another content,
   the same model) or confirm R1 carries the premise (etcd's member JSON is non-empty).

6. **`NewKVClient.spec` (and the other `New*Client`) are client-facing statements whose proof rests
   on 1c's realization of `connOk`**, an opaque slot with no `Invoke` elimination law
   (`client/v3/Api.lean:453`), and on realizing W0's opaque `remoteKVAt`. The sketch is plausible,
   but it can't be checked against stated laws. *Fix*: ask 1c for the law that turns `connOk` into
   grpc's `Invoke`/`NewStream` contract at etcd's methods, and cite it.

7. **Message sizes for rafthttp.** `msgEncodes` needs `Marshal`, which needs `encSize c < 2^48`;
   `msgIs` bounds it by `m.wireBound`, but nobody carries `m.wireBound < 2^48` for the messages raft
   sends (2f's request asked "below `2^63`"). Same shape as open question 3 (`MarshalConfChange`).
   Decide once for both: a workload premise like grpc's `msgsFit`, or a model fact that no Go slice
   reaches `2^48`, which would discharge both premises. 2f also asked that `proto.Size(m)` be the
   encoding's length: `Marshal.spec` does not relate `bs.length` to `encSize c` (2a's).

8. **A homogeneous cluster is assumed silently.** `msgWf` requires a set snapshot to be full. The Go
   doc says "peer nodes running older binary versions may send a non-nil, empty value for the
   snapshot field" (`raftpb/raft.pb.go`, `Message.Snapshot`'s comment), and raft handles it
   (`handleSnapshot` calls `EnsureSnapshot`). Such a decoded message has no `msgPts`, so 2f can't
   deliver it. Fine as a restriction, but state it in `msgPts`'s docstring and in the margin of 2f's
   decoder.

9. **R3's capacity request** (open question 2) is answered correctly: no capacity. It is worth
   pointing R3 at the concrete aliasing. `unstable.truncateAndAppend`'s `u.entries = ents`
   (`log_unstable.go:210`) adopts a `MsgApp`'s slice, and a later `append(u.entries, ...)`
   (`log_unstable.go:205`) writes into its capacity. For a `MsgApp` from `limitSize`
   (`ents[:limit]`, `util.go:294`) delivered in-process without a copy, that capacity is the
   leader's unstable log. I have not checked whether a supported user delivers raft's messages
   in-process uncopied (etcd decodes them through rafthttp; the examples clone). If one does, it is
   a raft bug for `issues/`. *Uncertain*.

## Third tier

- Header and report drift: `raftpb/Api.lean`'s header names laws `msgEncodes_fun`/`entryEncodes_fun`
  (the law is `wire_fun`); `Model.lean`'s `bootCC` docstring cites `bootCC_fun` (it is part of
  `bootCC_facts`); `etcdserverpb/Api.lean`'s header lists a `merge.go` snippet (it is in `stubs.go`);
  the mapping table says 2d's provisional is `entryRO` (2d's is `entryAt`, `ApiApply.lean:330`; the
  law 2d asked, `entriesRO_elem`, follows from `entriesRO` being a definition, so say so).
- `raftpb_persist` has no conjunct for `snapshotRaw`, `singlePts`; `pbRest`'s persistence is stated
  but not its intro at `□`. Harmless now.
- `version.LessThan.spec` quantifies over any `a b : val`; its doc ("major and minor") is wrong: the
  code is `ver1.LessThan(&ver2)` (`api/version/version.go:84`), a full semver comparison. The post
  is any boolean, so only the comment is wrong. `version.Cluster`'s doc omits the
  `semver.NewVersion` branch (`version.go:70`).
- Snippet `Assumes:` lines omit the read-only ownership of byte-slice parameters (`ctx`, `key`)
  that the literals need (`ctx ↦*□ bs`).
- Uncovered patterns (one snippet each would do): reading a handed-out `entriesRO` slice's elements
  (etcd's apply, `raft.go` `CommittedEntries`; 2d's `entryAt`); replacing a message's snapshot with
  a fresh one (`etcdserver/snapshot_merge.go:51`, `m.Snapshot = snapshot`: persist, then fold);
  building a message's `Entries` element by element before folding (rafthttp
  `msgappv2_codec.go:206-226`).

## Provability: what I checked and holds

- **Functionality of the relations.** `entryIs`, `hardStateIs`, `confStateIs`, `snapshotIs`, `msgIs`,
  `confChange*Is`, `singleIs` each fix the model as a reader of the content, so the relations are
  functional. `wire_fun` follows from `encodes_fun` and that. `confState_ext` is true: proto2
  `ConfState` has four repeated fields (no presence; `proto.Equal` compares them elementwise) and one
  optional `AutoLeave` that `full` fixes as set; `plain` excludes unknown fields. W0's request
  predicates carry the `Int` range premises that keep `reqHolds` functional (`Wire.lean:271-291`);
  without them, `rangeReqOwn p dq r ⊣⊢ rangeReqOwn p dq r'` for `r.limit = r'.limit + 2^64` and
  `holds_fun` would give `False`.
- **`decodeConfChange` as a definition.** It agrees with protobuf: `Proto.encodes` is decoding, so
  `encodes_fun` holds whatever the encoder chose (field order, packed or unpacked repeated, repeated
  scalars, defaults). Requiring `confChange*Is` (plain, depth, size) makes the result `none` for
  bytes with unknown fields. That is weaker than Go, which would decode them, but every conf entry
  raft holds is one `MarshalConfChange` wrote. `decodeConfChange_empty` is provable once 2a has the
  zero-content law (requested, item 2).
- **`MarshalConfChange` (some c).** `AsV1` dispatch, `confChange*_msgAt`, `Marshal.spec` (`fits` from
  `encSize ≤ wireBound < 2^48`, depth ≤ 2; no error from `marshalOk`), `encodes_fun` to identify the
  chosen content: sound. The size bounds are true of the encoding: a tag of at most 2 bytes and a
  varint of at most 10 per scalar; entries ≤ 44 + `len(data)` of the 64 allowed; a V2 change ≤ 24 of
  32; conf ids ≤ 11 of 12.
- **The `Ensure*` specs** match the code (`raftpb/util.go:20-66`): the owned case writes only `nil`
  pointer fields with fresh cells. The full case reads only, which is what makes `handleSnapshot`
  (`raft.go:1859`) and `InitialState` (`storage.go:132`) safe on shared snapshots.
- **`ConfState.Equivalent`**: the sketch works (Clone, in-place `slices.Sort` of the clones' lists
  under `lenOk`, a fresh `AutoLeave` cell, `confStateFull_msgAt`, `Equal.spec`, `confState_ext`; sorted
  lists are equal iff the lists are permutations of each other).
- **`EnterJoint`**: `enterJoint = none` is exactly the panicking `default` branch
  (`confchange.go:96-108`). `LeaveJoint`, `AsV1`, `AsV2` match the code.
- **Sharing**: the unfold laws' choices match what the code writes in place. No write goes through
  an optional scalar's cell after the message is folded: raft writes fields with `new(...)`
  (`raft.go:516,543,1743`; `node.go:388`), and etcd's `*cc.NodeId = id` (`storage/util.go:80`) is
  before folding. `MemoryStorage.CreateSnapshot` writes metadata fields (`storage.go:256-259`), which
  `snapMetaGo` holds at `dq`; `Equivalent` sorts only clones.
- **Snippets that are provable** (sketched): `raftpb/getters-nil`, `reply-shares-cell` (fold `r` from
  `pbRest_zero` and the shared `□` cell), `field-write` (modulo `proto.Uint64`), `msgapp-indexes`
  (`msgEnts`, `W64` wrap on both sides), `clone-message`, `wire-roundtrip` (under its size
  assumption), `marshal-decode`, `asv2`, `enter-leave`, `equivalent`, `ensure` (through the fraction
  split of second-tier item 2), `clone-snapshot` (`c ≠ s` by exclusivity of the own-1 fields),
  `etcdserverpb/compare-key`, `request-range`, `merge-range` (modulo F1), `watch-stub` (assuming 2a's
  `Send` gives the request back; not checked).

## Completeness: the provisional names, checked

| provisional (who) | 3h's claim | check |
|---|---|---|
| `entriesRO`, `msgPts`, `hardStatePts`, `snapshotPts`, `confStatePts`, `confChangePts` (R1 `Api.lean:141-156`) | `RaftPb.*` | holds. R1's `confStatePts` maps to `RaftPb.confStatePts` (any presence); where R1 relied on "presence" (its round-1 request), e.g. `InitialState`'s result, it must use `confStateFull`, or weaken at `□` (derivable) |
| `entryRO` (R3 `ApiLog.lean:495`) | definition | holds; getters on any `dq` |
| `entryPtrs` (R2 `ApiCore.lean:252`) | `RaftPb.entryPtrs` | holds |
| `ccsPts` (R4 `confchange/Api.lean:82`, `List Single`) | `RaftPb.ccsPts` over `ConfChangeSingle` | holds (same fields); per-element split follows from the definition; `confChangeV2Pts_unfold` gives `ccsPts` of `Changes` |
| `decodeConfChange`, `bootEntryData` (R1 `Model.lean:235,473`) | definition / opaque + `bootCC_facts` | decode holds; **bootstrap determinism missing** (2a), so R1's `BootLog` agreement is unproved |
| R2's `applyChange (.v2 (asV2 c)) = applyChange c` | not addressed | it is R1/R4's opaque `applyChange`; say so in the table |
| `pbEncodes` (2f) | `msgEncodes` (+ `entryEncodes`) | holds; size and `Size = len` (second-tier item 7) open |
| `reqModels`, `replyModels`, `chunkModels` (2a `v3rpc/Api.lean:94-101`) | 3h's definitions | holds; signatures match |
| W0's 15 predicates (`Wire.lean:137-152`) | 15 `*_msgAt` laws | all 15 present; F1 for `rangeRespOwn` |
| 1b's `watchReqOwn`, `wireWatchRespOwn`, `eventOwn` | relation laws; 2b's unfold laws accepted | holds; `IsCreate`/`IsModify` untranslated |
| 1c's `reqOwn`, `replyOwn`, `userAddOptsAt`, `statusRespOwn`, lease fields | relation laws, `replyOwn_lease` | holds for translated types; member, status and alarm fields untranslated |
| 2c's `irrOwn`, `alarmReqOwn` | **missing** (open question 4) | F4 |
| 2e's `irrIsRevoke`; `v3electionpb`/`v3lockpb` messages | **missing**; the latter not mentioned | F4 |
| 2d's `entryAt` | listed as `entryRO` | follows from the definition; fix the table |

Users outside raft and etcd: Kubernetes does not use `raftpb`. Of `etcdserverpb` it reads only
through `clientv3` (fields `resp.Header.Revision`, `kv.Key`) and `mvccpb.Event.IsCreate` (untranslated).
The cache reads the same fields. The examples' raft KV stores clone messages (covered).

## Ranking by need of revision

1. `Spec/go_etcd_io/raft/v3/raftpb/Api.lean` with 2a's `proto/Merge.lean` (F1), then
   `MarshalConfChange.lean` (F2), then the `ConfState` getters (second-tier item 2).
2. `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/`: the `IrrBody` decision (F4), the four lease
   `GetHeader`s (second-tier item 1), the `RangeResponse` merge capacity (F1), the snippets (F3).
3. `examples/specreq/{raftpb,etcdserverpb}/`: F3.
4. `Spec/go_etcd_io/etcd/api/v3/version/`: doc fixes only.
