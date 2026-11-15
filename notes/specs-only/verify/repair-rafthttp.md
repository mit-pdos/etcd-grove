# Repair: group `rafthttp` (2026-11-09)

Owned: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/`, `examples/specreq/rafthttp/`.
Worked from the 2f parts of `A8-server-boot-transport-{provability,completeness}.md`, A5's F1/F4 as
far as rafthttp is a user, and brief item 3 (sentinel errors).

## Findings

**A8-provability F8 (codec has no laws; delivered message not identifiable with the sent one): fixed.**
`Api.lean`:
- The provisional `pbEncodes` is gone. Every spec now uses raftpb's `RaftPb.msgEncodes`, which is
  functional through `wire_fun`. The specs changed: `messageEncoder.encode`, `messageDecoder.decode`,
  `decodeLimit`, `pipeline.post`, and the sketch of `pipeline.handle`.
- `msgFrame` is now transparent: `beU64 (W64 e.length) ++ e`, where `beU64 x := (u64Le x).reverse`.
  That is Perennial's `bigEndian.PutUint64` output, so the frame is self-delimiting by definition.
- `v2Frame` is now transparent and models all three msgappv2 frames exactly as `msgappv2_codec.go`
  does:
  - the link heartbeat is tag `0`;
  - `AppEntries` is tag `1`, then the count, each entry length-prefixed and `entryEncodes` at
    `st.2+1+j`, then the commit. The new `v2Short` holds the fields the decoder rebuilds;
  - the full `MsgApp` frame is tag `2` followed by `msgFrame`.

  Each frame also gives the next codec state as the encoder and decoder compute it.
- `v2Compat` is now transparent: the bytes are a prefix of a `v2Chain`, a new inductive chain of
  frames.

I chose transparency over the "determinism law" option. The README makes pure models transparent,
and from these definitions together with `wire_fun` the decoders' proofs can derive what they need
(frame identity, and `m' = m` or both link heartbeats) without a new law. One knock-on fix: the
`AppEntries` arm needs `m.to ≠ 0` for `sendable` to say anything. So `msgAppV2Encoder.encode` now
takes `dst ≠ 0`, and `msgChanAt` records `pid ≠ 0`, which `peer.send` already takes.

**A5 F4 (msgRecv has no producer; rafthttp's decoders deliver `msgPts`): fixed on rafthttp's side; laws requested.**
- The decoders (`messageDecoder.decode`/`decodeLimit`, `msgAppV2Decoder.decode`) now deliver
  `msgRecv ml m`.
- `raftOk`'s `Process` contract now takes `msgRecv` (this is the server's obligation when it proves
  `raftOk`, so it gives the server strictly more).
- The `recvChanAt` docstring and the sketches of the handlers and of `decodeLoop` were updated.

How each decoder gets `msgRecv`:
- msgappv2's `AppEntries` message is a literal whose `Entries` comes from a fresh `make`. It gets
  `msgRecv` from `msgRecv_unfold`, so no new law is needed.
- The `Unmarshal` and `Clone` paths need a law from raftpb (request below).

**A5 F1 (`MessageType.String` lost its spec; rafthttp's code calls it): request.** The sketches of
`Transport.Send`, `peer.send`, `remote.send`, `streamReader.decodeLoop` and
`snapshotHandler.ServeHTTP` now cite raftpb's `MessageType.String` for their log lines, as
requested of raft-conf-pb.

**A8-provability F3's `ReqErrorC` claim: fixed (snippet).** `transport.go`'s `ReqErrorC` no longer
claims that the server's stop on `errorc` "is always safe". It claims only the non-blocking report
and a loggable error, and points to F3 and `issues/etcd-read-after-backend-close-panic.md` for the
stop. The stop protocol itself belongs to server-core and server-boot and to the recorded decision.

**Brief item 3 (sentinel errors): fixed.**
- `vars_init.spec` now covers all seven error variables (`errIncompatibleVersion`,
  `ErrClusterIDMismatch`, `ErrExceedSizeLimit`, `errStopped`, `errUnsupportedStreamType`,
  `errMemberRemoved`, `errMemberNotFound`) through a new `errVars` list. Before, it covered only
  `ErrClusterIDMismatch`. Each variable gets `∃ e, errIs g e ∗ Http.errOk e ∗ ⌜e ≠ nil⌝`, where
  `errIs` is raft's `globalAddr g ↦□ e`.
- New law `errVars_distinct.spec`: the values are pairwise distinct.
- rafthttp had no Lean error constants. The posts that name an error already read it through
  `errIs`, as `checkClusterCompatibilityFromHeader` does. The Changes lines of
  `checkPostResponse`, `checkClusterCompatibilityFromHeader`, `snapshotSender.post` and
  `streamReader.dial` were updated.

**A8-completeness S4 (`vars_init`'s docstring misdescribes etcdmain): fixed differently.**
- The docstring now says what actually happens: embed binds both timeouts to flags, and etcdmain
  raises them to `5s` when lower, both before any server starts. A program that writes them is
  therefore outside the law (open-questions 5.9).
- I did not take the reviewer's preferred shape (owned points-to, frozen at `≥ 5s` before
  `Start`). `isPkgInit` is persistent, and no package exports a resource for writable package
  variables after initialization, so that shape is a cross-package design and not a local fix.
  The docstring records it.

**A8-provability second tier, `imgBytes` (opaque pure predicate): fixed.** rafthttp's provisional
`imgBytes` is replaced by 4a's `Backend.imgBytes`, the trusted bbolt file format, in
`dbReader_readerAt.spec` and `readerAt_dbReader.spec`.

**A8-provability second tier, `ReqInstallReceived` (`dbIn` not persistent): fixed (snippet).** The
snippet's Assumes now says that `Process` keeps `ν.dbIn snapIndex` in `r.mu`'s lock invariant beside
`snapIndex`, and that the reader takes it from there under the lock.

**A8-completeness S1 (`rafthttp.streamType__String_ptr` has no successor): fixed.**
`streamType__String_ptr.lean` is restored. The translated stream code calls `(*streamType).String`
about ten times (`Code/.../rafthttp.lean:3112, 4644, ...`), and the old proof of `streamReader.run`
used it.

**A8-completeness F5 (`PauseSending`/`ResumeSending` have no spec): request.** These are
`EtcdServer` methods. `Transport.Pause`/`Resume` already have specs, and `transporterOk` lets the
server's `r.transport.(rafthttp.Pausable)` assertion and the calls go through.

## Requests to raft-conf-pb

1. `SpecPlan/Spec/go_etcd_io/raft/v3/raftpb/Api.lean`: add a law turning a decoded or cloned message into
   `msgRecv`. In shape: `msgPts p (own 1) m ∗ <2a's fresh-capacity fact for raftpb.Message at p> ⊢
   msgRecv p m`, or directly from `Proto.msgAt raftpb.Message.ty p (own 1) c ∗ ⌜msgIs c m⌝ ∗ <fact>`.
   - Who needs it: `messageDecoder.decodeLimit` (`proto.Unmarshal`), `msgAppV2Decoder.decode`
     (`MustUnmarshalMessage` of a full frame, and `proto.Clone(&linkHeartbeatMessage)`), and the
     pipeline handler.
   - This is A5 F4's step 2. The fact itself is grpc-v3rpc's: `Unmarshal`/`Clone` posts with the
     repeated fields' capacity owned, A5 F4 step 1. The coordinator should route that to
     grpc-v3rpc if raft-conf-pb does not.
2. `SpecPlan/Spec/go_etcd_io/raft/v3/raftpb/MessageType__String.lean`: restore `MessageType.String.spec` as
   a trust-boundary spec ("returns some string"), per A5 F1. rafthttp's sketches cite it.
3. Optional, for convenience: a law `msgRecv p m ⊢ msgPts p (own 1) m ∗ (msgPts p (own 1) m -∗
   msgRecv p m)`. rafthttp's `isLinkHeartbeatMessage`/`isMsgApp`/getters take `msgPts`. It can be
   derived from the two unfold laws, so this is not blocking.

## Requests to server-core

1. `EtcdServer__Process.lean` and `raftNode__Step.lean` should take `msgRecv ml m` in place of
   `msgPts ml (DFrac.own 1) m`. `raftOk`'s `Process` now hands the message over as `msgRecv`, and
   raft's `node.Step` requires it (A5 F4 step 3). `srvNode_raftOk` (`ApiApply.lean`) then closes
   without change.
2. Add `EtcdServer.PauseSending.spec` and `ResumeSending.spec` (A8-completeness F5), together with
   `raftNode.pauseSending`/`resumeSending`.
   - Pre: the server's `srvMember`, giving the transport's `transporterOk`, plus a `threadTok`.
   - Post: the token back.
   - Proof: the type assertion to `rafthttp.Pausable` succeeds on the `*Transport`, then
     `Rafthttp.Transport.Pause.spec`/`Resume.spec`.
3. `vars_init.spec` now gives every rafthttp error variable, not only `ErrClusterIDMismatch`.
   `corrupt.go`'s uses (`ErrClusterIDMismatch.Error()`) keep working: the conjunct is now inside
   `[∗list] g ∈ errVars, …`. A spec that cited the old third conjunct positionally should take it
   from the list.

## Requests to server-boot

1. `examples/specreq/etcdserverboot/boot.go`, `ReqPartition`: add the pause pattern of the
   integration framework's `Member.Pause/Resume` (`s.PauseSending(); s.ResumeSending()`) once
   server-core's specs exist (A8-completeness F5).

## New decisions

- **The msgappv2 and message codecs are transparent definitions, not a determinism law.**
  `v2Frame`/`v2Chain`/`v2Compat`/`msgFrame` spell out the wire format of
  `msg_codec.go`/`msgappv2_codec.go`. The decoders' proofs derive self-delimitation and
  `m' = m` from them and raftpb's `wire_fun`. The alternative was an opaque `v2Frame` with an
  exported determinism law. That would be smaller, but it is a law about a pure model that README
  says should be spelled out, and its exact statement (link heartbeats decode to the canonical
  heartbeat, not to the sent one) is easy to get wrong.
- **`raftOk`'s `Process` takes `msgRecv`.** This makes A12's choice of `msgRecv` concrete at the
  transport boundary. The server proving `raftOk` receives strictly more than before.

## Build

`etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp`: **OK (105
modules)**. The only warning is the old unused-`id` warning in `raftOk`. `go vet
./specreq/rafthttp/...`: clean. No other directory references the removed names (`pbEncodes`,
rafthttp's `imgBytes`).

No Go bug found.

## Second pass (coordinator, `second-pass.md`)

- **The decoders deliver `msgRecv` through `RaftPb.msgRecv_intro.spec`.** Done in the sketches of
  `messageDecoder.decodeLimit`, `msgAppV2Decoder.decode` and `pipelineHandler.ServeHTTP`.
  - **`Unmarshal` paths close.** `Unmarshal` gives `Proto.mergeDst t p c` with `norm c = c`, and
    `msgIs c m` comes from `msgEncodes`. So `decodeLimit` and the pipeline and snapshot handlers
    close.
  - **AppEntries frame closes.** Its message is built by hand, so `msgRecv_unfold` folds it.
  - **Two msgappv2 paths still need laws** (requests below):
    - the full frame goes through `pbutil.MustUnmarshalMessage`, whose post is still
      `msgAt (own 1)`, not `mergeDst`;
    - the heartbeat goes through `proto.Clone`, which gives `mergeDst t p' (norm c)`, so
      `msgRecv_intro` needs `msgIs (norm c) m`.
- **`vars_init` docstring (server-boot's S4).** Done in the first pass: it names embed's flag
  binding and etcdmain's clamp as outside the law. Taking the timeouts' points-to as a premise of
  `Transport.Start` is not done, for the reason given above: no package exports an owned resource
  for package variables after initialization.
- **The snapshot handler supplies `SaveDBFrom`'s two updates.** `saveOk ν sd` (`Api.lean`) is now
  the nested pair `SaveDBFrom` takes, with `Q := ν.dbIn i`:
  - the first update moves `snapDbs sd F` to `snapSaving sd F i img`;
  - its commit is the second update, which moves that to `snapDbs sd (saveAt F i img)` and commits
    `ν.dbIn i`.

  `snapshotHandler.ServeHTTP`'s sketch and `snapshot.go`'s `ReqInstallReceived` Specs line are
  updated to match.
- **`ID.String_ptr` and the `URLs` pointer specs.** I searched the translation for pointer-receiver
  calls:
  - `(*types.ID).String` is called in 25 rafthttp functions. Their Proof sketches now cite
    `Types.ID.String_ptr.spec`, with a Changes line on each: `Transport.{AddPeer, AddRemote, Send,
    UpdatePeer, removePeer}`, `checkClusterCompatibilityFromHeader`, `checkPostResponse`,
    `createPostRequest`, `peer.{send, stop}`, `peerStatus.{activate, deactivate}`,
    `pipeline.{start, stop}`, the three handlers' `ServeHTTP`, `startPeer`,
    `streamReader.{close, decodeLoop, dial, run}`, `streamWriter.{closeUnlocked, run}`.
  - `(*types.URLs).Len` is called in `setPeerURLsHeader`, which now cites `Types.URLs.Len_ptr.spec`.
  - rafthttp never calls `StringSlice` through a pointer.
- **Message relations surviving `Proto.norm`.** rafthttp defines none of its own: its relations go
  through raftpb's `msgEncodes`/`entryEncodes`, and `v2Frame`/`msgFrame` are byte-level. raftpb has
  no `norm` law, though. Since 2a's `encodes_fun` now holds only up to `norm`, raftpb's own
  `wire_fun` also needs `msgIs`/`entryIs` to be invariant under `norm` (request below).

### Requests to raft-conf-pb (second pass)

- Add `msgIs_norm.spec : msgIs c m ↔ msgIs (Proto.norm c) m`, and the same for `entryIs`.
  - Who needs it:
    - `msgRecv_intro` on a `proto.Clone`'s `mergeDst t p' (norm c)`: the msgappv2 link heartbeat;
    - raftpb's own `wire_fun` under 2a's new `encodes_fun` (`norm c = norm c'`). That one is
      raftpb's proof obligation, flagged here.

### Requests to backend-schema (pbutil)

- `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustUnmarshalMessage.lean`: give `Proto.mergeDst t p c`
  (with `norm c = c`), as 2a's `Unmarshal.spec` now does, in place of `msgAt t p (own 1) c`.
  - Its body is `proto.Unmarshal`, so this follows directly.
  - Who needs it: rafthttp's `msgAppV2Decoder.decode`, whose full frame is
    `pbutil.MustUnmarshalMessage(&m, buf)` and must reach `msgRecv`.

### Build (second pass)

`etc/specs-build.sh --dir …/rafthttp`: **OK (105 modules)**. The first run said FAILED: Lake
reported success, but the up-to-date check failed afterwards, most likely because another group
edited an import in between. A rerun was clean. `go vet ./specreq/rafthttp/...` and `gofmt -l` are
clean.

## Final relay round

- **`SaveDBFrom` now takes the revert state `Backend.beRev p rv`** (server-boot's "Last pass").
  - `saveOk ν sd` (`Api.lean`) now also lends it for each call:
    `|={⊤}=> ∃ p rv, ⌜Snap.inDir sd p⌝ ∗ Backend.beRev p rv ∗ (∀ rv', Backend.beRev p rv' ={⊤}=∗ True)`.
  - The snapshot handler passes the loaned state to `SaveDBFrom`. It then returns whatever the call
    leaves through the wand: `beNoRevert p` on success, `beRev p rv` back on an error.
  - `snapshotHandler.ServeHTTP`'s sketch and Changes are updated. Its statement is unchanged,
    since it already took `saveOk`.
  - The docstring says how etcd's server meets the loan:
    - the backend file `<snap dir>/db`, which has a pending `beRevert` after `OpenSnapshotBackend`,
      when it is not already lent;
    - otherwise an unused entry of its own (`beFile_none`), because the transport needs nothing
      of `p`.
- **msgappv2 full frame:** closes. `pbutil.MustUnmarshalMessage` now gives a canonical `mergeDst`,
  so `RaftPb.msgRecv_intro` applies.
- **msgappv2 link heartbeat:** closes. raftpb's `raftpb_norm` carries `msgIs` over `Clone`'s
  `norm c`. That withdraws my second-pass request for `msgIs_norm`.
- **Build:** `etc/specs-build.sh --dir …/rafthttp`: **OK (105 modules)**. `go vet` is clean;
  the snippets did not change in this round.

### New decision (final relay round)

**The revert state is lent outside the atomic updates.** `SaveDBFrom` takes `beRev p rv` in its
precondition and holds it for the whole call. etcd's snapshot handlers can run concurrently: two
leaders' streams can overlap across a term change. So the client must be able to lend one state per
concurrent call. Lending the backend file's state alone cannot serve two calls at once, which is why
the client may name any entry, and an unused name needs the server to own names in the snapshot
directory.

The stronger alternative is server-boot's: move `beRev p rv` into `SaveDBFrom`'s second atomic
update, with pre `snapSaving ∗ beRev p rv` and post `snapDbs … ∗ beNoRevert p`. The directory fsync
is the atomic point, so this is true of the code. The server's invariant could then keep the backend
file's state and give it up only at that point, and `saveOk` would go back to two atomic updates.

### Request to server-boot (final relay round)

- Consider moving `Backend.beRev p rv` from `Snapshotter.SaveDBFrom.spec`'s precondition into its
  second atomic update: `beRev p rv` in the atomic pre, `beNoRevert p` in the atomic post. On an
  error, the first update comes back as now. Why: concurrent snapshot handlers each hold the lent
  state across a blocking call (above). If you take this, rafthttp drops the loan from `saveOk` and
  adds `beRev`/`beNoRevert` to its second update.

## Final relay round, revised (server-boot moved `beRev` into `SaveDBFrom`'s second update)

- **`saveOk` is back to two atomic updates, with no loan.** This supersedes the loan and the
  "New decision" of the round above, and the request to server-boot there is now satisfied.
  - The form is `saveOk ν sd := ∃ p, ⌜Snap.inDir sd p⌝ ∗ □ ∀ i img, □ ν.img i img -∗ AU<…>`.
  - The client picks the entry `p` once. For etcd's server it is the backend file.
  - The second update's atomic pre is `∃∃ rv, snapSaving sd F i img ∗ Backend.beRev p rv`. Its
    post is `snapDbs sd (saveAt F i img) ∗ Backend.beNoRevert p`, committing `ν.dbIn i`.
  - The client supplies `beRev` from its invariant at the directory fsync. Concurrent handlers
    therefore need nothing exclusive across the call, and the "the server owns names in the
    directory" assumption is dropped.
- **Handler sketch:** `snapshotHandler.ServeHTTP`'s sketch and Changes are updated. Its statement is
  unchanged.
- **Build:** `etc/specs-build.sh --dir …/rafthttp`: **OK (105 modules)**.
