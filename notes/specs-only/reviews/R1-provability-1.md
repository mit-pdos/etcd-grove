# R1 (raft's node API): provability review, round 1

Reviewer: provability agent, 2026-11-09. Read: `SpecPlan/Spec/go_etcd_io/raft/v3/{Model,Api}.lean` and
every function spec, `examples/specreq/raftnode/*.go`, `notes/specs-only/req/go_etcd_io_raft_v3*.md`,
the pinned Go (`.lake/src/raft`, `.lake/src/server/etcdserver`), Perennial's select/channel specs
and `SpecPlan/Spec/context/Api.lean`. I read the author's report (`notes/specs-only/batch-R1.md`) only after
I had my findings; its claims are checked at the end. I built nothing. "Uncertain" marks what I
could not settle by reading.

## First tier (hard rules)

### F1. `msgSent_replaceSnap` is unsound: a stale leader can count a follower that does not hold its entry (Api.lean:719-724)

The law lets anyone holding `msgSent γ m` (a `MsgSnap` of term `t` from `L`) and *any* valid `s'`
with `s.index ≤ s'.index` replace the snapshot. A valid `s'` may come from a commit at a later term
`t' > t` that `L` does not know about. Trace (5 voters, `L` a stale leader at `t`, partitioned with
`f` and `a`):

1. `a` acks `(j, t)` to `L`; later `b, c, a` elect a leader at some `t' > t` that never had `(j, t)`
   (its last term is above `t`), and it commits `(j, t'')` at index `j`.
2. A snapshot `s'` of that committed prefix (index `≥ j`) is placed into `L`'s `MsgSnap` to `f`
   (the law allows it). `f` is still at term `≤ t`, so it takes the message:
   `stepFollower` → `handleSnapshot` → `restore`. It replies
   `MsgAppResp{Index: lastIndex = s'.index}` at term `t` (raft.go:1855-1869).
3. `L` is still leader at `t`. `pr.MaybeUpdate(m.Index)` (raft.go:1542) sets `Match[f] ≥ j`, and
   `maybeCommit` (raft.go:793, log.go:455) commits `(j, t)` from `{L, a, f}`. But `f` never held
   `(j, t)`.

Result: two different entries committed at index `j`. The law's own comment claims "the follower's
restore of any committed snapshot is safe". The restore is safe; the flaw is the sender's commit
that counts the acknowledgement. The old law required `s'` to be known committed at the message's
term, and that premise is what excluded this case. The author's open question 4 asks exactly this,
and the answer is no.

- **What etcd needs.** etcd (`createMergedSnapshotMessage`) puts in the sender's *own* applied index.
  That index is a prefix of `L`'s delivered log. While `L` is still leader at `t`, this prefix is in
  `L`'s own log. If `L` has moved past `t`, it ignores the term-`t` acknowledgement.
- **Fix.** Tie `s'` to the sender's log. Take
  `isNode n γ m.src ∗ deliveredLb n γ l ∗ ⌜uint.nat s'.index ≤ l.length⌝` (with `snapValid γ s'`).
  Use `deliveredLb`, not `appliedLb`: etcd's applied index can run ahead of raft's `Advance`.
- **Who it affects.** rafthttp/2d's merged snapshot, and `transport.go`'s `ReqSendSnapshot`, whose
  `Assumes` already says "the leader's applied index", so the fix serves it.
- **Status.** By code reading, not reproduced in Go. This is a spec bug, not a Go bug: etcd only
  uses its own snapshot.

### F2. The storage laws' atomic updates are at mask `⊤ ∖ ↑γ.ns`, but `S σ` lives in raft's invariant at `γ.ns` (Api.lean:759-794, header :70-78)

These laws hand the client an atomic update built by raft: `readyStor_install`, `readyStor_append`,
`stor_compact`, `stor_createSnapshot` and `stor_setHardState`, each
`AU <{ ∃∃ σ, S σ ∗ … }> @ ⊤ \ ↑γ.ns, ∅`.

- **Why it fails.** Raft is the producer of these updates, so it must provide
  `|={⊤∖γ.ns, ∅}=> S σ`. The header puts `S σ` "in the node's invariant", and that invariant is
  allocated at `γ.ns` (`StartNode.lean`'s sketch). Opening it needs `γ.ns` in the mask, so none of
  the five laws can be proved.
- **Where the convention comes from.** `⊤∖γ.ns` is right for updates the *client* hands to raft:
  `Propose`, `readCtx_register`, `RestartNode`'s check. It does not fit updates raft hands to the
  client.
- **Fix.** Use the outer mask `⊤`. The consumers, `MemoryStorage.*.spec`, already open their
  updates at `⊤`. The alternative is a separate storage namespace, but it cannot be kept disjoint
  from the client's own namespaces.
- **Who it affects.** Every write to an attached storage: `readyloop.go` and `storage.go`'s
  `ReqSnapshotCompact`.

### F3. `RestartNode` / `NewRawNode` do not require the stored snapshot to be valid (RestartNode.lean:57-84, NewRawNode.lean)

Raft sends its storage's snapshot in `MsgSnap`s (`maybeSendSnapshot`, raft.go:~670-690), and
`msgSent_snap` promises every sent `MsgSnap` carries a `snapValid` snapshot.

- **What the premises do not give.** `StorageHolds` bounds only the stored snapshot's index. The
  configuration premise is `(cf σ).Is m ∧ confAt γ a m` at a point `a` that need not be
  `σ.snap.index`.
- **Two problems.** Nothing makes `σ.snap` a member of `snapsMade` with the configuration *at its
  index*. And with `a ≠ σ.snap.index`, the stored `ConfState` is the configuration at `a`, so the
  stored snapshot is not valid at all. etcd's restart builds exactly that snapshot:
  `bootstrap.go:107-115` puts the backend's configuration, at the consistent index, into the WAL
  snapshot at `si`.
- **Consequence.** Raft cannot establish its invariant "the stored snapshot is valid", and
  `msgSent_snap` fails for a restarted node.
- **Fix.** Add `σ.snap.isEmpty ∨ snapValid γ σ.snap` to both specs. For etcd, also check whether
  the snapshot raft sends from storage needs its configuration to match its index. It does: the
  receiver restores the configuration with the snapshot. That makes etcd's "snapshot at `si` with
  the configuration at `ci`" a real question for 2d/2e, possibly an etcd bug when a configuration
  change lies in `(si, ci]` (uncertain, not traced further).

### F4. The bootstrap log fixes only what its bytes decode to, not the bytes (Model.lean:470-476; StartNode, setupNode, RawNode.Bootstrap)

- **The gap.** `BootLog ps boot` says only `decodeConfChange EntryConfChange e.data = some …`.
  `RawNode.Bootstrap` appends entries whose `Data` is `proto.Marshal(cc)` (bootstrap.go:55-61). The
  3h request asks only that marshalled bytes decode back
  (`req/go_etcd_io_raft_v3_raftpb.md`).
- **Why it matters.** Raft's proof must show the node's committed log equals `boot`, and
  `committedLb γ boot` comes from `cluster_alloc`. That needs `e.data` to equal the bytes Go
  produces, and nothing gives it. Two nodes of one cluster could then hold different bytes at index
  1..n under one committed prefix, so `StartNode.spec` is unprovable for an arbitrary
  `boot ∈ BootLog ps`.
- **Presence also changes the bytes.** A `nil` and an empty `Peer.Context` encode differently, as
  does the absent `Id` field.
- **Fix.**
  - Add an opaque, 3h-owned function `bootEntryData : w64 → List w8 → List w8`: the bytes Go's
    marshal gives the message `Bootstrap` builds.
  - Define `BootLog` by `e.data = bootEntryData p.1 p.2`.
  - Add the decode law. Request it from 3h: `proto.Marshal` is a function of the Go message,
    presence included.
  - Have `peersPts` record whether each context is `nil`, or require non-empty contexts (etcd's are
    JSON).

### F5. A context error is not tied to the context, and the specs take Perennial's `isContext` (Api.lean:407-409; every `node.*` spec with a `ctx`)

**(a) The context error.** `nodeErr`'s context arm is `context.isCtxErr err`: *some* context's
error, with nothing saying `ctx` is done. Go returns `ctx.Err()` right after `<-ctx.Done()`
(node.go:519-520, 535-536, 545-546), so the context is done.

- These snippets panic on `err != nil && err != ErrStopped && ctx.Err() == nil`:
  `confchange.go:ReqProposeV1`, `readyloop.go:ReqDisrupt` (`Campaign`, `ForgetLeader`) and
  `transport.go:ReqDeliver`. None of them is provable.
- **Fix.** Make the arm `ctxDone ctx ∗ isCtxErr err`.

**(b) The context's type.** The specs require `context.isContext ctx cd`, which covers only a
`*cancelCtx` or a `*timerCtx`. etcd's `Process` is called with `context.TODO()` from rafthttp
(`http.go:148`, `:307`), so `node.Step.spec` cannot serve it. The snippets take an arbitrary
`context.Context`.

- **Fix.** State the node specs over W0's `Context.ctxOk ctx` (SpecPlan/Spec/context/Api.lean). That is
  what the ambient-context design is for.
- This is first tier on completeness grounds (a user not served).

### F6. `node.Stop` cannot be called twice, but `ReqStopRestart` requires it (node__Stop.lean:43-53; restart.go)

- **The spec.** `node.Stop.spec` takes `nodeRunning n 1`, which the first call consumes. Its Margin
  says a second `Stop` "returns at once", but no spec says so.
- **The snippet.** `ReqStopRestart` calls `n.Stop(); n.Stop()` and states "Stop twice does not
  block". It is unprovable.
- **Fix.** Use one spec with pre `isNode n γ id ∗ (nodeRunning n 1 ∨ nodeStopped n)` and post
  `nodeStopped n ∗ (vacancy if it was running)`. Go: node.go:331-341 selects on `done`.

### F7. `isStorage`'s contract lets a storage return what makes raft panic (Api.lean:366-384)

**`Entries`.** The contract allows `ErrUnavailable` whenever `σ.ents = []`, including when
`lo ≤ σ.off` (the storage was compacted to its last index between raft's `FirstIndex` read and its
`Entries` call: the client's `stor_compact` runs concurrently). `raftLog.slice` panics on
`ErrUnavailable` (log.go:514-518). A storage that meets the contract can therefore make raft panic,
so `StartNode`/`RestartNode`/`NewRawNode` over a general `S` are false.

- **Fix.** Drop the arm. It is unreachable for `MemoryStorage` under the pre: `lo > off` and
  `lo < hi ≤ last+1` imply `ents ≠ []`. Drop it from `MemoryStorage.Entries.spec` too, which is the
  compaction-in-place principle: no arm the precondition excludes.

**`Term` (and `MemoryStorage.Term.spec`).** Neither has a premise on `j`, yet the post claims
`ErrUnavailable` past the last index.

- **Go.** `if int(i-offset) >= len(ms.ents)` (storage.go:177) converts to a signed `int`. For
  `i ≥ offset + 2^63` the comparison is false and `ms.ents[i-offset]` panics. Storage's
  documentation restricts `i` to `[FirstIndex()-1, LastIndex()]`.
- **Consequence.** `memStor_isStorage.spec` and `MemoryStorage.Term.spec` are false at those
  inputs. The old spec had the range premise.
- **Fix.** Add `uint.nat j ≤ σ.last` to the update's provided pre in the contract (raft guarantees
  it: log.go:398-405), and the same, or `uint.nat i < σ.off + 2^63`, to `MemoryStorage.Term.spec`.

**Index wrap-around (same family, lower stakes).**

- **Go.** `MemoryStorage.Append` computes `last := entries[0].GetIndex() + len - 1` in `uint64`
  (storage.go:302); `lastIndex()` does the same.
- **The model.** `StorState.append` uses `Nat`. At `k + |es| > 2^64` (an `entriesRO` whose indices
  wrap) Go takes the `last < first` shortcut, while the model appends, so `Append.spec` is false.
- **Fix.** Add a bound (`σ.last + |es| < 2^64`, or an invariant `last < 2^63` in `memStor`), as the
  old specs had (`< 2^61`).

## Second tier

- **S1. `memStor`'s stated realization cannot prove `InitialState.spec`** (Api.lean:79-80;
  MemoryStorage__InitialState.lean).
  - **The conflict.** The header says `memStor ms σ` is "a ghost var of `σ` whose authority is in
    `MemoryStorage`'s lock invariant with the physical fields". `InitialState` reads
    `ms.snapshot`, `Metadata.ConfState` and `ms.hardState` *without* the lock, and
    `EnsureConfState` may write `cs.AutoLeave` (raftpb/util.go:24-26). With the fields only in the
    lock invariant, a thread holding the exclusive fragment cannot read them.
  - **A realization that works.** `memStor` carries a fractional share of the unlocked-read
    footprint: the `snapshot` and `hardState` fields, the snapshot's `Metadata.ConfState` field and
    the `ConfState` object. The lock invariant holds the other share plus the relation to `σ`.
  - **How the writers fit it.** Each writer does its stores to that footprint by opening its update
    once per store: abort where the abstract state is unchanged, commit at the store that changes
    it. For `CreateSnapshot` that is the `ConfState` pointer store; for `ApplySnapshot`, the
    `ms.snapshot` store, while the `ms.ents` store needs only the lock. The stored `ConfState`
    must be ensured (`AutoLeave` non-nil), since `InitialState` has no full ownership to write it.
  - **What that requires.** `CreateSnapshot.spec`'s `confStatePts` and `ApplySnapshot.spec`'s
    `snapshotPts` (at `dq = discard`) must imply ensured fields. `EnsureSnapshot` writes into the
    argument otherwise (raftpb/util.go:56-66). This is a missing request to 3h: the ownership
    predicates imply every optional field is present.
  - **Fix.** Restate the realization, and add the presence request.
- **S2. No law grants a read of an attached storage.**
  - **The users.** etcd's `EtcdServer.run` calls `s.r.raftStorage.Snapshot()` while the node runs
    (server.go:755), and uses the result's index and `ConfState` as its starting progress. The
    `FirstIndex` spec cites `kvdurable/kv.go:607` as a user.
  - **The gap.** The client cannot open `S σ` (it is in raft's invariant), and the only laws are
    writes.
  - **Fix.** Add a read law, `nodeStorage n γ S ⊢ AU <{ ∃∃ σ, S σ ∗ ⌜facts⌝ }> @ ⊤, ∅ <{ S σ,
    COMM … }>`. Its facts: `off ≤ snap.index`, `snap.isEmpty ∨ snapValid γ σ.snap`, and the stored
    entries committed up to the applied index. This is a completeness item; first tier for 2d if
    no other path exists.
- **S3. `a ≤ σ.hs.commit` excludes etcd's crash restarts** (RestartNode.lean:66).
  - **Why.** etcd sets the restored snapshot's configuration to the backend's, at its consistent
    index `ci` (bootstrap.go:107-115), so `a = ci`. A commit-only `HardState` is written but not
    fsynced, which bootstrap.go:633-637 acknowledges. After a crash `ci > σ.hs.commit` is
    possible, and the premise fails.
  - **Go does not need it.** Raft restores the tracker to `cf σ` whatever `a` is. The entries in
    `(σ.off, a]` are handed out again, and etcd skips `ApplyConfChange` for them. That is
    `ApplyConfChange.spec`'s second case, and `Advance`'s `confSkipped` range is empty below `a`.
  - **Suggestion.** Relax to `max σ.off Applied ≤ a` with `confAt γ a m` (which already implies the
    committed log reaches `a`). Check what raft's invariant uses `a ≤ commit` for (uncertain).
- **S4. Missing law: `confAt γ k m ⊢ ⌜m.Valid⌝`.**
  - **Who needs it.** `Membership.applyChange_v1.spec` needs `m.Valid`. A client refusing with
    `NodeID = 0` (etcd, `ReqApplyOrRefuse`) or deciding a change has to show validity of the
    configuration before the entry.
  - **Why it cannot derive it.** After a restart, `confAt` comes from `snapValid_committed` with no
    validity attached.
  - **Fix.** Add the law. It is true: `cluster_alloc`'s configurations are valid, `Membership.empty`
    is valid under the stated `checkInvariants`, and `applyChange_valid` covers the rest.
- **S5. `cluster_alloc` does not exclude local-target ids**, yet `ConfigOk` (and `freshIds_take`)
  require `isLocalTarget id = false`. A founding voter with a local-target id gets `nodeVacant`,
  but no start spec can use it. Add `∀ id ∈ vs, isLocalTarget id = false` (Api.lean:544).
- **S6. A snippet whose `Assumes` points the wrong way: `readyloop.go:ReqReadyLoop`.**
  - **Stop.** It assumes "stop is closed only after `n.Stop`", but panics when
    `ApplyConfChange == nil` and `stop` is open. The spec's `nil` gives `nodeStopped n`, which
    holds from `close(done)` inside `Stop`, before the stopper closes `stop`. Under the stated
    assumption the snippet can panic in Go.
  - **The correct assumption.** "`n.Stop` is called only after `stop` is closed". With it the loop
    holds a `nodeRunning` share while running (it needs one for the enter update anyway), so the
    `nil` branch is contradictory.
  - **The view.** The loop calls `ApplyConfChange` on every decided entry. After a `RestartNode`
    with `a > applied`, a re-delivered entry below the view whose change is not a no-op (add 4,
    then remove 4) violates the second case's `m' = v.membership`. Add to `Assumes`: the node
    started with its view at the delivered log, or skip entries below the view (etcd does, through
    its consistent index).
- **S7. Smaller snippet fixes.**
  - **`ReqApplyOrRefuse`.**
    - The `nil` check needs the caller to hold a `nodeRunning` share; say so.
    - `refuseByZero` needs the configuration not joint (`applyChange_v1`'s `¬ m.isJoint`): etcd
      uses v1 only.
  - **`ReqDeliver`.** It steps the `Ready`'s message pointer itself. For responses (`readyDq`)
    the pointer is read-only, and `Step` needs `msgPts … (DFrac.own 1)` (it writes the message).
    Copy it first, as `kvdurable/cluster.go:331` (`copyMsg`) does.
  - **`ReqStartFresh`.** It needs `id` not a local target (S5).
  - **`ReqSnapshotCompact`.** It needs `applied > 0` (`snap_make`'s `0 < l.length`).
  - **`ReqRestartDurable`.** It needs, after F3, the stored snapshot valid.
  - **`ReqBootstrapFromWAL`.** Its `snap` must be owned or ensured (S1).

## Third tier

- `MemoryStorage.Entries.spec`'s `ErrUnavailable` arm is unreachable under its pre (see F7).
- `msgPts` should imply a non-nil pointer. `node.Step` returns a non-`nodeErr` error for `nil`
  (node.go:477-479). Say so in the 3h request.
- `node.Advance.spec`'s `k` appears only in the precondition (harmless: it is whatever the `Ready`
  had).
- The `ConfigOk` scope restrictions (`ReadOnlySafe`, sync writes, validation on) are marked as
  such. Fine.

## What is good

- **The `Ready` contract.** `BatchOk` matches `readyWithoutAccept`/`acceptReady` (rawnode.go:139-184,
  400-430) clause by clause: hard state only on change, `MustSync` against `prevHardSt`, no
  committed entries with a snapshot, entries after the old commit.
- **`readyDq`.** Correctly makes responses read-only (acceptReady reads `msgsAfterAppend` after the
  hand-off).
- **The send-before-write check (`readyCheck`).** I checked it against the single-voter case,
  where a candidate might seem to win within one step. In v3.7 the self-vote travels through
  `msgsAfterAppend`, which is stepped only at `Advance` (raft.go:1070-1077). The term is therefore
  durable before the node can lead, and the check is sound there.
- **`ConfigOk` against `validate` and `newRaft`** (raft.go:293-341, 439-498). Every `validate`
  error is excluded, and the both-zero size panic is covered.
- **No panic in `newRaft`.** The panics are excluded:
  - `InitialState` errors: the contract returns `nil`.
  - `loadState`'s commit range: `σ.off ≤ σ.hs.commit` from `StorageHolds`; `σ.hs.commit ≤ D.commit
    ≤ D.last = σ.last` from raft's invariant on `raftState`.
  - `appliedTo`: the `Applied` premise.
  - `Restore`/`assertConfStatesEquivalent`: a valid `m`, with `ConfState.Is` up to permutation.
- **The restart model.** `StorageHolds` + `Durable.wcommit` admit a client-made snapshot (etcd's
  `CreateSnapshot` at the applied index, restored from the WAL with `ValidSnapshotEntries`), a
  restart after a graceful stop, a joiner's empty storage, and an index-0 configuration snapshot
  (the examples). This is a real improvement on R2d'a's `σ.b = 0` scope.
- **The bootstrap handling** (point c).
  - The decisions fixed at allocation, the view after `StartNode` at `|boot|` and the
    "below the view only a no-op" case agree with Go: `Changer.Simple` of an existing voter changes
    nothing.
  - They also agree with etcd: it applies the bootstrap entries' own changes, decoded with
    `Id = 0`, and `confDecided`'s `.apply (.v1 ⟨AddNode, p.1, p.2, 0⟩)` matches.
  - A bootstrapped member that restarts before its first snapshot gets etcd's index-0 snapshot with
    the backend's configuration at `a = ci`, which the spec covers (modulo S3).
- **The storage-ownership design** (point b). "Attached once, client writes only through raft's
  updates, `InitialState` the only non-atomic method, called only from `newRaft`" matches the code
  (grep: `InitialState` only at raft.go:444). It is sound once F2 and S1 are repaired.
- **The `MemoryStorage` models** (`StorState.append`/`applySnapshot`/`createSnapshot`/`compact`)
  match storage.go:218-325 case by case, including truncation below the first index and the
  `last < first` shortcut (below 2^64).
- **The select pattern works.** Perennial's blocking select takes each case's precondition under
  `∧` (Chan.lean:283-286). `readyChan_recv` consuming `nodeDriver` in one case leaves it to the
  others, so etcd's `select { ticker | Ready | stopped }` is provable.

## Snippets (point e), one line each

- `propose.go:ReqProposeOnce`: provable. `isCtxErr` → `errors.Is` of `Canceled`/`DeadlineExceeded`;
  `errIs` → `errors.Is` of raft's errors. The context must be `isContext` (F5b).
- `propose.go:ReqProposeRetry`: provable (`□` update reused across calls).
- `readindex.go:ReqLinearizableRead`: provable. If `rs.Index < writeIndex`, fire `readState_fire`
  with the write's `committedLb lw` (`rs.Index ≤ |lw|`). The read's `Q ops := opsOf lw <+: ops`
  (stated inside the persistent update, through `committedOps_lb`) contradicts a log shorter than
  the write's own index, by counting operations: the write's entry is a non-filler.
- `readyloop.go:ReqReadyLoop`: provable after S6 (the stop assumption reversed, the view at the
  start applied index) and F2.
- `readyloop.go:ReqMustSync`: trivially provable.
- `readyloop.go:ReqDisrupt`: not provable (F5a).
- `confchange.go:ReqProposeV1`: not provable (F5a).
- `confchange.go:ReqProposeV2Joint`: provable. The empty `ConfChangeV2` is an `isEmptyV2` entry,
  consistent with `opsOf`.
- `confchange.go:ReqApplyOrRefuse`: provable with S4 and S7's `Assumes`.
- `storage.go:ReqBootstrapFromWAL`: provable (detached; `applySnapshotErr` is false at the empty
  storage; `hsPtr` round trip), given S1's realization.
- `storage.go:ReqSnapshotCompact`: provable after F2 (`stor_createSnapshot` via `snap_make`;
  `stor_compact` via `appliedLb`/`storSnapLb`), for `applied > 0`.
- `restart.go:ReqStartFresh`: not provable until F4. Also S5.
- `restart.go:ReqRestartDurable`: provable with `a = σ.off`. Its `Assumes` needs F3's premise.
- `restart.go:ReqJoin`: provable (`confAt γ 0 empty` from a bootstrap log; `freshIds_take`).
- `restart.go:ReqStopRestart`: not provable (F6).
- `transport.go:ReqDeliver`: not provable (F5a; the response pointer, S7).
- `transport.go:ReqSendSnapshot`: provable only through `msgSent_replaceSnap`, which is unsound
  (F1). With F1's fix, its `Assumes` suffices.

## The author's claims, checked

- **"`InitialState` is non-atomic (it reads unlocked)" and "the same spec detached or attached".**
  True of the code, but the realization stated does not support it (S1).
- **Open question 4 (`msgSent_replaceSnap` safe at any term).** False: F1.
- **"One start spec for all durable states".** Holds for the durable-state relation. It misses the
  stored snapshot's validity (F3) and etcd's crash case `a > commit` (S3).
- **"`ApplyConfChange` accepts an entry below the view when its change is a no-op".** Checked
  against etcd's bootstrap: correct.
- **"Everything builds".** Not checked (I built nothing).

## Bugs in the Go code

None found that belongs in `issues/`.

- `MemoryStorage.Term`'s signed conversion (F7) is outside the documented range: at most a
  `nonissues/` entry, documentation only.
- F3 raises a question for 2d/2e. etcd restores a snapshot whose `ConfState` is the configuration
  at the consistent index, not at the snapshot's index (bootstrap.go:107-115). If raft later sends
  that storage snapshot to a follower, the follower installs the configuration at `ci` with the log
  at `si`. Uncertain whether this is reachable or harmful. I did not trace it; `issues/` has no
  entry.

## Targets ranked by need of revision

1. **`Api.lean`**: F1 (`msgSent_replaceSnap`), F2 (the storage laws' masks), F5 (`nodeErr`, the
   context predicate), F7 (`isStorage`'s `Entries`/`Term`), S1 (the `memStor` realization), S2
   (the read law), S4, S5.
2. **`RestartNode.lean`, `NewRawNode.lean`**: F3, S3.
3. **`Model.lean` `BootLog` with `StartNode`/`setupNode`/`RawNode__Bootstrap`**: F4.
4. **`node__Stop.lean`**: F6. **The `node.*` specs with a context**: F5.
5. **`MemoryStorage__Term.lean`, `MemoryStorage__Append.lean`, `MemoryStorage__Entries.lean`,
   `MemoryStorage__InitialState.lean`**: F7 bounds, S1.
6. **Snippets**: S6, S7.
7. **The rest** (`node.Propose`/`ProposeConfChange`/`ReadIndex`/`Advance`/`ApplyConfChange`/
   `Ready`, the `RawNode` mirrors, the helpers): sound as far as I traced.

## Verdict

Not done. There are seven first-tier findings:

- one unsound law (F1);
- one family of laws unprovable as masked (F2);
- one missing restart premise (F3);
- one unprovable start (F4);
- two kinds of unprovable snippets (F5, F6);
- one contract that admits a raft panic (F7).

Each has a local fix that keeps the design. The design itself holds up under the checks I made:
the `Ready`/enter/check updates, durability, the bootstrap view and `ConfigOk`. A second round is
needed after the repairs.
