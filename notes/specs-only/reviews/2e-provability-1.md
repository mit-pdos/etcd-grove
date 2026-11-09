# Batch 2e, provability review, round 1

Reviewer: provability (2026-11-09), at `e6d943c00b`. Read-only; Go sources at the pins in
`notes/specs-only/README.md` (server `a4d2bb17`, abbreviated `srv/`; pkg `a4d2bb17`, `pkg/`).
`batch-2e.md` read for its file list only, until these findings were written; its open questions
Q1-Q6 are cross-referenced where a finding touches one.

## What is good

- **The restart hub is clean.** `memberStart` with three intro laws, `memberDisk` as client-owned
  durable state, `srvRunning` → `memberDisk` at `HardStop`/`Stop`: this is the raft durable-node
  shape (a restart is a fresh volatile half). None of R2d'a's eight premises comes back under
  another name. `rnWalCommitAbove` is not needed: R1's `RestartNode.spec` takes the configuration
  point `a = ci` unbounded by the stored commit, and 2d replays above `ci`. `srvWinPend` is not
  needed: R1's `snap_make` admits a snapshot at `si` with the configuration at `a ≥ si`, which is
  exactly `bootstrap.go:103-115` (`buildConfStateFromV3store`). `memberDisk`'s header says outright
  that every binder is tied to the files, and the `ci > hs.commit` case is stated, not assumed away.
- **`NewServer.spec` returns `s = null` on every error path.** All six error returns in
  `srv/etcdserver/server.go:295-442` are `return nil, err`. The Margin is honest about the start
  right being lost and the raft node leaking.
- **The WAL calls are linearizable under `w.mu`** (`srv/storage/wal/wal.go:1032`, `1076`, `941`),
  so one AU per call is the right shape. `Close` takes the purge right and gives it back.
  `Release`'s premise (a saved record at the index) closes the old latent gap. `Sync` changes
  nothing.
- **`ccResult` matches `ValidateConfigurationChange`** case for case (`srv/etcdserver/api/membership/cluster.go:306-391`).
  This covers: the removed check first; promote versus add; `ErrIDExists`, then `ErrPeerURLexists`
  by string over all members; the learner limit only for `AddLearnerNode` with `IsLearner`; remove;
  update excluding the member itself; the panics in `ccPanicFree`. The `apply = false` arm is
  right. `AddMember`/`RemoveMember` at `apply = false` change nothing, as the fork does
  (`cluster.go:394-460`). `UpdateAttributes`' member-or-removed premise is exactly the
  `lg.Panic` path.
- **The compactor slot (`bootCfg`, intro and narrow elimination) is right.** The periodic `|ret| ≥ 10ns`
  bound is what `getRetryInterval`'s division needs. The compactor's safety is reduced to calling
  `Compact`/`Rev` safely.
- **`HardStop`'s two `select` arms are both handled.** `run`'s defer order (`server.go:814-831`:
  `stopping`, `cancel`, `sched.Stop`, `wg.Wait`, `r.stop`, `Cleanup`, `close(done)`) gives the
  closer what it needs. `sched.Stop` runs the pending jobs (`pkg/schedule/schedule.go:192-207`,
  `executeJob(todo, true)` ignores the context in `applyAll`'s job), so a received snapshot saved
  in the WAL is applied before the stop.

## First tier (a hard rule broken)

### F1. The WAL's trusted model is false of the fork's `ReadAll` at a received snapshot (`storage/wal/Api.lean`, `Recs.saveSnap`)

**Principle.** Sound: a trusted statement must be true of the code at every input it admits.

**Evidence.** The fork's `ReadAll` (`srv/storage/wal/wal.go:539-550`, the fix of
`nonissues/etcd-wal-stale-entries-above-snapshot.md`) drops the entries above the start snapshot
when that snapshot's index is above the commit saved before it, which is exactly a received
snapshot. `Recs.saveSnap` only appends the record and never truncates `log`.

**Counterexample.** A follower has log 1..5 (term 1) with commit 3 and receives a snapshot at
(4, term 2). The raft loop calls `SaveSnap(4,2)`, then `Save(hs commit 4, [])`.
- The model gives `newest = (4,2)` and `entsAfter = [e5 (term 1)]`.
- Go's restart reads `[]`: at the snapshot record, 4 > 3 and `ents = ents[:0]`.

**Consequence.** `walHolds R D` cannot be kept after any received snapshot: raft's durable `D` has
no entries above the snapshot, while `R.entsAfter` keeps the stale tail. So `memberDisk` is not
producible by 2d's stop on such a run.

**Fix.** Make `Recs.saveSnap R s` truncate `log` at `s.index` when `s.index > R.hs.commit`
(`log := R.log.take (s.index - R.floor)`). That is the fork's rule, and every later record replays
consistently. Re-run `ReqSaveOrder` with a received-snapshot variant.

### F2. `Recs.save` is false at inputs the AU admits (`storage__Save.lean`)

**Principle.** Sound (same rule as F1).

**Evidence.** `R.log.take (k - R.floor - 1) ++ es` misplaces the entries in two cases:
- `k ≤ R.floor` with `es ≠ []`: the model puts `es` at index `floor+1`. Go drops records at or
  below the start and re-truncates (`wal.go:500-516`).
- `k > R.floor + |R.log| + 1` (a gap): the model claims a contiguous log, while Go's restart
  returns `ErrSliceOutOfRange` (`wal.go:507-512`).

Raft never produces either, but the trusted triple claims the model for every `k`.

**Fix.** Add `⌜es = [] ∨ R.floor < k ≤ R.floor + R.log.length + 1⌝` inside the AU's `∃∃ R`. The
caller proves it from `walHolds R D` and raft's batch.

**Smaller, same file.** `Release`'s premise should be `∃ w ∈ R.validSnaps, w.index = sn.index`
(that is, `sn.index ≤ R.hs.commit`), not `R.snaps`. Otherwise `release` can leave the model with
`newest = none` while Go's `ValidSnapshotEntries` still finds unpurged older records. Both of
`Release`'s callers can prove the stronger premise: the apply thread through the notifyc handshake
(`srv/etcdserver/server.go:990`), and `applySnapshot` after the raft loop's `Save`
(`server.go:1057`, `1111`).

### F3. No source for the peer-address resources; aliasing of addresses not excluded (`ApiBoot.lean`: `cluster_alloc`, `memberUrls_take`, `memberStart_*`; brief items c, d)

**Principle.** Every premise has a source; a resource the sketch uses must come from somewhere.

**Evidence.**
- 2f's `Transport.Start` needs `peerAddr ν a` for the local URLs, and `AddPeer`/`AddRemote` need it
  for every peer URL (`Spec/.../rafthttp/Api.lean:38-41`, `316`). It comes only from
  `Http.addrFree a` (`peerAddr_reserve`, `rafthttp/Api.lean:518-520`).
- None of `cluster_alloc`, `memberUrls_take`, the `memberStart` laws or `NewServer.spec` takes or
  carries an address resource. `rafthttpBootCfg` is a pure `Prop`, which cannot carry one. So
  `NewServer`'s step 7 (`tr.Start`, `AddPeer`) has no source for `peerAddr`.

**Consequence (d).** `cluster_alloc` can be applied twice with the same `ms`. The two clusters have
identical member ids and cluster id (`memberIdOf` of the same URLs and token), so rafthttp's
cluster-id check (`checkClusterCompatibilityFromHeader`) passes. Messages of one cluster's members
reach the other's processes at the same URLs, and the two ghost states are mixed.

`Http.addrFree`'s environment premise ("one string per socket", `Spec/net/http/Api.lean:30-35`)
would also settle the DNS and normalization aliases that `ValidateClusterAndAssignIDs` sees
(`cluster.go:768`, `netutil.URLStringsEqual` resolves hosts, `pkg/netutil/netutil.go:147-197`).
But only if the URL sets the join right is keyed by are reserved addresses.

**Fix.**
- `cluster_alloc` takes `[∗] Http.addrFree a` for every initial member's peer host and reserves
  them for the cluster's network (`peerAddr ν a`, with `ν.γ` the raft names in `γ`).
- `memberUrls_take` does the same for a joiner's URLs.
- `memberBoot`/`memberJoin`/`memberDisk` carry the persistent `peerAddr`s, so that `NewServer`
  hands them to the transport.
- Key the memberUrls distinctness by reserved address, not by `List.Perm` of strings.

### F4. The join right keyed by URL strings is unsound against `MemberUpdate` (`memberStart_join`; Q1; brief item c)

**Principle.** Sound. A trusted triple, `bootstrap.spec`'s join case, must be true of every run the
pre admits.

**Evidence.**
- `bootstrap` assigns the joiner the id of whichever existing member's peer URLs equal its own,
  at the time of `GetClusterFromRemotePeers` (`srv/etcdserver/bootstrap.go:343-373`,
  `cluster.go:755-783`).
- W0's model has `memberUpdate id urls` (`Spec/go_etcd_io/etcd/api/v3/Model.lean:1150-1157`). It
  refuses only URLs used by another member, not URLs a pending join right holds.

**Run.**
1. A member `X` is running (an initial, restarted, or joined member).
2. The program takes `memberJoin γ u2` for fresh `u2`. This is allowed: `u2 ∉ U`.
3. Some client calls `MemberUpdate(X, u2)`; it commits.
4. A process starts with `memberStart_join` at `u2`. `ValidateClusterAndAssignIDs` gives it `X`'s
   id, and two processes now run raft node `X`, one with empty state, so it can vote twice in a
   term.

The header's realization ("the invariant reserves raft's vacancy for every id added under a
pending URL set") has nothing to hand this joiner: `X`'s `nodeVacant` is gone. So `bootstrap.spec`'s
post is false here. The same happens through `memberJoin u` after `X` (added under `u`) has
already started and then been updated to `u2`.

**Fix.** The join right must pin the URL-to-id mapping from the right's issue to the join's read.
Options to put to the user:
- (i) W0's original K2: `etcdLb γ σ` naming member `id` with URLs `urls`, plus a per-id token
  minted by the add's commit. Add a scope premise, carried by the cluster's invariant: "no
  `memberUpdate` moves URLs onto a pending joiner's or off it". A workload premise on the
  `MemberUpdate` callers, stated where they call (1c's `Cluster.MemberUpdate`).
- (ii) Keep URL keying, but make `memberUrls` the authority that `memberUpdate`'s Step must
  respect. That is impossible without changing Go, so it is again a client premise.

Either way, Q1's "accept?" is not enough as posed: the cost is not only "a removed initial
member's URLs cannot be joined again".

**Related.** `bootstrap.spec` trusts that the joiner's remote peers answer with `γ`'s committed
view (Q4). That answer is etcdhttp's `/members` (`srv/etcdserver/api/etcdhttp/peer.go:39,66`),
which no spec covers. In this repository's starters, only `RaftHandler` is served
(`examples/lib/etcdstart/common.go:172`), which answers 404 there. So `ReqJoin` always takes its
error branch (vacuous), and the trusted claim rests on an unspecified handler that the HTTP closed
world (`raftProto`, "every other request: nothing") does not constrain. State the `/members`
handler's protocol (part of the reserved address's `Proto`), or make the remote view a premise
the joiner can establish.

### F5. `memberDisk` (exclusive `snapDbs`) conflicts with the raft handler, which outlives the stop (`ApiBoot.lean` realizations, `raftHandler`, `Snap.snapDbs`; brief item f)

**Principle.** Realizations must be satisfiable at once. Here two of them conflict.

**Evidence.**
- `raftHandler h γ id` is persistent, and the programs serve it on the peer listener
  (`examples/etcd/restart/restart3.go:79`). They close the listener only after `HardStop`
  (`restart3.go:102-103`), and in-flight handlers outlive a listener close.
- The snapshot handler calls `h.snapshotter.SaveDBFrom` before `Process` (`rafthttp/http.go:279`),
  with no stopped check (`http.go:215-279`).
- 2e's request to 2f (item 3) makes `SaveDBFrom` an update over `snapDbs`, held by "the server's
  invariant". But at `HardStop` that `snapDbs` moves into the client-owned `memberDisk`. A `POST
  /raft/snapshot` after the stop, or during the next incarnation's `bootstrap`, writes a
  `.snap.db` file that `memberDisk`'s `F` does not record.

The handler's proof cannot fire the update, and the trusted meaning of `snapDbs` is false of the
directory.

**Fix.** Do not hold `snapDbs` exclusively across incarnations. Split it into:
- a persistent directory invariant: every `.snap.db` file at index `j` is an image certified for
  `j` (`snapImage`/`ν.img`), which any handler, old or new, may extend;
- the exclusive part, only for what the restart and the apply thread need: the file at the WAL's
  newest index while `ci <` that index, kept by the apply thread until it opens it.

The alternative is a stop right for the handler (its listener closed and drained) that `HardStop`
takes. Go's `http.Serve` gives no drain, so the first option is better.

### F6. Bounds: specs that read-lock or `wg.Add` take no `threadTok` (`EtcdServer__GoAttach`, `__Logger`, `__CutPeer`, `__MendPeer`, `isConnectedSince` and kin, `adjustTicks`, `transporterOk`)

**Principle.** A bound is reasoned about where it is owned. The owner turns a `threadTok` into a
reader slot; a spec in between takes the caller's `threadTok` (CLAUDE.md, "Bounds"; PRINCIPLES,
"An exclusive resource the code needs is covered by a token").

**Evidence.**
- `GoAttach` does `wgMu.RLock()` and `wg.Add(1)` per call (`srv/etcdserver/server.go:2436-2453`).
  Its spec takes only `isServer` and `f`'s WP. The sketch says "a wait group backed by thread
  tokens", but nothing supplies one. Perennial's token-backed wait group needs `threadToks`
  (`.lake/packages/perennial/Perennial/Proof/sync/WaitGroupTokJoin.lean:92`). `specs-ref` took a
  reader slot and a level token.
- `Logger()` read-locks `lgMu` (`server.go:444-449`). Its Changes paragraph says "no slot (the
  lock's owner keeps the readers)", but the owner still needs the caller's token.
- `EtcdServer.CutPeer`/`MendPeer` call 2f's `Transport.CutPeer`/`MendPeer`, which take `threadTok`
  (`rafthttp/Transport__CutPeer.lean`).
- The provisional `transporterOk` ("`ActiveSince` may be called from any goroutine") hides the same
  need for `ActiveSince`/`ActivePeers`.

2c's request-path specs take `threadTok`, so 2e is inconsistent with its neighbours too.

**Fix.** Add `threadTok` (given back) to `Logger`, `CutPeer`, `MendPeer`, the `util.go` helpers and
`adjustTicks`. Restate `transporterOk` as the `Transporter` bundle with token-taking methods. Give
`GoAttach` a token that the goroutine holds until `Done` (the bounds plan's thread pool), with the
stopped branch giving it back. `ReqPartition` then needs a token in its `Assumes`.

### F7. Snippets not provable from the specs (brief item g)

**Principle.** A snippet must be provable from the batch's specs and laws.

- **`ReqStartOne`'s `MemberID() == 0` panic.** No law gives `id ≠ 0`. `MemberID.spec` returns
  `#(W64 id)` with `id : Nat` unbounded, so `W64 id = 0` is not excluded even for `id ≠ 0`.
  - Fix: `srvMember_id : srvMember s γ id ⊢ ⌜0 < id < 2^64⌝`. It is true: `NewClusterFromURLsMap`
    refuses id 0, and the WAL metadata is a `uint64`.
- **`ReqStartThree` (distinct ids) and `ReqJoin` (`s2.MemberID() ≠ s1.MemberID()`).** `NewServer`'s
  post is `∃ id` with no link to which `memberBoot`/`memberJoin` was spent, and there is no
  exclusivity across servers.
  - Fix: `srvBuilt_excl`/`srvRunning_excl` over `(γ, id)` (each realization holds the node's
    running token or `nodeVacant`'s replacement for `id`). Also state `memberStart_new`'s id
    (`id = m.id`) in `NewServer`'s post.
- **`ReqStopAfterError` calls `s.StopNotify()`, which has no spec.**
  - Fix: a spec giving a receive on `done` that leaves the escrow (a persistent closed-channel
    handle).
- **`ReqSaveOrder`, `ReqSnapRoundTrip`, `ReqMembers`, `ReqCompactorLifecycle` need resources or
  specs that nothing gives.**
  - `ReqSaveOrder`: `wal.Create`/`wal.Open`/`ReadAll` have no specs (`walOpen`, `walRecs`).
  - `ReqSnapRoundTrip`: no law allocates `snapDbs dir F₀` for an empty directory.
  - `ReqMembers`: `NewClusterFromURLsMap`, `NewMember`, `schema.NewMembershipBackend` and
    `MustCreateBackendBuckets` have no specs (so no `isCluster`, `clusterSt` or `beMembers`). Its
    `n+1` check also needs the new member's id distinct from the initial ones, which is not in
    `Assumes`.
  - `ReqCompactorLifecycle`: `compactable`/`revGetter` have no intro law for the fakes. The calls
    through the `Compactor` interface need `isCompactor`'s method triples, but there is only an
    intro law, no elimination (PRINCIPLES, "an interface value gets a bundle", like
    `sync.isLocker`). `start.spec`'s sketch (`s.compactor.Run()`) needs the same elimination.
  - Fix: either add the allocation laws and constructor specs, or reclassify the first three as Go
    tests of the trusted models (worth running: F1 would have shown up) and say so in their
    headers. For the compactor, add `compactable_intro`/`revGetter_intro` from the method's WP,
    and `isCompactor` elimination laws.
- **Referenced snippet files that do not exist.** `ApiBoot.lean:130-133` and `NewServer.lean`
  name `stop.go` and `config.go` (`ReqConfigs`). `GoAttach.lean` names `ReqAttachAfterStop` in
  `stop.go`. None of these exist.

## Second tier

- **S1. The data-directory aliasing premise is stated over strings, not effective directories
  (brief item d).** `dataDirFresh`'s header: "paths pairwise distinct, canonical". A dedicated WAL
  dir `a/member/wal` of one member and the default WAL dir of a member with data dir `a` are
  distinct strings naming one directory (`walDirOf` is opaque). State the adequacy premise over
  `walDirOf ds`, `snapDirOf`, `backendPathOf` and the member dir of every issued `Dirs`, with no
  two equal or nested. Add `memberDisk γ id ds ∗ memberDisk γ' id' ds ⊢ False` (any ids), which
  clients restarting by directory need.
- **S2. `memberDisk`'s realization omits two facts the restart needs.**
  - `RecoverSnapshotBackend` `lg.Panic`s if the WAL's newest index is above `ci` and its `.snap.db`
    is missing (`bootstrap.go:476-479`, `storage/backend.go:106-117`). `memberDisk` must carry
    `ci < newest.index → F newest.index = some img ∧ snapImage …` (`diskOk` does not cover a
    missing file).
  - `RestartNode` needs `snapValid γ ⟨si, term, conf(ci)⟩`. Its source is `snap_make` from a
    `committedLb` of length `si` with that term, plus `confAt γ ci m`, so `memberDisk` must carry
    the persistent `committedLb` (only `confAt` is mentioned).

  Both are in the "…". Name them, since `bootstrap.spec` is trusted over an opaque post.
- **S3. `SaveDBFrom`'s model is false under concurrent saves at one index.** `Exist` then `Rename`
  (`srv/etcdserver/api/snap/db.go:58-71`) races: two snapshot handlers (leaders of two terms
  sending index `i`) can both see no file, and the second rename wins. The model's `saveAt` keeps
  the first. Make the post nondeterministic (`F' i ∈ {F i, some img}`), or fire at the rename with
  "any image certified for `i`" (F5's persistent invariant makes this free).
- **S4. The `--max-learners` divergence (Q5).** `ccResult`'s `r = none ∨ r = some
  .tooManyLearners` is sound for one member, but 2d's `applyStep` is a function of the entry at
  "the proposing member's configuration". Each member applies with its own `maxLearners`
  (`cluster.go:349-353`), so members with different flags diverge on one committed entry: raft
  configurations differ across members. This needs a cluster-wide premise (all members share
  `MaxLearners`) at `memberStart`, carried by the cluster's invariant. It is also an undocumented
  configuration precondition of etcd: a `nonissues/` candidate. Not filed (read-only review).
- **S5. Composition with 2d on `errorc`.** `EtcdServer.run.spec`'s sketch says "`errorc` is never
  sent on". But the transport's `ErrorC` is `s.errorc` (`server.go:423`), and `stopWithDelay`
  (`server.go:1364-1373`) sends on it when the member removes itself. `HardStop.spec` and
  `ReqStopAfterError` rely on `run` returning on it. One of the two sketches is wrong. 2d must
  handle the arm, which ends as a stop, so this is harmless for 2e's post.
- **S6. Member ids: `Nat` here, `w64` in 2d.** `srvMember s γ id`, `memberDisk γ id` and
  `HardStop` use `id : Nat`; 2d's `srvNode`/`srvRunTok`/`srvStopped` use `w64`. 2d's
  `isServer_names` gives `∃ N id` per server, with no agreement law across two servers of one `γ`.
  2c's linearizable reads on two members would need `N` to be a function of `γ` (as the req note
  says, "one record at integration"). Ask 2d for `isServer_names_agree`, or make `Names` a field of
  `Cluster`.
- **S7. `NewServer`'s start right is lost on an error (Q3).** Fine as a margin. But a restart that
  fails on a configuration error (`auth.NewTokenProvider`, `ValidateMaxLearnerConfig`, the
  transport's `Start`) loses the member's `memberDisk` for good, although the directory is
  unchanged on most of those paths. Returning `memberDisk` on the paths before `newRaftNode`
  (`server.go:296-300` and the token-provider error) would be stronger, at no cost to callers.
- **S8. Go code reading, not a reachable bug.** `bootstrap.go:105-109`, in the fork's protobuf-v2
  translation: `sn = &raftpb.Snapshot{}` then `sn.Metadata.ConfState = &cs` dereferences a nil
  `Metadata`. It is reachable only with a WAL holding no valid snapshot record, which an
  etcd-written WAL always has (the index-0 record of `wal.Create`, never filtered by the commit).
  Not etcd-reachable; no `issues/` entry needed. It may be worth a `nonissues/` note as a
  fork-introduced hazard (upstream's `Metadata` is a value).

## Uncertain (not verified)

- Whether `EtcdServer.Compact` with the compactor's context, with no token and auth on, is answered
  as a refusal (state unchanged, `envUpd`'s update aborted) or as a permission error. Either fits
  `compactable`, but 2c's `Compact.spec` was not read.
- Whether zap's `Fatal` in `bootstrap`/`purgeFile` is a non-returning call in the boundary's model
  (a hang, which is fine for a WP) or a panic. `Spec/go_uber_org/zap` was not checked.
- `ReqSaveOrder` was not run. By hand, the model gives `hs.commit = 4`, `ents = [3, 4]`, and so does
  Go: no panic in Go.

## Targets ranked by need of revision

1. **`ApiBoot.lean` with `bootstrap.lean` and `NewServer.lean`** (F3, F4, F5, F7, S1, S2, S6, S7):
   the start rights have no address resources, the join keying is unsound against `memberUpdate`,
   `memberDisk`'s directory ownership conflicts with the live handler, and the laws the snippets
   need are missing.
2. **`storage/wal/Api.lean` with `storage__Save`/`SaveSnap`/`Release`** (F1, F2): the trusted model
   disagrees with the fork's `ReadAll`.
3. **`GoAttach`, `Logger`, `CutPeer`, `MendPeer`, the `util.go` helpers, `adjustTicks`** (F6): no
   thread tokens.
4. **`api/snap/`** (S3, and its share of F5).
5. **`examples/specreq/etcdserverboot/`** (F7): the unprovable checks, the missing files, the
   model-tester snippets.
6. **`api/v3compactor/`** (F7: the interface bundle's elimination laws, the intro laws).
7. **`api/membership/`** (S4 only; `ccResult` is right).
8. **`EtcdServer__HardStop`/`Stop`/`Cleanup`/`start`/`Start`** (S5 composition; otherwise sound
   against `run`'s defer).
9. `config/`, `features/`, `v2stats/`, `v3alarm/`, `v3election/`, `v3lock/`, `leasehttp/`: not
   reviewed in depth. `v3alarm`'s `Activate`/`NewAlarmStore` were read and found consistent with
   the fork's `AlarmStore.Recover` fix.

## Verdict

**Not done; a round 2 is needed.** Seven first-tier findings. Two are false trusted statements
(F1, F2: the WAL model against the fork's `ReadAll`). Three are cluster-contract soundness gaps:
F3 (no address tokens: two allocations alias), F4 (the URL-keyed join right against
`memberUpdate`), and F5 (`memberDisk`'s snapshot directory against the live raft handler). F6 is a
bounds rule broken by six specs. F7 covers the snippets that cannot be proved. The restart
composition with R1 and 2d (brief item a) is the batch's strength: no R2d'a premise returns. It
needs F1 and S2 to be realizable.
