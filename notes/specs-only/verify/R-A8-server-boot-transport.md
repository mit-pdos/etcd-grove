# R-A8: re-review of server boot/storage (2e) and rafthttp (2f) after the repairs

Reviewer: an independent re-review, 2026-11-09, at `974e05095b` (worktree `specs-only`), against
`1aa6fc1337` (the verification round). Read-only, except for this report. I wrote the verdict on each
original finding before I read `repair-server-core.md` and `repair-server-boot.md`. I read those two
afterwards, only for the crash part, to check whether my new findings were already recorded. None of
them was.

Scope:
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/{membership,snap,v2stats,v3alarm,v3compactor,v3election,v3lock,rafthttp}`;
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/{storage (top level), storage/wal, config, features}`;
- the crash parts of `etcdserver/ApiBoot.lean`;
- the snippets `examples/specreq/{etcdserverboot,rafthttp}`.

I put the most weight on the crash story, end to end.

## Verdicts

| batch | verdict | why |
|---|---|---|
| **2e** (boot, storage, WAL, snap, membership, compactor, election/lock, config, features) | **FAIL** | Four new first-tier findings, all in the crash story (N1-N4). The crash restart still does not compose. Outside the crash story, every original finding is resolved or recorded. |
| **2f** (rafthttp) | **PASS WITH OPEN DECISIONS** | The only open decision is 5.9 (etcdmain/embed write `ConnReadTimeout`/`ConnWriteTimeout`). F8 is resolved. N3(a) blocks the server's realization of `saveOk`, which the snapshot handler and `snapshot.go` rely on, but the fix is in 2e's specs (`OpenSnapshotBackend`, `dbFile_rename`); no 2f statement changes. One second-tier item: S3. |

## The original first-tier findings

Each status below was checked against the spec text at `HEAD` and the Go code (`.lake/src/server`).

| # | finding | status at `HEAD` |
|---|---|---|
| P-F1.1 | `crashScope` was a parameterless `Prop` | **Resolved differently.** It is now a disjunct `crashOutOfScope γ ds` in `disk_crash`'s conclusion (`ApiBoot.lean:278,585-593`). But the new predicate is unconstrained: see **N2**. |
| P-F1.2 | no WAL crash law | **Resolved.** `walWriting`, `walRecs_crash` and `walWriting_crash` (`wal/Api.lean:228,255-266`). `storage.Save` and `storage.SaveSnap` now have two updates (`storage__Save.lean`, `storage__SaveSnap.lean`). |
| P-F1.3 | `crashedMid` was missing the case "all entries plus the new state record, unsynced" | **Resolved** (`wal/Api.lean:168-172`). The two cases match raft's split `raftState_crash` (`raft/v3/Api.lean:909-921`). I checked: the old record with a prefix `j` against case 1, the new record with all entries against case 2, and the commit range `[syncedCommit, hs.commit]` against `[wcommit, commit]`. |
| P-F1.4 | the backend's crash law cannot be reached; no generations | **Partly resolved.** `disk_crash` is now per generation and threads `crashRest` over `diskFiles ds`, and the server uses 4a's names. But the realization of `diskState` at `L'` needs raft's and W0's vocabulary at `L'`, and no law gives it (**N1**). The idle path cannot be proved (**N4**). |
| P-F2 | `diskAcc`'s masks block the raft loop's write and the restart | **Resolved.** `diskAcc` is now an accessor at `diskN` (`ApiBoot.lean:291-293`). `γ.raft.ns = etcdN .@ "raft"` is disjoint from `diskN` (`ApiApply.lean:552,603`). `RestartNode`'s update at `⊤ ∖ ↑γ.ns, ∅` can be built: open `diskN` inside it, then weaken the mask. |
| P-F3 | a member that stops itself (`errorc`) closes the backend under in-flight readers | **Resolved as a recorded open decision**: A7 and C46 (`open-questions.md:56-60,872-875`). `run.spec`'s text states the scope. The `ReqErrorC` snippet no longer claims that the stop is safe (`rafthttp/transport.go:139-145`). |
| P-F4 | member ids that raft reserves | **Resolved.** `cluster_alloc` now has a premise (`ApiBoot.lean:538`), and `nonissues/etcd-member-id-raft-reserved.md` exists. |
| P-F5 | provisional storage names were never bridged to 4a | **Resolved.** `OpenBackend` and `OpenSnapshotBackend` return 4a's `isBackend`. `beClosable` is 4a's whole-open handle. `Snap.beFile` is an abbreviation of `Backend.beFile`. `Snap.dbFile_rename` is the trusted bridge for `os.Rename`. Remnants (second tier, S5): `beReadable` is still provisional (`EtcdServer__Backend.lean:50`, not in my directories), and the docstrings of `bootstrapped{Server,Storage,Backend}.Close` (line 9 of each) still name `ServerStorage.beOpen`. |
| P-F6 | v3lock/v3election stated facts at prefix `name` | **Resolved.** The posts and effects now use `name ++ "/"` (`lockServer__Lock.lean`, `electionServer__{Campaign,Leader}.lean:48,62`). The snippet now uses `Name: "lk"`. |
| P-F7 | `diskOk`'s text did not cover what the trusted specs rely on | **Resolved** (`storage/Api.lean:11-36`). Second tier (S2): a torn tail without a zeroed sector is not named. |
| P-F8 | rafthttp's codec had no laws | **Resolved.** `msgFrame`, `v2Frame` and `v2Compat` are transparent, and `pbEncodes` is replaced by `RaftPb.msgEncodes` (`rafthttp/Api.lean:418-473`). I checked them against `msgappv2_codec.go:87-256`. Second tier (S3): see below. |
| P-F9 | `snapDbs` had no generation | **Resolved:** `snapSaving`, `snapGone`, `snapDbs_crash` and `snapSaving_crash` (`snap/Api.lean:137-199`). I checked them against `db.go:36-96`: two updates around the directory fsync, and the keep-existing branch fsyncs too. Second tier (S1): the rename's source and destination crash independently. |
| C-F1 | `EtcdServer.MemberList` had no spec | **Resolved:** `EtcdServer__MemberList.lean` and the snippet `ReqMemberListAfterAdd`. |
| C-F2 | `urlsRight` raw strings against the parsed URLs | **Resolved:** W0's `urlsRight_norm` (`api/v3/State.lean:213`). A refusal now gives the right back (`EtcdServer__AddMember.lean:63-64`). |
| C-F3 | `RaftCluster.Version`, `SetVersion`, `SetDowngradeInfo` were missing | **Resolved.** The specs exist, and I checked `Version`/`SetVersion` against `cluster.go:579-624`. `Apply.clusterVerOk` is now transparent (`apply/Api.lean:557`). |
| C-F4 | v3lock/v3election message predicates were provisional | **Resolved.** They are abbreviations of 3h's (`v3lock/Api.lean`, `v3election/Api.lean`). `v3client.New` is still the recorded gap (integration I4). |
| C-F5 | exported getters, `MoveLeader`, `Downgrade`, `Pause/ResumeSending` had no specs | **Resolved.** The specs exist, and so do the snippets `ReqGetters`, `ReqPartition` (pause) and `ReqReadyOrStop`. |

Counts:
- 14 original findings; P-F1 is counted once, with its four parts.
- 11 are resolved, 1 is resolved as a recorded open decision (P-F3), 1 is resolved differently but is now vacuous (P-F1.1, which becomes N2), and 1 is partly resolved (P-F1.4, which becomes N1 and N4).

## New first-tier findings

### N1. Nothing carries raft's, W0's or 2f's vocabulary across a crash; `crashGone_intro` has no source for `nodeVacant`

- **Where:** `ApiBoot.lean:565-593` (`crashGone_intro`, `disk_crash`) and `boot.go`'s `ReqCrashRecover`.
- **The law's shape.** `disk_crash` concludes `@diskState ⟨hG.goose_globalGS, L'⟩ …`. The realization the header states (`ApiBoot.lean:87-90,125-136`) holds `raftState γ.raft id D ∗ nodeVacant γ.raft id`, `confDecided` facts and `peerAddr ν a`. At `L'` these are raft's and 2f's opaque predicates at the new heap. Every opaque predicate takes `hG`, and the heap binders landed at `1aa6fc1337`.
- **What exists.** The only crash law raft has is `raftState_crash` (`raft/v3/Api.lean:909-921`), and it stays in the same generation. `grep GooseLocalGS Spec` finds generation-crossing laws only for files: `walRecs`, `snapDbs`, `Bbolt.fileHolds`, `Backend.beFile`.
- **Consequences:**
  - `disk_crash` cannot be realized from raft's API.
  - After the crash, the restart needs `envUpd γ ecfg` at `L'` for `NewServer` (`NewServer.lean:146`). `envUpd` is transparent over `etcdState` at the ambient heap (`State.lean:233-235`). W0 has no `etcdState`/`etcdLb` law across generations, and 2f has none for `srvNet` or for the reserved addresses.
  - So `ReqCrashRecover`'s claim, "a write acknowledged before the crash is read after the restart", has no proof: the client's `etcdLb` from before the crash is a resource of the dead generation.
- **`crashGone_intro` (`srvRunning ∗ crashed ⊢ |==> crashGone`).** Its docstring says `crashGone` carries raft's `nodeVacant`. While the node runs, raft holds the vacancy (`rawNode ∗ nodeRunning`, held by the run goroutine). Raft has no law that gives `nodeVacant` back after a crash: `rawNode_drop` needs the goroutine's tokens. Open question 2.7 asked "should raft export a crash law?" and settled on "the crash rule's". But Perennial's crash rule (`CrashAdequacy.lean:16-33`) hands over only `crashed`, the extensions' `crashStart` and the crash frame; it gives nothing of raft's.
- **Who is affected:** `ReqCrashRecover`, 2d's `ReqCrashKeepsAnswered`, W0's adequacy (K6).
- **Fix:**
  - Raft: laws that carry the cluster and per-node resources to `L'` (`raftState`, `nodeVacant`, the persistent cluster facts), or one statement that raft's vocabulary does not depend on the local generation. Also a node crash law, for example `isNode n γ id ∗ crashed ⊢ |={⊤}=> nodeVacant γ id`, since raft's invariant can keep the vacancy token.
  - W0: `etcdState`/`etcdLb` across generations.
  - 2f: `srvNet` and the peer addresses across generations.
  - Then `top.md` K6 can drop "until raft's crash transition exists". It also still names `crashScope`.

### N2. `crashOutOfScope` is unconstrained, so `disk_crash` holds trivially

- **Where:** `ApiBoot.lean:274-278,568-569,590-592`.
- **The gap.** `crashOutOfScope γ ds` is an opaque persistent `IProp`. Nothing consumes it, and no law ties it to anything. A realization `crashOutOfScope := True` proves `disk_crash` by its right disjunct, whatever the disk holds.
- **Why the adequacy theorem cannot save it.** The header says "the adequacy theorem excludes the disjunct as its environment premise". But an environment premise is a statement about executions, and nothing connects this ghost predicate to one. This is exactly the problem the original F1.1 described ("a constant `Prop` … the realization can extract nothing"), moved one step along.
- **Who is affected:** every use of `disk_crash` (`NewServer` round 2, `bootstrap`, `raftNode.start` step 6, `ReqCrashRecover`), and W0's K6.
- **Fix.** State the scope in terms whose meaning is physical: the WAL's records. `walRecs` is trusted to mean "what `Open` + `ReadAll` returns". For example, the right disjunct could be

  `∃ R w R', ⌜R.crashedDuring w R' ∧ (w is a snapshot write ∨ ¬ (restartView R').confAboveOk)⌝`

  (or a transparent `crashOutOfScope` defined so), so that W0's premise "no crash leaves a WAL whose replay breaks `confAboveOk` …" excludes it.
- **Also fix the header.** `ApiBoot.lean:152-153` says `diskState` "keeps R1's durable invariant that at most one conf-change entry is above `wcommit`". That is not an invariant raft gives: a lagging follower stores committed entries holding several conf changes above its stored commit (open question 2.8). It also contradicts the first case of `crashOutOfScope`. Drop it.

### N3. The install holds the backend file's revert state and file across a non-atomic call

- **Where:** `storage/OpenSnapshotBackend.lean` (pre `Backend.beFile path o ∗ Backend.beNoRevert path`; post `beRevert path o`) and `snap/Api.lean:215-225` (`dbFile_rename`).
- **(a) A concurrent snapshot handler cannot finish.** `SaveDBFrom`'s second update takes `Backend.beRev p rv` for the backend entry `p` at the directory fsync. The client supplies it through `saveOk` "from its invariant" (`rafthttp/Api.lean:241-256`). This was moved there in the final relay round precisely so that it is not held across a call. While the apply thread is inside `OpenSnapshotBackend`, it holds `beNoRevert`, so the invariant cannot supply it. A rafthttp snapshot handler runs concurrently with `applySnapshot`, so the server's `saveOk` cannot be built. This is the same loan problem the relay round fixed for two handlers, now between a handler and the install.
- **(b) Two installs in a row cannot both establish the premise.**
  - `dbFile_rename` and `OpenSnapshotBackend` require `beNoRevert`. After one install the state is `beRevert`, and only a later `SaveDBFrom`'s fsync clears it.
  - The schedule is reachable:
    - the handler saves snapshot A and then B (two leaders, or a delayed `MsgSnap`);
    - the raft loop hands out A's `Ready`. Its first `notifyc` comes after `Sync` (`raft.go:284`), and its second `notifyc` (`raft.go:307`) only waits for `applySnapshot` to receive the first, which happens before the rename (`server.go:1057-1068`);
    - `Advance` then lets B's `Ready` through;
    - the apply thread renames A and then B, with no save in between.
  - The second rename's premise has no source (`beRevert_noRevert`, `Durable.lean`).
- **(c) A crash during the install loses the files.** The apply thread holds `beFile`/`beNoRevert` outside `diskState` for the whole call, so a crash there leaves `disk_crash` without the backend file for `beCrash`. The WAL and `SaveDBFrom` already use two-step updates for exactly this reason.
- **Fix:**
  - Take the revert state, and the destination's file, inside the rename's atomic update:

    `AU <{ ∃∃ F H rv, snapDbs sd F ∗ snapGone sd H ∗ Backend.beRev dst rv ∗ beFile dst o }>`

    with the update giving `beRevert dst (prev)`.
  - Let `beRevert` carry every image a crash may restore. After two unsynced renames onto `db`, a journaling file system may keep either of them or neither, so the possible images are `o0`, A's or B's. That needs `beRevert p (os : List (Option Image))` (4a's), with `beCrash` choosing among them.
  - With this, `OpenSnapshotBackend` holds nothing across the call except what `New` takes.

### N4. `diskIdle_crash` cannot be proved, and crashes outside `[Start, HardStop]` lose the disk

- **Where:** `ApiBoot.lean:571-577` and `565-566`.
- **The idle law.** `diskIdle_crash` is `diskState ∗ diskIdle ∗ crashed ⊢ |==> diskState@L' ∗ diskIdle@L'`. For a stopped member, `diskState`'s realization holds the closed backend file `Backend.beFile path (some img)` (`ApiBoot.lean:87-90`; `Cleanup` gives the file at rest). That predicate is 4a's and is backed by OsFs (`beFile_bytes`, `beFile_of` over `osMeta`/`fileHolds`), and its only crash law, `beCrash` (`Durable.lean:121-131`), takes an open backend's `beDurInv`/`beHist` together with `crashRest` and a `|={⊤}=>` update. `diskIdle_crash` takes no `crashRest` and is a plain update, so it cannot produce `beFile` at `L'`. It cannot open the per-directory invariant that holds `snapDbs` either (`ApiBoot.lean:94-101`).
- **The crash windows.** `crashGone` comes only from `srvRunning` (`crashGone_intro`), and `diskIdle` is consumed by `memberStart_disk`. A crash in any of these windows leaves the disk with neither:
  - inside `NewServer`/`bootstrap`, the WAL replay included (the common crash-loop case);
  - between `NewServer` and `Start`;
  - inside `HardStop`/`Stop`/`Cleanup`;
  - after `Cleanup` before `Start`.

  `ReqCrashRecover` says "after a crash of the process **at any point**". That claim is not served.
- **Fix:**
  - One crash law per disk that takes `diskState ∗ crashed ∗ crashRest` and a `|={⊤}=>` update. The disk's invariant records whether a server runs, so neither `crashGone` nor `diskIdle` is needed; the vacancy comes from N1's raft law.
  - Keep every durable resource in `diskState` at every step (two-step updates, as in N3).
  - 4a: a crash law for a closed file at rest, `beFile p o ∗ beRev p rv ∗ crashed ∗ crashRest Ps ⊢ |={⊤}=> ∃ o', ⌜o' = o ∨ rv = some o'⌝ ∗ beFile@L' p o' ∗ beNoRevert@L' p ∗ crashRest (p :: Ps)`. A closed bbolt file's last commit was fsynced.

## Second tier

- **S1** (`snap/Api.lean:122-124`, `Durable.lean` `beCrash`): the rename's two sides crash independently. `snapCrashed` (the source may stay gone) and `beCrash`'s `rv = some o0` (the destination may revert) together admit a state the code cannot reach: the backend reverted to `o0` (consistent index below the snapshot) with the snapshot's `.snap.db` gone. A rename within one directory is atomic across a crash. After such a crash, `RecoverSnapshotBackend` fails, so in the model the restart fails where Go succeeds. This is not unsound (`NewServer` may fail), but it is a needless restriction of the crash restart. Fix: a joint pending-rename token with one crash law (`dst = img ∧ src gone` or `dst = o0 ∧ src = img`).
- **S2** (`storage/Api.lean:16-19`): `diskOk`'s crash clause should name the case of a torn tail with no all-zero sector. `decoder.go:119-127`'s `isTornEntry` reports `ErrCRCMismatch` there, and `bootstrap` exits. Under OsFs's power-loss model, dirty bytes are arbitrary.
- **S3** (`rafthttp/Api.lean:459-460`): `v2Frame`'s full frame sets the next state to `m.index + |m.entries|`. The Go sets it to the last entry's `GetIndex()` (`msgappv2_codec.go:146-149,251-254`). The two agree only when a `MsgApp`'s entries are consecutive from `m.index + 1`. Raft guarantees that, but `sendable` (`rafthttp/Api.lean:140-144`) does not state it, so the encoder's post is false at such an input. Fix: add it to `sendable`'s `MsgApp` clause, or write the state as the last entry's index.
- **S4:** the header claim about the conf-entry invariant (see N2).
- **S5:** stale text:
  - the `bootstrapped*.Close` docstrings (`ServerStorage.beOpen`);
  - `top.md` K6 (`crashScope`);
  - `storage/Api.lean` still declares the superseded `beOpen`/`beTx`.
- **Trust base, noted:** `Snap.dbFile_rename` is a trusted spec of `os.Rename` that produces 4a's OsFs-backed `beFile`. 4a records this as a gap ("until OsFs has `rename`", `Durable.lean:17-27`). It stays an axiom until OsFs models `rename`.
- **Uncertain:**
  - `EtcdServer.MemberList.spec` takes no `srvGate` share. I did not check whether `requireAuthInfo`'s path reads the backend under the stop. The file is outside my directories.
  - `ReleaseSnapDBs`' single update for a multi-file removal racing a stale `SaveDBFrom` of a lower index. Probably fine with the linearization at the directory listing; not fully checked.

## Regressions and changed files

89 spec files in my directories changed since `1aa6fc1337` (`git diff --name-only`):

| package | changed files |
|---|---|
| rafthttp | 36 |
| v3compactor | 15 |
| membership | 9 |
| storage | 8 |
| v3election (+pb) | 7 + 2 |
| snap | 4 |
| v3lock (+pb) | 3 + 2 |
| config | 1 |
| wal | 1 |
| `ApiBoot.lean` | 1 |

What I checked:
- **Against the Go and their callees:** `ApiBoot`'s crash part, `wal/Api`, `snap/Api`, `SaveDBFrom`, `ReleaseSnapDBs`, `storage.{Save,SaveSnap}`, `OpenSnapshotBackend`, `OpenBackend`'s header, `config/Api` (`backendPath_entry`), `RaftCluster.{Version,SetVersion}`, `rafthttp/Api`'s codecs, `msgAppV2Encoder.encode`, the two decoders, `v3lock/Api`, `lockServer.Lock`, `electionServer.{Campaign,Leader,Observe}`, `v3compactor/Api`.
- **Checked by diff:** the other 31 rafthttp files are sketch-only changes. Each citation they add exists: `RaftPb.msgRecv_intro`, `msgPts_msgAt`, `MessageType.String`, `Types.ID.String_ptr`, `readerAt_dbReader`, `Config.backendPath_entry`.
- **Uncertain:** `SetDowngradeInfo`, `membership/Errors.lean` and the 14 v3compactor method files (a mechanical `R` parameter) were read only for their statements.

Results:
- **False of the code** (a panic path or a wrong post): none, beyond S3.
- **Inconsistent** (a way to prove `False`): none found.
- **Vacuous:** `crashOutOfScope` (N2).
- **Do not close:** `disk_crash` (N1, N2), `diskIdle_crash` (N4), `crashGone_intro` (N1), and the second consecutive install (N3).

## Snippets

| snippet | result |
|---|---|
| `ReqMemberListAfterAdd`, `ReqGetters`, `ReqReadyOrStop`, `ReqPartition` (with pause) | Provable from the new specs. |
| `ReqLockOverInProc` | Provable apart from `v3client.New` (recorded gap); the prefix is fixed. |
| `ReqErrorC` | No longer claims the stop. |
| `receive.go` | Its `msgRecv` change is consistent. |
| `snapshot.go` (`ReqInstallReceived`) | Its assumption is now stated (`dbIn` kept under `r.mu`). It depends on the server's `saveOk`, which N3(a) blocks. |
| `ReqCrashRecover` | **Not provable:** N1 (no `etcdLb`/`envUpd` at `L'`), N2 (the scope is vacuous), N4 ("at any point"). |

Coverage of the completeness report's user patterns:
- **Covered:** wait for ready or for the stop (S2 of the original), pause/resume, the member list, the getters.
- **Still open, on recorded decisions:** Q7 (embed's forced `grpc.Stop`), Q8 (a join through etcd's peer handler), 5.9.

## Counts

- Original first-tier findings: 14. 11 resolved, 1 recorded as an open decision, 1 resolved differently but vacuous, 1 partly resolved.
- New first-tier findings: 4 (N1-N4), all in the crash story.
- Second tier: 5 (S1-S5), plus 2 uncertain items.
- Spec files: 89 changed. 25 checked against the Go, 33 checked by diff (31 rafthttp sketch-only files and 2 pb Api files), 31 statement-only (uncertain).
- Snippets: 10 changed or added. 8 provable (one of them apart from a recorded gap), 1 blocked by N3(a), 1 not provable (`ReqCrashRecover`).

## Ranking by need of revision

1. `ApiBoot.lean`'s crash laws: N1, N2, N4. They need raft-core's and W0's laws across generations, and 4a's crash law for a closed file.
2. `OpenSnapshotBackend` and `Snap.dbFile_rename`, with 4a's `beRevert`: N3.
3. `snap/Api` crash coupling (S1), `diskOk` (S2), `sendable`/`v2Frame` (S3).
4. Stale text (S4, S5).

No new Go bug was found. The reachable double install in N3(b) is a gap in the spec, not a bug: Go renames twice correctly.
