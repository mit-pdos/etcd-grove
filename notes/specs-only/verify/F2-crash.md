# F2-crash: fresh re-review of the crash story

Reviewer: fresh and independent, 2026-11-09, at `HEAD` = `06bf8654dd` (read with the worktree; the
other agent's uncommitted edits are to `notes/` only: `open-questions.md`, `STATUS.md`,
`status-history.md`). Read-only, apart from this file. I wrote my verdict on each finding of
`F-server-boot.md` (F1-F5, G-a, G-b) and `F-raft-storage.md` (F1, F2) from the specs and the Go first,
then read `repair4-raft-crash.md` and `repair5-crash.md` (and `repair2-crash.md` for one disagreement).

Sources: Go `.lake/src/server` (fork `a4d2bb17`), `client/pkg/v3` from the module cache; Perennial
`.lake/packages/perennial/Perennial/GooseLang/{CrashAdequacy,CrashToken,Lifting}.lean`; OsFs
`GooseLang/Ext/OsFs/{Impl,Crash}.lean`. No Lean scratch was needed: every derivation I tried stops
at `crashed` or at a one-shot guard (below), and consistency of opaque laws cannot be shown in Lean.

## Verdict

**FAIL.** Soundness passes. Realizability and closure do not: two crash windows have no
realizable `disk_crash` and are not recorded as gaps (N1, N2). One trusted crash law leaves out a
physical premise it relies on (N3).

**Soundness (question 1): PASS.**
- No combination of the crash laws proves `False`. That includes `L' = hG.goose_localGS`, a law
  applied twice, and the `token ∨ crashed` realizations together with the exclusivity laws.
- No combination proves a panicking program safe.

**Realizability (question 2):**
- Most laws are realizable, apart from the recorded gaps:
  - the crash frame's extraction;
  - OsFs `rename` and directory fsync;
  - G-a (D7, pending);
  - raft's `readyBatch` (D6, pending).
- Three are not: N1, N2, N3.

**`ReqCrashRecover` (question 3): does not close modulo exactly the recorded gaps.** Besides them,
it needs:
- **N1:** a crash after a snapshot install, until the next `SaveDBFrom`.
- **N2:** a crash inside `wal.Create`.
- **N3:** under POSIX as written, which is the standard G-a uses, the whole `member/` directory.

**net/http (question 4): true.**
- `addrFree_protoAt_excl` is true of the intended model and of Go under the whole-program crash
  rule.
- The nonissue's panic is real: `bootstrap.go:482`, by the path below.

Open user decisions in the area:
- 2.8: the crash scope `crashScopeOk`, with its at-rest lagging-follower margin;
- D3: `beDetached`;
- D4: per-generation protocols;
- D5: `addrFree_protoAt_excl`;
- D6: `readyBatch`;
- D7: G-a;
- the rename's joint crash (R-A8 S1, `repair2-crash.md` decision 7). It is recorded, but its
  assessment is wrong: see N1.

## The findings rechecked

| # | finding | status at `HEAD` | evidence |
|---|---|---|---|
| F-s-b **F1** / F-r-s **F1** | `raftState_gen` at `L' = hG` gives a second `nodeVacant`, hence `False` | **Resolved** | `exclusive`'s vacancy clause is now `⊢ crashed` (`raft/v3/Api.lean:599`). The two-vacancy derivation ends at `crashed`, which its premise already holds. Realization: `occ(id, g) ∨ crashed@g` with a per-id record and a token pool (`:920-934`). I checked it at `L' = hG`, at a reused crash name and at a fresh one. At the real `L'` the name is fresh (`crashToken_init`, `CrashToken.lean:68`). 2e's `diskIdle_excl`, `diskIdle_agree` and `memberDisk_excl` give `crashed` (`ApiBoot.lean:643-655`). Second tier: s1 below, Perennial has no lemma that refutes `crashed` at a step. |
| F-s-b **F2** | nothing lets the adequacy proof exclude `crashOutOfScope` | **Resolved; the scope itself is open decision 2.8** | `Wal.crashInScope` (`wal/Api.lean:267`) is taken by `walRecs_crash`/`walWriting_crash`, which add `R'.crashScopeOk` (`:309-324`), and by `disk_crash` (`ApiBoot.lean:753-755`). The disjunct is gone. Sound: the laws need the old generation's `crashed`. Records that already fail the scope at rest give `False` only for a run whose crash is out of scope (`Recs.crashed` only lowers the commit). |
| F-s-b **F3** | a client address cannot be served after a crash | **Resolved; open user decision D4** | `Http.protoFam a F` with `protoFam_at` and `protoFam_gen` (`net/http/Api.lean:395-410`). `srvEp_reserve`'s family `F L := grpcOver (etcdContract@⟨g,L⟩ γ ep) _` (`ApiBoot.lean:837-855`). At `hG`, `protoFam_at` gives `addrAt ep (etcdContract γ ep)` by structure eta. At `L'`, it gives the `L'` instance, whose lease rows name `L'`'s views. Second tier: s4 below, this rests on the whole-program crash model. |
| F-s-b **F4** | `Net.dbIn` names no receiver | **Resolved** | `dbIn : w64 → w64 → IProp` (`rafthttp/Api.lean:171`), `recvd ν id m` (`:264-268`), `saveOk ν lid sd`'s commit `ν.dbIn lid i` (`:281-289`), `Process` over `recvd ν (W64 id) m`. The realization is a generation-independent record per directory (`ApiBoot.lean:104-110`). |
| F-s-b **F5** | `srvEp_agree` has no source | **Resolved; open user decision D5** | `Http.addrFree_protoAt_excl` (`net/http/Api.lean:419`). `srvEp_reserve` opens the cluster's address map at `srvEpN`. `ep ∉ dom M` follows from an entry's `protoFam`, `protoFam_at` (at `⟨g,L⟩`), `addrFree_gen` and the new law. Agreement is within one `γ`. Second tier: s2 below, the realization text. |
| F-s-b **G-a** / F-r-s **F2** | a first boot's file after `Close`; `backend.Close` not provable for a fresh file | **Statements resolved; consequence pending the user (D7)** | `beOpenUpd` adds `none` to the revert list for a created file (`backend/Api.lean:724-731`). `beFile_crash`'s `o' ∈ os` covers the vanish case (`Durable.lean:176`). The reopen goes through `Bbolt.boltReopen_alloc` (`bbolt/Api.lean:607`), and `ReqReopen`'s Assumes is updated. The panic is real (below). N3 widens the decision: under the same model, `member/` is not durable either. |
| F-s-b **G-b** | rename over an open backend | **Resolved, modulo the recorded OsFs `rename` gap; open user decision D3** | `FileSt`, `beAt`, `beRenamedOver`, `beDetached`, `beCloseUpd`'s detached form (`backend/Api.lean:560-575,739-748`), `beDetached_crash` (`Durable.lean:196`). `OpenSnapshotBackend`'s update takes either form. The fold order (`beDetached_crash`, then `beCrash`/`beFile_crash`) is consistent with `beRevs`'s exclusivity. |

## Question 1: soundness, the derivations tried

None reaches `False`:
- **`raftState_gen`/`raftState_crash` at `L' = hG`, any number of times.**
  - They give `raftState@hG` (consumed and given back) and vacancies.
  - `exclusive` turns two vacancies into `crashed`, which the premise already holds.
  - Raft's realization handles the reused name (`cur = g' = g`, vacancy `crashed@g`).
- **`disk_crash`, `beCrash`, `beFile_crash`, `boltCrash`, `dataDirFresh_crash`.**
  - Each needs `crashRest (osGS hG) (osGS L') Ps` with `p ∉ Ps`. The frame gets that only for the
    `L'` it proves, and the law extends `Ps`, so it is one-shot per file.
  - At `L' = hG`, `crashRest` itself holds full `fileStart` fragments at the old OsFs names. These
    conflict with the old generation's `osMeta`, so that instance of the frame is vacuous in any
    case. That is harmless: the real `L'` is fresh.
- **`memberBoot_crash`, `memberJoin_crash`, `walRecs_crash`, `walWriting_crash`, `snapDbs_crash`,
  `snapSaving_crash`, `beDetached_crash`.** Each consumes its exclusive input and gives one
  (`beDetached_crash` gives the old instance's `beRevs`). Iterating mints nothing.
- **`token ∨ crashed` with the other laws.**
  - The exclusivity laws that still say `False` (`raftState`, `diskState`, `dataDirFresh`,
    `memberJoin`, `srvBuilt`/`srvRunning`, `beRevs`, `beDetached`, `walRecs`, `snapDbs`) are over
    resources that no crossing law duplicates.
  - `diskIdle_agree`'s `∨ crashed` and `memberStart_disk` at a kind not tied to `diskState` give
    `memberStart`. `NewServer` refutes the alternative at its first step.
  - A running generation cannot obtain its own `crashed`. Two vacancies or two idle tokens of one
    generation come only from crossing laws, and those need `crashed`.
- **Old-instance resources carried into the next generation.**
  - In generation `g2`, a program holding `crashed@g1` and an uncrossed `raftState@hG1` or
    `walRecs@hG1` can still cross it during `g2`.
  - That is the same move the frame could have made: the resource is single, and its record moves
    once.
  - `disk_crash` needs `crashRest`, which is the frame's only.
- **`walRecs_crash` with `crashInScope` on records out of scope.** It gives `False` only for runs
  that the premise excludes: the margin, decision 2.8.
- **net/http.**
  - `protoFam` has no agreement law, and `protoAt_agree` stays withdrawn.
  - `addrFree_gen` is `⊣⊢`, so a free address is converted, never copied.
  - `reserve` consumes `addrFree`.

## Question 2: realizability, law by law

| law | verdict |
|---|---|
| raft `global`, W0 `etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen`, `peerLeaseServed_gen`, `envUpd_gen` | plausible: global ghost state and invariants (`InvGS` is in `GooseGlobalGS`, so an AU's fupd is the same at `⟨g, L'⟩`). |
| raft `raftState_gen` | plausible from the stated realization. It also needs a lifting lemma that hands a step its `notCrashed`, which Perennial does not have (s1). |
| raft `raftState_crash` | **not realizable as stated: open user decision D6** (`readyEnter` can be forged from `nodeStopped`, `Api.lean:1015-1022`). Recorded. |
| 2e `srvNet_gen`, `srvEp_gen`, `srvEp_reserve`, `srvEp_agree` | plausible (F5 above). |
| 2f `peerAddr_gen` | follows from `protoFam_gen` by definition (`peerAddr` is transparent; `⟨g,L'⟩.goose_globalGS = g`). |
| net/http `reserve`, `protoFam_at`, `protoFam_gen`, `addrFree_gen`, `addrFree_protoAt_excl` | trusted. True of the intended model. The text's `ghost_map` realization needs a correction (s2). |
| WAL `walRecs_crash`, `walWriting_crash` | trusted. True under `crashInScope` and `diskOk`, **but they rely on `member/`'s directory entry being durable, which nothing in etcd makes so (N3)**. Nor is there a law for `wal.Create`'s own window (N2). |
| snap `snapDbs_crash`, `snapSaving_crash`, `dbFile_rename` | trusted. Each is true alone, but the rename's two sides crash independently, which admits a state that panics in `bootstrap` (N1). |
| 4a `beFile_crash`, `beCrash`, `beDetached_crash`, `beOpenUpd`, `beCloseUpd`; 4c `boltReopen_alloc`, `boltRelease`, `boltCrash` | plausible, modulo the recorded OsFs `rename`/directory-fsync gap. In OsFs every file created in a generation keeps `named = false` until the crash (`OsFs/Impl.lean:118`, no directory sync). |
| 2e `memberBoot_crash`, `memberJoin_crash`, `dataDirFresh_crash` | plausible (the raft crossing inside; `crashRest_take` on `osMeta p none`). |
| 2e `disk_crash` | a composition of the above. **Not realizable in N1's and N2's windows** (not recorded), nor in G-a's (D7, recorded), and it is subject to the recorded extraction gap. |

## Question 4: the nonissue's panic, checked

The path is real under POSIX as written and OsFs's D4.

The first boot:
- `bootstrapSnapshot` runs `TouchDirAll(SnapDir)` (`bootstrap.go:211`). There is no fsync, and
  `fileutil.TouchDirAll` is `MkdirAll` plus writing and removing a `.touch` file.
- `bolt.Open` then creates `member/snap/db`.

A local snapshot:
- The fork's `storage.SaveSnap` writes only the WAL's snapshot record (`storage/storage.go:59-70`).
- That record is fsynced, and the state record before it in the file is fsynced with it.
- Nothing syncs `member/snap`. The only directory fsync there is `SaveDBFrom`'s
  (`snap/db.go:61,76`).

The crash and the restart:
1. The crash drops the name `member/snap/db`.
2. `bootstrapBackend`: `beExist` is false (`:256`), and `OpenBackend` creates a fresh file.
3. `recoverSnapshot` (`:449-482`): the newest valid record is `k > 0`.
4. `RecoverSnapshotBackend` (`storage/backend.go:106-118`): consistent index `0 < k`, so it calls
   `OpenSnapshotBackend`.
5. `DBFilePath(k)` fails (a local snapshot makes no `.snap.db`). The error is returned (`:64-66`).
6. `cfg.Logger.Panic` at `bootstrap.go:482`.

Whether ext4 (`data=ordered`) and xfs commit the new name with the file's first `fdatasync` is
plausible from their journaling. I did not verify it on a kernel: uncertain.

`addrFree_protoAt_excl` is a fact about the environment's tokens:
- `addrFree a` is issued once per address and run (`net/http/Api.lean:34-39`). `reserve` consumes
  it, and `protoAt` exists only after `reserve`.
- Per-generation protocols are true of Go under Perennial's crash rule: every socket, connection
  and client thread of the generation dies.

## New first-tier findings

### N1. The install's rename crashes as two independent laws, which admit a state where the restart panics; `repair2-crash.md` decision 7 says this is harmless

**Where:**
- `Snap.dbFile_rename`, `snapCrashed`, `snapDbs_crash` (`snap/Api.lean:123-128,188-200,237`);
- `Backend.beFile_crash`, `beCrash` (`Durable.lean:146,176`);
- the composition in `disk_crash` (`ApiBoot.lean:753`);
- the record: `repair2-crash.md` item 148 and decision 7, and the rename's joint crash in
  `open-questions.md` (D23 in the working copy).

**The step.**
- After an install, `OpenSnapshotBackend`'s rename leaves `beRevs p (o_old :: os)`, and
  `snapGone sd H` with `H k img`.
- At a crash, the prover gets two independent existentials:
  - `beFile_crash`/`beCrash` choose `o' ∈ os`: the old backend back, with consistent index `< k`;
  - `snapDbs_crash` chooses `F' k = none`: the source still gone.
- Physically this pair is unreachable: a rename within one directory (`member/snap/k.snap.db` →
  `member/snap/db`) is atomic across a crash.
- In the model it is admitted, and the restart then **panics**, not errs:
  - the WAL holds the record at `k`, durable before the install (`<-toApply.notifyc`,
    `server.go:1057`, after the raft loop's `SaveSnap`, `Save` and `Sync`);
  - `RecoverSnapshotBackend` calls `OpenSnapshotBackend`, `DBFilePath(k)` fails, and
    `bootstrap.go:482` panics.
- So no restartable `diskState(.member id)` exists for that outcome. `memberDisk`'s realization
  needs "the file at the WAL's newest snapshot index is there when `ci` is below it"
  (`ApiBoot.lean:124-133`).
- So `disk_crash` cannot be realized there. `bootstrap.spec` (trusted, error or success, no panic)
  would be false of such a disk.

**How long the window is.** It lasts from every install (by `applySnapshot` or by `bootstrap`'s
recovery) until the next `SaveDBFrom`'s directory fsync, that is, until the member next receives a
snapshot. Typically that is the rest of the member's life.

**Where I disagree with the record.** `repair2-crash.md`: "not unsound: in the model the restart
may fail (`NewServer` errs) where Go succeeds, and `ReqCrashRecover` returns on that error." This
is false. Go panics at `bootstrap.go:481-482` on that error. So the gap is a first-tier
realizability gap of `disk_crash`, not a harmless margin. K6 does not list it.

**Affects:** `disk_crash`, `ReqCrashRecover` (Assumes: "inside a snapshot install" and "while
serving"), K6.

**Fix:**
- One trusted crash law for the joint rename. `dbFile_rename`'s update records the pending rename
  with its source, e.g. the revert entry `(o_old, some (sd, k, img))` in `beRevs`.
- The crash law gives either `dst = img ∧ F' k = none`, or `dst = o_old ∧ F' k = some img`. This is
  R-A8 S1's own suggestion.
- Or: state the dependency as a trusted bridge law over both outcomes, taken by `disk_crash`'s
  realization.
- Either way, re-tier decision 7 and add it to K6.

### N2. `wal.Create`'s window, between its rename and the parent's fsync, has no crash law; the two texts that describe it contradict each other and the Go

**Where:**
- `ApiBoot.lean:214-217` ("a crash before the rename's fsync leaves no WAL … the kind
  unchanged");
- `bootstrap.lean:46-48` ("the kind moves … at the rename, and a crash before the parent's fsync
  may undo it, leaving no WAL");
- `wal/Api.lean`, which has no law for a WAL being created;
- `disk_crash`'s post `k' = k ∨ ∃ id, k' = .member id`.

**The Go.** `wal.Create` (`storage/wal/wal.go`) does the following, in order:
1. writes `member/wal.tmp` (metadata, snapshot record 0);
2. `renameWAL` (`:185`);
3. `fileutil.Fsync(pdir)` (`:225`).

A crash between steps 2 and 3 may leave the WAL at `Recs.init md`, or no WAL. Both outcomes occur.

**Why no realization works.**
- **If the kind moves at the rename** (bootstrap's text), the outcome "no WAL" leaves
  `diskState(.member id)` with no `walRecs`. `walRecs_crash` always gives one, and `disk_crash`
  cannot give `.boot` back from `.member id`.
- **If the kind moves at the fsync** (ApiBoot's text), the outcome "WAL present" leaves
  `diskState(.boot ms m)`.
  - The restart then takes Go's WAL path: `wal.Exist`, `RestartNode` with no peers.
  - The trusted `bootstrap.spec`'s `.boot` case asserts the no-WAL path (`StartNode` with the
    bootstrap log).
  - Neither the WAL's laws nor `disk_crash` can give `walRecs@L' (Recs.init md)`.

**Affects:** `disk_crash` (a crash "inside `NewServer` or `bootstrap`", which `ReqCrashRecover`'s
Assumes claims to cover), `bootstrap.spec`'s "Crashes inside `bootstrap`".

**Fix:**
1. A trusted WAL state `walCreating wd md`, held by `diskState(.boot/.join)` from the rename to the
   fsync.
2. A crash law `walCreating wd md ∗ crashed ⊢ |==> walRecs@L' wd (Recs.init md) ∨ walAbsent@L' wd`.
3. `disk_crash`'s realization then gives `k' = .member id` (WAL present: raft at `Durable.init`,
   the cluster's configuration at index 0, `RestartNode` from it) or `k' = k`. The post already
   admits both.
4. `bootstrap.spec`'s `.member id` case covers a WAL at `Recs.init`.
5. Make the two texts agree.

**Observation (uncertain, not filed).**
- A single-member cluster that crashes on its first boot anywhere between `wal.Create`'s rename and
  the first `Ready`'s `Save` restarts on a WAL with no bootstrap entries.
- `RestartNode` then runs with an empty configuration and the member never campaigns.
- That is liveness only (no panic, no wrong answer). `ReqCrashRecover`'s read times out and the
  snippet returns.
- Worth a `nonissues/` entry if the coordinator agrees; I did not run it.

### N3. The WAL's trusted crash laws, and every `diskState` crash, rely on `member/` being durable in the data directory, which etcd never fsyncs; this widens D7 (G-a)

**Where:**
- `wal/Api.lean:54-89` ("Why it is true": records, CRC chain, torn tails; nothing about
  directories);
- `walRecs_crash`/`walWriting_crash` (`:309-324`);
- `nonissues/bbolt-create-dir-not-synced.md`;
- D7.

**The Go.**
- `bootstrap` calls `fileutil.TouchDirAll` on `DataDir` and `MemberDir()` (`bootstrap.go:64,68`).
- `TouchDirAll` (`client/pkg/v3/fileutil/fileutil.go`) is `MkdirAll` and `IsDirWriteable`, which
  writes and removes `.touch`. It does no fsync.
- The server's only directory fsyncs (grep `fileutil.Fsync`/`OpenDir`) are:
  - `wal.Create`'s parent, `member/` (`wal.go:202,225`);
  - the WAL directory's own (`:314,356,879`);
  - `SaveDBFrom`'s (`snap/db.go:126-131`).
- So `member/`'s entry in a data directory that etcd created is never made durable.

**Why it matters.**
- Under POSIX as written, the standard by which G-a says the backend file "may vanish", a crash
  after a first boot may lose all of `member/`: the WAL, the backend, the snapshots.
- `walRecs_crash` then claims a WAL that is not there.
- `ReqCrashRecover` (`NewCluster = true`, one member) would bootstrap a new cluster and reach its
  own `panic("crash-restart: an acknowledged write lost across the crash")`.
- The trusted law is true on ext4 (`data=ordered`) and xfs, where the WAL's fsyncs commit the
  journal holding the earlier `mkdir`s. It does not say that this is what it rests on: the hard
  rule "an assumption states the physical fact the code relies on".

**Two consequences for D7.**
- Option (c), the fork fix "fsync `member/snap` after `OpenBackend` creates the file", does not
  make the disk crash-safe under POSIX. It would also need fsyncs of `DataDir` (after `member/`)
  and of `DataDir`'s parent.
- Option (a) is the consistent choice: the ext4/xfs premise, stated over directory entries in
  general ("an entry is durable once a file under it is fsynced"). It is already what the WAL's
  trusted model assumes, and it also settles G-a.

**`nonissues/bbolt-create-dir-not-synced.md` is wrong on one point.** It says "etcd's data directory
is also created and synced by `fileutil.TouchDirAll`". `TouchDirAll` syncs nothing.

**Fix:**
1. State the premise in the WAL's header and in `ServerStorage.diskOk`'s text, or as an explicit
   environment premise beside `crashInScope`.
2. Put D7 to the user with this wider scope.
3. Correct the nonissue.
4. File the `member/` directory as a nonissue: code reading, the same "not observed on ext4/xfs"
   reason, `blocks-proof: yes` pending D7.

## Second tier

- **s1. Refuting `crashed` at a step.**
  - Every `token ∨ crashed` realization needs a lifting lemma that gives a WP step its state
    interpretation's `notCrashed`. These are raft's starts and `NewServer`'s first step for
    `diskIdle`.
  - `Lifting.lean:752` puts `notCrashed` in the state interpretation. No lemma exposes it: a grep
    for `notCrashed_crashed` use or `crashed -∗ WP` finds nothing.
  - It is distinct from the recorded crash-aware-invariant entry (`perennial-changes.md:2097`).
    Record it there as its own need.
- **s2. `addrFree_protoAt_excl`'s realization text** (`net/http/Api.lean:412-418`).
  - `reserve` is a `|==>` from the fragment `a ↪{1} unset` alone. A `ghost_map` cannot update an
    element without its authority.
  - Use a one-shot per address instead (Iris `one_shot`: `pending` updates to `shot F`, and
    `pending ∗ shot F ⊢ False`).
- **s3. K6 lists only G-a as pending the user.**
  - It should also name D6 (`raftState_crash` is not realizable until `readyBatch`), N1 and N2.
  - It should say that `crashInScope`'s margin excludes at-rest crashes of lagging followers.
- **s4. The per-generation protocols (D4) rest on the whole-program crash model.**
  - The model: every client dies with the generation.
  - Under per-node crashes (Perennial has `DistAdequacy.lean`), clients on surviving nodes would
    hold old-generation facts (`leaseViewLb`), and F3 would come back.
  - The branch's goal is to avoid backtracking, so K6 should say that this choice is tied to the
    whole-program rule.
- **s5. Two texts to fix.** The contradictory texts of N2 (`ApiBoot.lean:214-217` against
  `bootstrap.lean:46-48`), and repair2-crash's "NewServer errs" (N1).

## Snippets

| snippet | result |
|---|---|
| `etcdserverboot/ReqCrashRecover` | **Not provable modulo exactly the recorded gaps.** The restart composes: `disk_crash`, `memberStart_disk` at either kind (the configuration `NewCluster = true` is fine at `.boot` and at `.member id`), `NewServer`, `Start`, `Range`, with `etcdLb_gen`, `envUpd_gen`, `srvNet_gen`, `peerAddr_gen`. It also needs N1 and N2, and, under POSIX, N3. |
| `v3rpc/ReqServe` | Provable. Restart after a stop: `srvEp` and `protoFam` as they are. After a crash: `srvEp_gen`, `protoFam_gen`, then `protoFam_at` at the new generation. |
| `backend/ReqReopen` | Provable. The created file's `none` is in the revert list. The second open uses `boltReopen_alloc`. "No crash" is assumed. |
| `raftnode/ReqRestartDurable` | Provable, with a vacancy from a stop, or from `raftState_gen`/`raftState_crash` in the frame. The latter is subject to D6. |

## Go code

- **No new bug that panics or gives a wrong result in practice.**
- The nonissue's panic is confirmed under POSIX (above).
- N3 is the same kind as `bbolt-create-dir-not-synced.md`: the `member/` directory is not durable
  under POSIX, which is not seen on ext4/xfs. It should be a `nonissues/` entry; it is not filed,
  since I may not write to the repository.
- N2's observation is a possible liveness gap, uncertain.

## Counts

- **Findings rechecked:** 9.
  - F-server-boot F1-F5, G-a, G-b; F-raft-storage F1, F2.
  - 7 resolved. 2 resolved in the statements with a consequence pending (G-a / F2: D7).
  - The open user decisions in the area are listed under "Verdict".
- **Laws checked:** 36. Raft 4; W0 8; 2e 13; 2f 1; net/http 5; WAL 2; snap 3; 4a/4c 8 (some
  counted in two rows above).
- **Not realizable outside the recorded gaps:** `disk_crash` in two windows (N1, N2), and the WAL's
  crash laws under POSIX (N3).
- **New first-tier:** 3 (N1, N2, N3). N1 reverses an earlier assessment, decision 7.
- **Second tier:** 5.
- **Snippets:** 4 checked. 3 provable; `ReqCrashRecover` is not, modulo the recorded gaps alone.

## Ranked by need of revision

1. `Snap.dbFile_rename`/`snapDbs_crash` with 4a's revert list: the joint rename law (N1). Re-tier
   decision 7.
2. The WAL's `wal.Create` window: `walCreating` and its crash law; `bootstrap.lean`/`ApiBoot.lean`
   text (N2).
3. `wal/Api.lean`'s trusted header and the environment premises: the directory-durability
   premise; D7 widened; the nonissue corrected and a new one (N3).
4. `top.md` K6: the gaps of s3 and s4.
5. `net/http/Api.lean`: `addrFree_protoAt_excl`'s realization text (s2);
   `notes/perennial-changes.md`: the step lemma (s1).
