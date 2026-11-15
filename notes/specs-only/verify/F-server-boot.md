# F-server-boot: fresh re-review of the server core, boot and the crash story

Reviewer: fresh and independent, 2026-11-09. Reviewed at `HEAD` = `7394a3ca7e`, diffed against
`41c6c3a39f`. Read-only, apart from this file.

I wrote my verdicts on R-A8 N1-N4 and RR1-RR4 from the specs and the Go code first. Only then did I
read `repair2-crash.md`, `repair2-server-core.md` and `repair3-boot.md`, to check where we disagree.

Go: `.lake/src/server`, `.lake/src/raft`. Perennial: `.lake/packages/perennial/Perennial/GooseLang/CrashAdequacy.lean`
(`goose_crash_adequacy`'s `Hwp`, lines 451-459), `CrashToken.lean`, `Lifting.lean` (fork rules,
lines 1894-2010). OsFs: `GooseLang/Ext/OsFs/Crash.lean` (`crashRest`, line 274).

**Note on the worktree.** During the review, uncommitted edits by another agent appeared in
`api/v3/State.lean`, `ApiBoot.lean`, `ApiReq.lean`, `EtcdServer__leaseTimeToLive.lean` and
`leasehttp/*` (`peerLeaseServed`, `leaseViewLb_zero`). Everything below is about `HEAD`, read with
`git show HEAD:`. Line numbers are `HEAD`'s.

## Verdicts

| batch | verdict | first-tier left |
|---|---|---|
| **crash story** (cross-batch: R1's crash section, W0's `*_gen`, 2e's `disk_crash`, 2f/net/http `*_gen`) | **FAIL** | F1 (raft's crossing laws prove `False` from `raftState ∗ crashed`), F2 (nothing lets the adequacy proof exclude `crashOutOfScope`), F3 (a client address cannot be served after a crash). Recorded gaps: the crash frame's extraction (Perennial), G-a, G-b. |
| **2e** (boot, `NewServer`/`Start`/`start`, storage, WAL, snap, membership, compactor) | **FAIL** | F1's second half (`diskIdle_excl`/`memberDisk_excl` against `disk_crash`), F2, F3, F5 (`srvEp_agree` has no source in net/http's API). RR3, RR4 and R-A8 N3/N4 are resolved in the statements. |
| **2d** (apply side, snapshot) | **FAIL** | G-b (recorded, not a user decision): `applySnapshot` cannot supply `OpenSnapshotBackend`'s closed `beFile` while the old backend is open. F4: `applySnapshot`'s `snapImage` has no source. RR1 and RR2 are resolved. |
| **2f** (rafthttp) | **FAIL** | F4 (`Net.dbIn` names no receiver, and is fixed across generations). R-A8 S3 is resolved. |

`go vet ./specreq/etcdserverboot/ ./specreq/v3rpc/` is clean, and `gofmt -l` prints nothing.

## The findings to recheck

| # | finding | status at `HEAD` | evidence |
|---|---|---|---|
| R-A8 N1 | nothing carries raft/W0/2f vocabulary across a crash; no vacancy source | **Resolved in the statements; the raft part is unrealizable (F1)** | `Raft.global` and `raftState_gen`/`raftState_crash` at `L'` (`raft/v3/Api.lean:930-990`); W0's `etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen`, `envUpd_gen` (`api/v3/State.lean:277-301`); `srvNet_gen` (`ApiBoot.lean:670`); `raftProto_gen`, `peerAddr_gen` (`rafthttp/Api.lean:237,245`); `protoAt_gen`, `addrFree_gen` (`net/http/Api.lean:377,380`). `crashGone_intro` is gone, and the vacancy comes with `raftState`'s crossing. But `raftState_gen` holds at every `L'`, including the crashed generation itself, which yields two vacancies (F1). |
| R-A8 N2 | `crashOutOfScope` was unconstrained | **Partly resolved** | It is now transparent: `∃ R, walRecs (walDirOf ds) R ∗ ⌜¬ R.crashScopeOk⌝` (`ApiBoot.lean:336`). It is **non-vacuous**: the only producers of `walRecs` at `L'` are the trusted `walRecs_crash`/`walWriting_crash` (`wal/Api.lean:279,286`), whose `R'` the prover does not choose. A `.boot`/`.join` disk has no WAL, so it can never take the disjunct. But no statement lets the adequacy proof refute the disjunct, so K6 cannot be proved (F2). |
| R-A8 N3 | the install held the revert state and file across a non-atomic call | **Resolved; one recorded gap remains (G-b)** | The rename's atomic update takes `beFile dst o ∗ revertSt dst os` and leaves `beFile dst (some img) ∗ revertSt dst (o :: os)` in the caller's state (`OpenSnapshotBackend.lean`). `beRevs` is a list (`backend/Api.lean:491`), so two installs before a directory sync are covered. `saveOk`'s second update takes `∃∃ os, … beRevs p os` (`rafthttp/Api.lean:269`). Left over: the old backend is still open at the rename (`server.go:1068` opens the new one, `:1144` closes the old one), so the caller's state holds `beDurInv ∗ beHist`, not the closed `beFile p o` the update takes. Recorded in `EtcdServer__applySnapshot.lean`'s Changes and in K6, but not as a user decision. |
| R-A8 N4 | the idle law could not be proved; crashes outside `[Start, HardStop]` lost the disk | **Resolved in the statements; recorded gaps remain** | There is one `disk_crash` over `diskState ∗ crashed ∗ crashRest` at `|={⊤}=>` (`ApiBoot.lean:683`). `crashGone` and `diskIdle_crash` are deleted. `beFile_crash` covers a closed file (`Durable.lean:162`). `New` and `Close` move the file through `beOpenUpd`/`beCloseUpd` inside `diskAcc`. Gaps: the frame's extraction (`notes/perennial-changes.md:2092`); G-a, a first boot's `member/snap/db` is not durably named after `Close` (`bolt.Open` fsyncs no directory), so `beFile_crash`'s `o' = o` is false there (repair3-boot 7(a), K6). |
| RR1 | apply-side specs without `srvStarted` | **Resolved** | `applySnapshot`, `applyConfChange`, `snapshot`, `compactRaftLog`, `snapshotIfNeededAndCompactRaftLog` and `shouldSnapshotToDisk` take `srvStarted`. Their callers hold it: `applyAll`, `apply`, `applyEntries` and `run` take it. `srvNode_member` (`ApiApply.lean:625`) then gives the transport for `applySnapshot` (`server.go:1157,1166`) and `applyConfChange` (`:2075-2101`). |
| RR2 | getters before `srvMember` | **Resolved** | `Logger`, `MemberID`, `FeatureEnabled`, `RequestTimeout`, `Cluster` and `ClusterVersion` are over `srvFields`, which comes from `srvNode_fields` (`ApiApply.lean:632`) and `srvMember_fields`. `KV.spec` is over `s.kv ↦□ w` (sources: `srvNode_kv`, `isServer_kv`, `srvStores_kv`). `Config` is over `isServer`: it copies the whole `s.Cfg`, which `start` writes (`server.go:556,564`). `Process` (`server.go:701-710`) needs only `srvFields`. In `NewServer`, `Logger`/`FeatureEnabled` at `:343,363,366,387` run on `srvFields`, made after the literal. |
| RR3 | `start` keeps no `threadTok`; compactor `Run` keeps it | **Resolved** | `start.spec` and `Start.spec` take `srvMember ∗ threadTok` and return `threadTok`. `isCompactor_methods`'s `Run`, `Periodic.Run` and `Revision.Run` return it. Both loops are `go func()` (`periodic.go:105`, `revision.go:67`), and `Periodic.Run` reads only settings before its `go`. `go s.run()` and each `GoAttach` goroutine run on their forks' tokens (`wp_fork_tok_body`, `Lifting.lean:1993`). |
| RR4 | `NewServer` takes no `threadTok` | **Resolved** | `NewServer.spec` takes the caller's `threadTok` and returns it on both paths. `NewLessor` returns it (`go l.runLoop()`, `lessor.go:245`), and `lessor.Stop` returns none. None of `mvcc.New`, `NewAuthStore`, `NewTokenProvider`, `Transport.Start`/`AddPeer`/`AddRemote`, `V3compactor.New`, `restoreAlarms`, `newCorruptionChecker`, `SetCheckpointer` or `bootstrap` takes a token. The token balance closes. |

### Where I disagree with the repair reports

- **`repair2-crash.md`, "Each crossing law is not vacuous: it consumes the old generation's exclusive
  resource".** This is true of `disk_crash` and `beFile_crash`, which need OsFs's `crashRest`. It is
  false of raft's `raftState_gen`: it gives back `raftState` at `L' := hG.goose_localGS`, and `crashed`
  is persistent (F1).
- **"W0's adequacy theorem excludes [`crashOutOfScope`] by its environment premise".** No statement
  connects the premise to the logic (F2).
- **`repair3-boot.md` item 2 (`srvEp_reserve` realized by a tag in net/http's map).** net/http's API
  exposes no tag (F5).
- **`v3rpc/serve.go`'s "a restart, after a stop or a crash, reuses both".** False for a crash (F3).

## New first-tier findings

### F1. Raft's crossing laws, instantiated at the crashed generation itself, prove `False` from `raftState ∗ crashed`. 2e's idle exclusivity cannot be realized beside `disk_crash`.

**Where:**
- `raft/v3/Api.lean:956` (`raftState_gen`), `:983` (`raftState_crash`), `:592` (`exclusive`'s
  `nodeVacant` clause);
- `ApiBoot.lean:600,608` (`diskIdle_excl`, `memberDisk_excl`) and `:683` (`disk_crash`);
- the realization texts at `raft/v3/Api.lean:900-907` and `ApiBoot.lean:122`.

**The derivation.**
- `raftState_gen.spec` is `∀ L', raftState γ id D ∗ crashed ⊢ |={⊤}=> raftState@⟨g, L'⟩ γ id D ∗
  nodeVacant@⟨g, L'⟩ γ id`.
- Take `L' := hG.goose_localGS`. `HeapGS` has exactly the two fields `goose_globalGS` and
  `goose_localGS` (`Lifting.lean:707-709`). So `⟨hG.goose_globalGS, hG.goose_localGS⟩` is `hG` by
  structure eta, and the law reads `raftState ∗ crashed ⊢ |={⊤}=> raftState ∗ nodeVacant`.
- `crashed` is `dghostVar crashName .discard ()` (`CrashToken.lean:39`), which is persistent. Apply
  the law twice: `raftState ∗ crashed ⊢ |={⊤}=> raftState ∗ nodeVacant ∗ nodeVacant`.
- `exclusive.spec`'s clause `nodeVacant ∗ nodeVacant ⊢ False` then gives
  `raftState γ id D ∗ crashed ⊢ |={⊤}=> False`.

**Why it matters.**
- The crash frame is exactly where `raftState` and `crashed` meet (`disk_crash`'s realization holds
  `raftState` inside `diskState`). So `disk_crash`, and with it every post-crash guarantee (K6,
  `ReqCrashRecover`), would be provable by ex falso.
- Equivalently, the raft obligations have no realization. The stated one ("a ghost map keyed by
  `(id, generation name)`, an entry inserted once") cannot insert `L`'s entry a second time.
- Perennial's frame is `∀ L'` (`CrashAdequacy.lean:457`) and says nothing about `L'` being fresh,
  so the laws must hold at `L' = L` and at any reused crash name.

**The same issue in 2e, realizability only.**
- `disk_crash` mints `diskIdle@L'`, "keyed by the generation" (`ApiBoot.lean:122`).
- It cannot be iterated: its `crashRest(L, L')` premise is one-shot per file.
- But it must still hold for every `L'`. At an `L'` whose crash name an earlier generation used,
  that name's idle token was already handed out. A realization `own(idle ds (name hG)) ∨
  crashed@hG` would serve, but then `diskIdle_excl`/`memberDisk_excl` fail at a crashed
  generation.

**Fix (pick one):**
- **(a) Local.** Drop the vacancy clause from `Raft.exclusive`, and drop `diskIdle_excl` and
  `memberDisk_excl`. No spec or snippet uses them. Realize the tokens as `own(… name hG) ∨
  crashed@hG`: a node start or `NewServer` refutes the `crashed` case at its first step (the state
  interpretation's `notCrashed`). Say in raft's section that the laws hold at every `L'`, and how.
- **(b) Perennial.** The crash frame gets a one-shot witness of the transition `L → L'` (as OsFs's
  `crashRest` already is for files: it holds the old maps' exclusive `gAuth hL`). Raft's crossing
  laws, and `disk_crash` for `diskIdle`, take it. Record it in `notes/perennial-changes.md`.

### F2. Nothing lets the adequacy proof exclude `crashOutOfScope`, so K6 and `ReqCrashRecover` cannot be proved

**Where:** `ApiBoot.lean:187-196,336,683-692`; `wal/Api.lean:225-239,279-291`; `top.md` K6.

**The gap.**
- `disk_crash` concludes `(diskState@L' ∗ diskIdle@L' ∗ …) ∨ crashOutOfScope@L'`. In the right
  case, the next generation's boot program has no `memberStart`, so it cannot be proved to call
  `NewServer` safely, and `P L'` cannot be produced.
- The header says W0's adequacy theorem excludes the case "by its environment premise over the
  run". But `goose_crash_adequacy` takes `Hstart`/`Hwp` and nothing about runs. The premise
  ("`Open` + `ReadAll` returns records meeting `crashScopeOk`") is about `walRecs`'s trusted
  meaning, which OsFs does not model (`wal/Api.lean:77-81`).
- So it can enter the proof only as a trusted statement, as `ServerStorage.diskOk` does (an opaque
  `Prop` that the trusted crash laws take, `wal/Api.lean:100`). No such statement exists.
- So the disjunct is non-vacuous, but no proof can ever refute it.

**`crashScopeOk` itself is the right condition.** It is stated over what a restart reads, and it
matches R1's `Durable.crashOk`. I checked the snapshot batch's WAL order (`SaveSnap` then `Save`,
`raft.go`): `crashedDuring`'s cases are exactly `crashOk`'s, with the snapshot-record window outside
the scope.

**Fix.**
- Add an opaque environment `Prop` (e.g. `Wal.crashInScope`, or fold it into `diskOk`'s meaning).
- Let `walRecs_crash`/`walWriting_crash` take it and add `⌜R'.crashScopeOk⌝` to their posts
  (trusted: true under the premise).
- Then `disk_crash` takes `⌜crashInScope⌝` and loses the disjunct. Or keep `crashOutOfScope` with a
  law `crashInScope → crashOutOfScope ⊢ False`.
- W0's adequacy statement lists the `Prop` beside `diskOk`, and K6 says so.

### F3. After a crash, no member can serve its client address

**Where:** `ApiBoot.lean:768` (`srvEp_reserve`), `:774` (`srvEp_gen`); `net/http/Api.lean:377`
(`protoAt_gen`); `grpc/Api.lean:350` (`addrAt`); `v3rpc/Api.lean:338,425` (`etcdContract`'s
`leaseFact` over W0's `leaseViewLb`); `examples/specreq/v3rpc/serve.go:13-18`.

**The gap.**
- The address's protocol is fixed once, by `srvEp_reserve`, at `P1 = grpcOver (etcdContract γ ep) P`,
  built at the first generation's `hG1`. The address's `addrFree` is spent.
- `protoAt_gen` carries `protoAt ep P1` to `L'` ("the same `P` on both sides"). The next generation's
  `v3rpc.Server`/`Grpc.start` needs `addrAt ep (etcdContract γ ep)` at `hG2`.
- The two contracts are not equal. `etcdContract`'s lease rows name `leaseViewLb`, and by design
  `leaseViewLb` is per generation: no `leaseViewLb_gen`, "the batch a crash loses may hold applied
  grants" (`ApiBoot.lean:80-81`).
- `grpcOver_inj` (`grpc/Api.lean:810`) says different contracts give different protocols, so
  `addrAt` at `hG2` is not derivable.
- Nor can the second-generation server meet `P1`'s rows. A request carrying `leaseViewLb@hG1 i`
  must be answered from a table `≥ i`, but the restarted lessor recovers from a backend that may
  be behind `i` until the WAL replay catches up.
- `v3rpc/serve.go`'s "a restart, after a stop or a crash, reuses both: `srvEp_gen`,
  `Http.protoAt_gen`" is therefore false for a crash. K3 after a crash is not served.
- `ReqCrashRecover` calls `s.Range` directly, so it is not affected.

**Fix (pick one):**
- **(a)** Make the client address's binding per generation. The environment's `addrFree` is
  re-issued per generation (the clients of the old protocol die with the process). `protoAt_gen` is
  then kept only for protocols built from global vocabulary (`raftProto`); `srvEp_gen` stays.
- **(b)** Index `leaseViewLb` (and the contract's rows) by an incarnation that the crash advances,
  so that the old rows are about a dead incarnation and hold trivially.

Option (a) is closer to the physical fact. It is the user's choice, being a change to W0's and
net/http's environment.

### F4. `Net.dbIn` names no receiver, so `Process` cannot record "the image is in *my* directory"

**Where:** `rafthttp/Api.lean:160-164` (`Net`), `:252` (`recvd`), `:269` (`saveOk`);
`EtcdServer__Process.lean` (sketch: "which `Process` deposits in the member's invariant over its
snapshot directory"); `EtcdServer__applySnapshot.lean` (`snapImage`'s source).

**The gap.**
- `ν` is one per cluster (`srvNet_agree`). `dbIn : w64 → IProp` takes only the index.
- Member X's snapshot handler commits `saveOk ν sd_X`'s update, which gives `ν.dbIn i`, and passes
  it in `recvd ν m` to X's `Process`.
- Whatever `ν.dbIn i` means is the same for every member. It can say "some member's directory holds
  a file of index `i`", but not "X's does".
- Yet `applySnapshot`'s `OpenSnapshotBackend` reads X's own snapshot directory and panics on an
  error (`server.go:1068-1070`), so `snapImage` needs exactly that fact.
- `raftOk`'s `Process` accepts a `recvd` from any caller, so the logic cannot use the fact that only
  X's handler delivers a `MsgSnap` to X.

**Across a crash.** `srvNet_gen` keeps the same `ν` at every generation, while the snapshot
directory's invariant is "keyed per generation" (`ApiBoot.lean:179-181`). So a `dbIn` that names that
invariant would name the dead generation's.

**History and fix.** Unchanged since before `41c6c3a39f`, and not raised by R-A8. **Fix:**
`dbIn : w64 → w64 → IProp GF` (receiver id and index). `saveOk ν lid sd` gives `ν.dbIn lid i`, and
`recvd` takes `ν.dbIn m.to s.index`. The server realizes it over a generation-independent
per-directory record (the directory's ghost history, a global lower bound), not over the
per-generation invariant.

### F5. `srvEp_agree` has no source in net/http's API

**Where:** `ApiBoot.lean:756-772`; `net/http/Api.lean:191-196,367-381`.

**The gap.**
- The realization says that net/http's global map "keeps beside the protocol the reserver's saved
  tag `(γ, id)`". net/http is a trusted boundary whose API has `reserve` (`addrFree a ⊢ |==> protoAt
  a P`), and no tag, no `protoAt` agreement (withdrawn, `grpc/Api.lean:807`), and no law refuting
  `addrFree a ∗ protoAt a P`.
- 2e's own ghost map cannot help. To insert `ep` it must know `ep` was never reserved, and the
  earlier reservation consumed the earlier `addrFree ep`.

**Fix.** A one-line trusted law of net/http, true of its set-once map: `addrFree_protoAt_excl :
addrFree a ∗ protoAt a P ⊢ False`. 2e then keeps its own map `ep ↦ (γ, id)` with a `protoAt ep _`
per entry.

### Recorded gaps, still open and not user decisions

- **G-a (`Durable.lean:162`, `beFile_crash`; repair3-boot 7(a)).** After a first boot's `Close`,
  `beFile p (some I)` claims a durably named file, but `bolt.Open` created it with no directory
  fsync. A crash may then lose it, and Go recovers by replaying the WAL from index 0. As stated, the
  law is false at that point.
  Fix: `beCloseUpd` gives `beFile p (some I)` only for a durable name, and gives a "maybe absent"
  form otherwise (the same `Image.empty ∈ L` case as `beCrash`).
- **G-b (`EtcdServer__applySnapshot.lean`, Changes).** At the rename the old backend is still open,
  so the AU's closed `beFile p o` cannot be supplied. `applySnapshot` does not close at all, even
  without a crash.
- **The crash frame's extraction of `diskState`** (`notes/perennial-changes.md:2092`). This is the
  Perennial gap; it is recorded.

## Regressions: files changed since `41c6c3a39f`

59 spec and snippet files in the area changed (`git diff --stat 41c6c3a39f`). I checked them as
follows.

**Against the Go and the callees:**
- `ApiBoot` (crash laws, `srvFields`, `srvEp`/`srvAt`, `leaseURLOf_intro`, `cluster_alloc`/
  `urls_reserve`/`soleMember_intro`);
- `NewServer`, `Start`, `start`;
- the getters;
- `KV`, `Watchable`, `NewUberApplier`, `Process`;
- the seven apply-side specs;
- `v3compactor/Api` and both `Run`s;
- `NewLessor`/`lessor.Stop`;
- `OpenSnapshotBackend`, `snap/Api` (`revertSt`, `dbFile_rename`), `storage/Api` (`diskOk`), `wal/Api`
  (the crash laws, `crashScopeOk`);
- `Durable.lean`'s crash laws;
- raft's crash section, W0's `*_gen`, net/http's `*_gen`, rafthttp's `*_gen` and `saveOk`;
- `msgAppV2Encoder` (S3: `msgWf`'s consecutive indexes, `raftpb/Model.lean:356`).

**By diff only (text or mechanical):**
- `Cluster`, `ClusterVersion`, `Config`;
- `bootstrapped*.Close` (`beCloseUpd`), `bootstrap`, `newCorruptionChecker`, `OpenBackend`;
- `snapshotHandler.ServeHTTP`'s sketch;
- the `Lease*` request specs and `leaseTimeToLive`. These are 2c's: read for statements only, and
  checked as uncertain.

**False of the code:** none beyond G-a.

**Inconsistent:** F1.

**Vacuous:** none. `crashOutOfScope` is no longer vacuous.

**Does not close:** F2 (K6), F3 (serving after a crash), F4 (`applySnapshot`'s `snapImage`), F5
(`srvEp_agree`), G-b.

### Realizability of each generation-crossing law

- **`etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen`, `srvNet_gen`,
  `srvEp_gen`, `protoAt_gen`, `addrFree_gen`:** plausible as `own`s and invariants of the global ghost
  state. Each is a `⊣⊢`, so iterating one mints nothing.
- **`envUpd_gen`:** follows from `etcdState_gen` (the AU's masks are global invariants).
- **`Raft.global`:** plausible.
- **`raftProto_gen`:** an equality of `Proto` values, which `Raft.global`'s `⊣⊢` does not give. It is
  realizable only if `raftProto`'s body ignores the local state, e.g. raft's predicates taken at a
  canonical local state. Say so in its realization (second tier).
- **`peerAddr_gen`:** follows from `protoAt_gen` and `raftProto_gen`.
- **`walRecs_crash`, `walWriting_crash`:** trusted. At `L' = L` they are one-for-one, so harmless.
- **`beCrash`, `beFile_crash`, `dataDirFresh_crash`:** guarded by `crashRest`, which is one-shot per
  file. `beFile_crash` is false at G-a.
- **`memberBoot_crash`, `memberJoin_crash`:** one-for-one, realized through `raftState_gen`, so they
  inherit F1.
- **`raftState_gen`, `raftState_crash`:** F1.
- **`disk_crash`:** a composition of the above, plus F1's second half and F2.

### `srvEp`'s one-member-per-address premise

- The premise is sound as a scope restriction: one member id per client address over the run,
  recorded (repair3-boot, New decisions 2). It rests on net/http's physical premise (`addrFree` once
  per socket and run, `net/http/Api.lean:30-35`).
- Its realization needs F5.
- The restriction is stricter than physics after a crash (F3).

### Thread tokens

They balance through `NewServer` → `start`/`Start` → the compactor's `Run` → the lessor's
`NewLessor`/`Stop` (see RR3 and RR4).

## Snippets (`examples/specreq/etcdserverboot/boot.go`, `v3rpc/serve.go`)

| snippet | result |
|---|---|
| `ReqStartOne`, `ReqStartThree`, `ReqRestart` | Provable against the statements (`NewServer`'s and `Start`'s tokens returned; `srvMember` for `Start` and `MemberID`; `memberDisk` to `memberStart_disk` at `.member id`). |
| `ReqJoin`, `ReqPartition`, `ReqReadyOrStop`, `ReqMemberListAfterAdd`, `ReqGetters`, `ReqStopAfterError`, `ReqCleanupBeforeStart`, `ReqStopDrained` | Unchanged; provable. `ReqGetters`' `Config` is now over `isServer`, which `Assumes: s was started` gives. |
| `ReqCrashRecover` | **Not provable:** F1 (the frame can derive `False`), F2 (the out-of-scope disjunct), G-a/G-b (crashes after a first boot's close and around an install), and the recorded frame-extraction gap. Second tier: its Assumes lacks "no later delete or overwrite of `k`" (`ReqRestart` has "no other writer of k"). Otherwise the restart composes: `memberStart_disk` at either kind `disk_crash` leaves (same configuration), `envUpd_gen`, `etcdLb_gen` + `etcdLb_reach` for the read's ticket. |
| `v3rpc/ReqServe` | Its "or a crash" restart claim fails (F3); the stop-and-restart case is fine. |

## `top.md` K6

The text matches the laws, but:
- it still says "(no crash transition in the model)" beside "After a crash too";
- its recorded gaps omit F1, F2 and F3;
- open question 2.8's verify-round line still says "`crashOutOfScope γ ds` (… or a snapshot batch
  interrupted)". The scope is now only the snapshot-record window, and `γ` is gone.

## Second tier

- S1 (R-A8): still open (recorded, decision 7).
- S5: `storage/Api.lean:98,106` still declare the superseded `beOpen`/`beTx`.
- The `srvNode` docstring (`ApiApply.lean:276-278`) and `srvNode_raftOk`/`srvNode_member` say
  `srvNode` holds "from its server literal on". `srvNode_kv` (`s.kv ↦□`, written at
  `server.go:366`) forces it after `mvcc.New`, as `NewServer`'s sketch says (after
  `restoreAlarms`). Fix the text.
- `raftProto_gen`'s realization (above).
- K6, 2.8 and `ReqCrashRecover`'s Assumes (above).
- `storage/Api.lean`'s `diskOk` excludes a torn tail with no zeroed sector. That is fine as the
  physical sector-atomicity premise, but say that this is what it is.

## Bugs in the Go code

None found. F1-F5 are bugs in this repository's specs. They belong in `notes/`, not in `issues/`.

## Counts

- **Findings rechecked:** 8.
  - R-A8: N1 resolved in the statements but unrealizable (F1); N2 partly resolved (F2); N3 resolved
    with recorded gap G-b; N4 resolved with recorded gaps (G-a, extraction).
  - RR-server-core: RR1, RR2, RR3 and RR4 resolved.
- **New first-tier:** 5 (F1-F5). F4 predates `41c6c3a39f`.
- **Recorded gaps still blocking:** 3 (G-a, G-b, the frame extraction).
- **Second tier:** 7.
- **Spec files:** 59 changed files in the area. About 40 checked against the Go or their callees, 19
  by diff. About 30 unchanged callers and callees read beside them (raft's crash section, W0
  `State`, net/http, `Durable`, grpc `addrAt`, the `v3rpc` contract).
- **Snippets:** 12 checked. 10 provable, 1 not provable (`ReqCrashRecover`), 1 provable except its
  crash claim (`ReqServe`).
