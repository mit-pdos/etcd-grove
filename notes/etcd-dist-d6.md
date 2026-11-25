# etcd-dist D6: a member machine that crashes and restarts (spec phase, 2026-11-24)

Branch `etcd-safe-d6/2026-11-24`. Plan: `notes/etcd-dist-plan.md` §12 "D6". The member machine runs
`server.MainDeployment(d, i)` (`examples/etcd/dist/server/server.go`, `MainLogger`): `NewServer(cfg)`, then
the peer handler, `Start`, `ReadyNotify`, gRPC. After a crash (`OsCrash`: a power loss, or a kill followed
by `sync`; `notes/restart-vs-crash.md` explains why a kill without `sync` is outside the model) the same
program runs again; `bootstrap` takes the restart branch when the WAL exists (`haveWAL`,
`bootstrap.go:77`).

Lean written in this phase (statements and definitions only; no proof, no axiom, no `sorry`; all three built on the VM, 2026-11-24):

| file | tier | what |
|---|---|---|
| `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvCrashImage.lean` | defs | `wal.crashImage`, `srvCrashImageAt`, `srvCrashImage`, `bootstrapCrashContract` |
| `Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServerCrash.lean` | spec | `NewServer.specC` |
| `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/crash/MemberGen.lean` | defs | `MemberCl`, `memberFirst`, `memberRestart`, `memberGen`, `atCtx`, `memberPc`, `memberGen_crash.law`, `raftTorn`, `readyCrashTorn.law` |

## 0. Findings that shape D6

1. **A torn WAL `Save` breaks raft's safety, and the model admits it.** `WAL.Save` writes the entry
   records, then the state record (`wal.go:1122-1129` at the WAL fork `8c28a4296`), and the model's crash
   image of a WAL keeps "the first `k` entry records of operation `j` when it is a `Save` (its state record,
   written last, lost)" (`walImg`, `GooseLang/Ext/AbsDisk/Impl.lean:115`). Raft's durable-state model calls
   such a state unsafe (`RaftState.wcommit`'s docstring, `Protocol/RaftState.lean:40-46`: a commit below
   `wcommit` may count a superseded conf change as pending), and `issues/raft-commit-lost-with-entries-kept.md`
   is the failing test (two conf changes in one torn batch: two leaders commit different entries at one
   index). So raft's crash law needs a third case beside `readyCrashEnter`/`nodeCrash`, the torn batch,
   and it holds only when the kept prefix has no conf-change entry (`readyCrashTorn.law`). In a static
   cluster (no workload of `etcd_safe` changes membership: `Workload`, `TopLevelDefs.lean:95-118`) the only
   batch with conf changes is each member's **first** `Ready` (raft's `Bootstrap` appends the bootstrap
   log and commits it in memory). *Inference, not tested:* a member whose first `Save` is torn restarts
   with the bootstrap conf changes in its log above commit `0`; a heartbeat carrying `min(Match, committed)`
   can then commit a prefix of them, leaving it a voter in a partial configuration (e.g. `{self}`). That is
   the bootstrap instance of the existing issue; a test should decide it before it gets a `nonissues/` or
   `issues/` file. `issues/raft-commit-lost-with-entries-kept.md` says `blocks-proof: no`: for D6 it blocks
   (Q1).
2. **The backend can be ahead of the WAL after a crash.** The apply thread commits the backend (synced)
   while the raft loop's commit-only `Save`s are not synced (`wal.go:1119`, `MustSync`;
   `restart-vs-crash.md` Q1(c)). The graceful image's `i ≤ σ.commit` (`wal.stopImage`, `WalApi.lean:606-611`,
   and the premise of `bootstrapRestartContract`, `InvRestart.lean:696-718`) is false of crash images.
   `srvCrashImageAt` drops it; `NewServer.specC`'s proof must handle the replay of entries at or below
   the consistent index (the apply thread skips them).
3. **A crash during the first boot leaves leftovers.** `bootstrap` opens the backend (`bootstrapBackend`,
   `bootstrap.go:78`, `OpenBackend` creates the file and writes the meta bucket) before it creates the WAL
   (`bootstrapStorage` → `bootstrapNewWAL`). A crash in between restarts on the fresh path
   (`haveWAL` false) with a backend file present (`beExist`, `bootstrap.go:256`; `schema.Validate` runs on
   it) and possibly `wal.tmp` (removed by `Create`) and the snapshot directory. `NewServer.specG` takes
   `wal.bootRes cfg` (the area fresh) and `bootstrapContract` a fresh directory: both must accept such
   leftovers (task T3). The raft side is fine: no `Ready` was saved, so the durable state is still
   `RaftState.init`, and `nodeBoot` is persistent (`InvNodeRule.lean:181-187`).
4. **The crash premise must imply `W1`.** `walInv_crash` takes `Q st st' → W1 C st st'`
   (`storage/wal/Crash.lean:256-257`); `etcdFsSem` has `Q := True` (`etcdstart/FsExts.lean:62`), and
   `Net/Statement/NetFsBridge.lean`'s `CrashBootWp` hard-wires `fun _ _ => True` (`:115`). D4a/D4c must give
   member machines a crash premise with `W1 walCodec` (the WAL tester's `tQ`,
   `WalTester/.../wal/Adequacy.lean:60`), and, once real bbolt has a crash proof, bbolt's `P1` analogue.
   `W1` is a world premise pending the owner's review (`W1.lean`'s header).

## 1. The per-generation predicate (`memberGen`)

`memberGen C cfg id` (`MemberGen.lean`) is what generation `L` of member `id` starts `NewServer(cfg)` from:

* **Global, persistent, heap-free**: `etcdstart.clusterFacts C.γ C.γk issued cnt wn fs gen`
  (`etcdstart/AllocN.lean:196`: `srvRaftLogInv`, `idClusterInv`, the reserved id 0, `srvPropMint`,
  `srvRdCtxInv`, `kvInv`), allocated once by `clusterAllocN` (`:230`).
* **First generation** (`memberFirst`): D7's `memberSlice` (`AllocN.lean:212`: the prefix's key
  `(pfx, 0)`, `nodeBootG`, `raftState … RaftState.init`, `nodeVacant`, the snapshot directory's map, the
  wait slot, fresh store names, `idPfxTok`) and `wal.bootRes cfg` (from the file extension's start
  resources: `fsStartRes`, `NetFsBridge.lean:63`). `memberBoot_of_slice` (`AllocN.lean:304`, adds
  `bootMarshal`, which is per-heap and comes from the program's package initialization) gives
  `NewServer.specG`'s rows.
* **Later generations** (`memberRestart`): `etcdstart.memberRestartFacts γ' ρo id` (persistent,
  `etcdstart/Restart.lean:87`: the same cluster facts at the old incarnation's names `ρo`, `idPfxInv`, a
  registered key) and `srvCrashImage γ' ρo id dd` (`InvCrashImage.lean`). The durable ghost state is the
  image's: `raftState γ.cl id S` and `nodeVacant` (exclusive, global, survive the crash inside the run's
  crash invariant, as kvnet's `kdFileInvK`), the committed-log lower bound `srvRLogLb`, the backend's
  image facts (`imageRestAt`, `imageStOk`, `mvccImage`), the membership at `i` (`confAt`), the WAL's slot
  (`wal.crashImage`: `StorageHolds S σ`, `walReadFacts σ`, `σ.b ≤ i`, the snapshot certificate), the
  files (`srvFiles dd id σ D`, at the new generation) and the snapshot directory's invariant (at the new
  generation).
* **Rebuilt from the crash frame** (`memberGen_crash.law`, kvnet's `kvGen_crash`,
  `KvNet/.../kvnet/TopBoot.lean:135`): from the run's `Keep`, `£ 1`, `crashed`, `Fs.crashRest Q …` and
  `Fs.osInv (L := L')`: open the run's durability invariant with its token (raft's state `S` and the
  WAL/backend ghost records), run `walInv_crash` (`Crash.lean:256`) and `walBootCrash`
  (`BootCrash.lean:320`; `BootFo` from `bootFo_of`, `HistFo.lean`), the backend's crash (interim axiom A1
  below), the snapshot directory's crash, `crashRest_treeWf`/`crashRest_treeS`; choose raft's case by
  what the WAL image kept (enter / discard / torn: `readyCrashEnter`, `nodeCrash` `InvNodeRule.lean:745`,
  `readyCrashTorn.law`); turn the new generation's WAL resources into `walFiles` (all synced: a new
  generation starts with every byte durable) and the backend's into `fileHolds`, i.e. `srvFiles`.
  `memberPc` (`kvPc`'s shape) is the predicate `CrashBootWp` is stated at, once D4c generalizes it.

## 2. `NewServer` from any reachable file state

**Proposal: one restart spec, `NewServer.specC`** (`NewServerCrash.lean`): `NewServer.specR`
(`NewServerR.lean`, graceful) with `srvDiskImageAt` → `srvCrashImageAt` and `bootstrapRestartContract` →
`bootstrapCrashContract`; the post unchanged. The crash image differs from the graceful one in four rows
(`InvCrashImage.lean`'s header): no `i ≤ σ.commit`; `walReadFacts σ` carried (so the contract no longer
trusts it: this retires the trusted I1-I4 promise for crash restarts once C6's `walReadCut_*` lemmas give
it from the WAL's crash image); the vacancy unarmed; any registry. The graceful image is an instance
(`srvDiskImageAt ⊢ srvCrashImageAt` up to `walReadFacts`), so `specR` can be derived from `specC` and
retired. A first start stays `NewServer.specG` (Go takes the other branch and the post differs:
`srvBuiltG`, `leaseTTLRowR`), generalized for leftovers (finding 3); the member's program reaches one
or the other through `memberGen`'s disjunction, decided by the files.

Callee facts it needs that do not exist:

| fact | status | plan |
|---|---|---|
| `bootstrapCrashContract` | premise (as `bootstrapRestartContract` today) | #34 stage 5 proves the restart branch: ask it to prove `bootstrapCrashContract` (the generalization costs `recoverSnapshot`'s `beExist`/`ci` cases, which Go has) and derive the graceful one |
| `bootstrapContract` / `wal.bootRes` with first-boot leftovers | not stated | T3: weaken `wal.bootRes` to "no WAL, possibly `wal.tmp`" and the backend path to "absent or holding only what `bootstrapBackend` writes"; `schema.Validate` on such a file |
| `srvFiles` from the crash frame | missing | T5: `walInv_crash` + `walBootCrash` (proved, WAL tester) → `walFiles` at the new generation; needs a lemma "a new generation's `walDiskAt` is all synced" (`walSyncedLb d.H.length` from `fileStart`) |
| `walReadFacts σ` of a crash image | missing (C6) | T5: from `walImg` and the history invariant (`walReadCut_wf`, `_last_le`, `_b_le_commit`, `_snapAtBase`; `notes/wal-crash-handoff/restart-wal-interface.md` §2) |
| bbolt file after a power loss | **no proof for real bbolt** (only minibolt: `osfs/bboltfs/DBCrash.lean`, `BootP1.lean`) | interim axiom A1 |
| `storage.OpenBackend` on a crashed file | axiom today (`storage/OpenBackend.lean:64`), but its pre is the concrete `fileHolds` (S5, sound in the strict sense): **no new axiom needed** once A1 gives `fileHolds path D'` at the new generation | — |
| snapshot directory's invariant after a crash (`snapDirInv`) | missing | T6: a crash lemma for `snapDirInv` (renames into `snap/`, `.snap.db` files; `SaveDBFrom`'s directory sync, `snap/db.go:57-64`) |
| `NewServer.specC`'s replay below the consistent index | missing | T4 (the restart invariant, §4) |

## 3. Raft's durability across a crash

**What exists.** Raft's API already has the crash law (2026-11-21/22, `notes/raft-crash-law-design.md`,
route 1): `raftState γ id S` (the durable state, exclusive, `InvNode.lean:733`), `nodeVacant`/
`nodeVacantA`/`nodeCrashTok`/`nodeArm` (`:738-764`), `readyEnter` = live half ∧ crash half
(`readyEnterLive`, `readyEnterCrash`, `:1100-1128`), `readyCrashEnter` (`:1130`), `nodeCrash`
(`InvNodeRule.lean:745`). The storage contract is about `MemoryStorage` (`isNode`'s storage key,
`nodeCommitLb`, `nodeAppliedLb`); raft's proof never sees the WAL. `StorageHolds S σ`
(`NodeApiVocab.lean:136`) says which records restart a node at `S`: same term and vote, the log from the
base, and a stored commit anywhere in `[wcommit, commit]` (so unsynced commit-only `Save`s are covered).

**What connects raft to the WAL in the server.** `rnDurInv` (`InvWal.lean`, R2b-1): an invariant holding
the loop's view and `walAsViewed` (the WAL's records `walRecs` with `ViewOk`: `StorageHolds` of the
durable state); `raftState` is the loop's (`rnDrv`, `InvRaftNode.lean:609`), entered after the `Save`
(`rnPendEnter`). For crashes it must become kvnet's pattern (`kdFileInvK`/`kdFileState`,
`KvNet/.../kvnet/BootLemmas.lean:50` `kd_boot_choose`): one invariant per generation holding
`raftState S`, raft's crash token and the WAL's durable ghost record, or `crashed ∗ token`. Its body, per
WAL state: (a) idle: the synced records hold `S`; (b) between `Save`'s writes and `enter`: the records
hold `S'` once synced; before, any `walImg` of the history at the synced mark, which is `S` (nothing
kept), `S'` (all kept) or `raftTorn S es k` (entries kept, state record lost). The crash then picks
`nodeCrash` / `readyCrashEnter` / `readyCrashTorn` (D6.3). Raft v3.7's leader self-ack after persistence
(`raft.go:851-857`) and etcd's `Advance` after `Save` (`etcdserver/raft.go`) are why no acknowledged
entry is outside the synced records: the existing `readyEnter` discipline already encodes that
(messages leave after the enter, `readyLeaderMsgs` only at role leader).

**kvnet's storage** (`KdStorage*.lean`, `PersistLemmas.lean`) writes one file atomically (`durable`'s
rename), so it never needed the torn case; etcd's WAL does.

**The gap** is `readyCrashTorn.law` (`MemberGen.lean`), with the premise "no conf-change entry in the
kept prefix", proved inside raft's protocol (`raft_crash` of the design note, with the log edited:
`appendEnts` of a prefix; the safety argument: a torn prefix adds no conf change above `wcommit`, so
`ConfI1` (`Protocol/StepC.lean:177`) is kept, and the entries are the batch's, a leader's at their
terms; term and vote regress only to their synced values). The first `Ready` (bootstrap conf changes)
is excluded by the premise: Q1.

## 4. The restart invariant

Graceful: `InvRestart.lean` (`srvDiskImageAt`, `restartNames`, `bootOkR`), `notes/restart-plan.md`,
`BuiltRestart.lean` (`srvBuiltR`). For a crash, the member's local invariants are rebuilt by
`NewServer.specC` from the image and the global facts as in the graceful restart, with three crash-only
obligations (crash hazards: `notes/restart-vs-crash.md`, which under the "restart = crash after sync"
assumption excludes P1-P9):
1. **Replay below the consistent index**: raft restarts at the WAL's commit `σ.commit`, possibly below `i`;
   the apply thread must skip entries `≤ i` (`applyEntryNormal`'s `index <= ci`) and the restarted
   `srvBuiltR` is at `restartKV ρ.rd.kv A` with `|A|` reaching `i`, not `σ.commit`. Today's restart proof
   assumes `i ≤ σ.commit` (`wal.restartOk_start`).
2. **The backend's received-snapshot case** (`RecoverSnapshotBackend`, `storage/backend.go:106-121`): a
   WAL snapshot above the backend's index with a `.snap.db` present. `wal.crashImage` keeps `σ.b ≤ i`; a
   crash inside a received snapshot's install can violate it (Q3).
3. **`ReadyNotify`** (`server.go`'s TODO): serving clients only after the restarted member applied its own
   publish entry. Not needed for safety (a member that serves earlier answers linearizably through
   read-index), only for the program's comment; leave out of D6.

## 5. The request-id generator after a crash

Requirement on the issue record (D4b designs it): **an id issued by any incarnation of member `id`
before a crash is never issued again by a later incarnation** (the cluster's claims map `issued`
keeps every claim forever: `idClusterInv`, `idutil/Defs.lean:543`). The ghost side is ready:
`idPfxInv gen p` is persistent and global (`:588`), so it survives; `idIncarnation_alloc` (`:1011`) gives
a fresh key `(p, inc)` from `idClusterInv` alone; `memberRestartFacts_alloc` (`etcdstart/Restart.lean:227`)
builds the new incarnation's names. What is missing is only the trusted side: today `IdIssueState`
survives a crash unchanged and has no crash interpretation (`IdIssue/Impl.lean:40,77`;
`nonissues/etcd-request-id-restart-reuse.md`: Go's clock-seeded counter can reuse ids across restarts,
so the record must exclude reissue, as the plan's D4b says). D6 needs from D4b: a crash interpretation
that keeps the issued ids, with `idIssueFragD id g` facts of dead generators still refuting a reissue.

## 6. Proof tasks

Sizes are rough Lean lines. "Now" = can start on this branch's statements.

| task | files | size | depends on | start |
|---|---|---|---|---|
| T1 raft torn law: `readyCrashTorn_law_holds` | `Proof/go_etcd_io/raft/v3/` (`Protocol/Enter.lean`'s `raft_crash` + a torn variant; `InvNode.lean` law) | 600-1200 | Q1's decision only for the bootstrap batch | now |
| T2 the server's crash-aware durability invariant: `rnDurInv` → per-generation invariant with raft's crash token, the WAL's synced/named records and the batch-phase cases; `rn_enter` under `notCrashed` | `etcdserver/InvWal.lean`, `InvRaftNode.lean`, `EtcdServer__run.lean`, `raftNode__start*` | 1500-3000 | T1's statement | now |
| T3 first start with leftovers: `wal.bootRes` weakened, `bootstrapContract`'s fresh case over an existing backend file | `WalApi.lean`, `InvBoot.lean`, `NewServer.lean` (spec text), #34 | 400-800 + #34 | owner sign-off (spec change) | after sign-off |
| T4 `NewServer.wp_proofC` (from `NewServer.wp_proofR`): crash image, replay below `ci` | `Proof/.../etcdserver/NewServerC.lean`, `BuiltRestart.lean` | 1500-2500 | `bootstrapCrashContract` premise | now |
| T5 WAL crash → `srvFiles` and `walReadFacts` | `storage/wal/` (new `SrvCrash.lean`), `WalRecs.lean` | 800-1500 | none | now |
| T6 snapshot directory crash lemma | `etcdserver/api/snap/` | 300-600 | none | now |
| T7 `memberGen_crash_law_holds` (assembly of T1, T2, T5, T6, A1) and `memberGen` first | `dist/crash/MemberCrash.lean` | 600-1000 | T2, T5, T6 statements | after T2's statement |
| T8 the member machine's `CrashBootWp` (program: `serverProg d i`) | `dist/crash/MemberBoot.lean` | 300-600 | D2 translation of `dist/server`, D4c | later |
| T9 #34 stage 5 generalized to `bootstrapCrashContract` | #34's files | +300 over stage 5 | #34 | with #34 |

## 7. Interim axioms proposed (none added in this phase; each needs the owner)

* **A1. bbolt's file after a power loss** (retired by bbolt's crash proof over `fsExt`, starting from
  `osfs/bboltfs`). At the backend's interface: each successful `backend` commit gives a persistent
  durable record `backend.dbDurLb γB D` (the committed data `D` is synced: etcd's backend commits with
  `fdatasync`, bbolt's `tx.Commit` writes pages, syncs, writes the meta, syncs); the crash law:
  `backend.dbCrashKeep γB path -∗ crashed -∗ Fs.crashRest Q … V' ={E}=∗ ∃ D', ⌜D' = D_last ∨ D' = D_next⌝ ∗
  backend.fileHolds (L := L') path D'` where `D_last` is the last committed data whose commit returned
  and `D_next` the one in flight. Sound because bbolt's meta-page switch is atomic under its checksum
  (its `P1`, `BootP1.lean`, measured for minibolt) and etcd commits every batch with a sync; the known
  restart hazard (`nonissues/bbolt-restart-reuses-pages-of-unsynced-commit.md`) needs a kill without
  `sync`, outside the model. `nonissues/bbolt-init-not-crash-safe.md` (a crash inside the first
  `init`) must be refuted or the axiom restricted to files past `init`; review with the `axiom` skill.
* **A2 (only if Q1 is answered "assume")**: no torn first batch, i.e. `readyCrashTorn.law` for the
  bootstrap batch. Not recommended: it is false of Go (finding 1); the fork fix of Q1 is.
* `bootstrapCrashContract` stays a premise of `NewServer.specC` (as today's contracts), retired by T9.

## 8. Open questions (for the lead / owner)

* **Q1 (the torn bootstrap batch; decided (a), the Go side done: §10)**: (a) fix the fork so that `Save` is atomic across a
  crash: always end a `Save` with a state record, and have `ReadAll` drop entry records after the last
  state record (they belong to an unfinished `Save`; nothing was acknowledged from them, since
  messages leave after `Save` returns); the WAL's `walImg`/`walRead` then read a torn `Save` as none, and
  T1 is not needed; (b) prove T1 and add a test-backed `issues/` entry for the bootstrap variant, with a
  premise excluding it; (c) restrict the theorem. (a) is a Go change with its own `issues/` report.
* **Q2**: `W1` becomes a premise of every member machine's crash (finding 4); it is pending review.
* **Q3**: the received-snapshot crash window (`σ.b > i` with a `.snap.db`): extend `wal.crashImage` or
  show etcd's order (`SaveDBFrom` synced before `SaveSnap`) excludes it.
* **Q4**: the storage registry across a crash. `ρ.rd.raft` names the registry (`SrvRaft.reg`), and
  `restartNames` keeps it; a crash's new heap needs a fresh registry (or a proof that a registry naming
  dead locations is harmless). `memberRestart` leaves the registry name free (`γ' = {C.γ with reg := r}`);
  T4 decides.
* **Q5**: D4b's crash interpretation (§5).

## 9. T1's result (2026-11-24, branch `etcd-safe-d6t1/2026-11-24`)

**Go.** `issues/raft-bootstrap-entries-kept-small-appends/bootstrap_torn_test.go` (copied into the raft
module root): 1, 3 and 5 members bootstrapped as etcd does (`NewRawNode` + `Bootstrap(peers)` on an
empty `MemoryStorage`), etcd's `raftConfig` (PreVote, CheckQuorum, `MaxSizePerMsg` 1 MiB,
`MaxInflightMsgs` 512), each `Ready` handled as doc.go says; member 1's first `Ready` torn at a random
prefix (entries kept, `HardState` and the rest dropped), restart with `NewRawNode` from its storage;
300 random schedules each (ticks, deliveries, drops, partitions, campaigns, proposals).
`TestBootstrapTornFirstReady` and `TestBootstrapTornAnyReady` (the latter: every member may also crash
before, after or in the middle of any later `Ready`) **pass** at the verified fork d2c16c5, upstream
`main` ae830f4 and v3.7.0: no index committed twice; member 1 rejoins as a voter of the whole
configuration once healed, unless every member lost its bootstrap `Ready` (always, for one member: a
single-member cluster whose bootstrap `Save` is torn never elects again; liveness). Measured in
`TestBootstrapTornAnyReady`: 47 torn **later** batches held bootstrap conf entries (a member whose first
`Save` was torn gets the rest of the bootstrap log in a later batch), and 13 torn batches kept entries
above a nonzero stored term; both are outside the premise the lead chose, and both were safe.

With `MaxSizePerMsg` 1 the same setting is **unsafe**: `TestRestartWithPartOfBootstrapEntries` (3
members, two keep only index 1 of their bootstrap batch) commits two entries at index 3: a member that
lost its bootstrap `HardState` commits the bootstrap log one entry per append, applies a prefix of the
bootstrap conf changes, and elects itself in that prefix's configuration. Recorded as
`issues/raft-bootstrap-entries-kept-small-appends.md` (`blocks-proof: no`: etcd's 1 MiB covers its
bootstrap log). So "a torn bootstrap batch is harmless" holds for etcd only because an append carries the
whole bootstrap log, a fact about `MaxSizePerMsg` and the peers' contexts that raft's proof never uses.

**Lean: `readyCrashTorn.law` is not provable as stated** (by reading the definitions; no proof attempted):

1. *The bootstrap disjunct.* `raftState`'s body (`ownDurGhost`, `Protocol/GhostState.lean:3119`) carries
   `durI1 γ S S.wcommit` (`:3048`): in a dynamic cluster (every node-API cluster with a `confAt`, so
   etcd's: `RestartNode.lean:406`) no two conf entries of the log lie at or above `wcommit`.
   `raftTorn RaftState.init es k` has `wcommit = 0` and the first `k` bootstrap conf entries: false for
   `k ≥ 2`. And `RestartNode.spec` restarts only at `γ.bootLen ≤ σ.commit`
   (`Spec/go_etcd_io/raft/v3/RestartNode.lean:93`), so such a state could not be restarted anyway; making
   it restartable is a new protocol argument that must use `MaxSizePerMsg` ≥ the bootstrap log's size
   (the Go test above shows it false otherwise).
2. *Entries above the durable term.* `durPers` (`:2963`) bounds every log entry's term by `S.term`
   (`:2970`). A batch that raised the term (a follower's first append from a new leader: one `Ready`
   with the new `HardState` and entries of the new term) torn keeps entries of a term above
   `st.durable.term`, and `raftTorn` keeps the stored term (it must: `StorageHolds` reads the state
   record). The no-conf-entry premise does not exclude it; Go reaches it (13 runs above).
3. *No torn content in `readyEnter`.* The law's only source for the batch is `readyEnter … st st' ms`,
   whose crash half (`readyEnterCrash`, `InvApi.lean:2721`) is a wand entering the whole of
   `st'.durable`; the facts a torn state needs (the entries' records, `batchOk`'s `durPers` of the batch)
   are inside it. A torn law needs a third conjunct of `readyEnter`, built by `RawNode.Ready`'s proof from
   a new protocol lemma (`raft_crash_torn` beside `raft_crash_enter`, `Protocol/Enter.lean:2302`), i.e.
   raft's API and its `Ready` proof change, not only a defs-tier law.

**Minimal restatements, and the recommendation.**
* (R-a, recommended; Q1 (a)) Delete `readyCrashTorn.law`: fix the WAL fork so that a torn `Save` reads as
  no `Save` (every `Save` with entries ends with a state record; `ReadAll` drops entry records after the
  last state record), and have etcd bootstrap again (`StartNode`) when the WAL holds no state record (a
  crash between `wal.Create` and the first `Save`, or a torn first `Save`): raft's state is then
  `RaftState.init`, `nodeBoot` is persistent, and the existing `nodeCrash` covers it. Without the second
  half, etcd's restart after a crash before its first `Save` (`haveWAL` true, empty storage) calls
  `RestartNode` at `σ.commit = 0 < bootLen`, which `RestartNode.spec` excludes, torn or not.
* (R-b) Keep a torn law for later batches only: premise `(∀ e ∈ es.take k, ¬ IsConfEnt e ∧ uint.Z e.Term' ≤
  uint.Z st.durable.term)`, plus obstacle 3's API change (sizing: the note's 600-1200 lines, unchanged).
  Not usable for etcd as is: etcd's WAL can tear a term-raising batch (obstacle 2), so T2 could not
  discharge the premise; removing it needs `durPers`'s term bound weakened (new Leader-Completeness
  reasoning: a restarted node's log may run past its term).

## 10. The torn-`Save` fix (Q1 (a)): Go done, plan for the Lean (2026-11-24, branch `etcd-safe-walfix/2026-11-24`)

**Where the code lives.** One fork pin carries everything: project `etcd` of `etc/goose.py` (rev
`bc2b5f4d0`, upamanyus/etcd branch `goose-lean-fmtattrs`) translates the WAL with its bodies over
`fsExt` (since 2026-11-15; `goose-lean-walfs2`'s `8c28a4296` and `goose-lean-walfs3-fp9`'s `d3feef9bc` are
ancestors of `bc2b5f4d0`, checked with GitHub's compare) and the server. Project `etcd-wal` (`WalTester/`)
has no pin: it translates the tester in `examples/etcd/wal` and imports the `etcd` project's
translations. So the change flows through one fork branch, one `rev` in `etc/goose.py` and the
pseudo-version in `examples/go.mod`/`go.sum` (`notes/wal-fsext-fork/bump-go-mod.sh`).

Fork branch **`goose-lean-fmtattrs-tornsave`** (upamanyus/etcd), one commit on `bc2b5f4d0`:
`768ecf158` "wal, etcdserver: a Save a crash interrupts reads back as no Save" (wal.go +65/-6, new
`unsaved.go`, bootstrap.go +10, two test files).

**Go behavior before (at `bc2b5f4d0`).**
* `WAL.Save` writes the entry records, then `saveState(st)`, which writes **nothing** for an empty
  `HardState` (`raft.IsEmptyHardState`): every `Ready` whose `HardState` did not change (a leader
  appending proposals, a follower's append that moves no commit) is a `Save` of entry records only.
  `raft.MustSync` is true whenever there are entries, so such a `Save` is synced (or cut, which syncs).
  Commit-only `Save`s (no entries) may stay unsynced.
* `readAll` applies every decoded entry record (truncating the log at a lower index), and in write mode
  zeroes the tail from the end of the last valid record. A crash in a `Save` after its entry records
  (a kill once the page writer has flushed, a power loss before the fsync) restarts with them under the
  previous `HardState`: issue `raft-commit-lost-with-entries-kept`. A torn *conflicting* append even
  overwrites earlier, durable entries in the read (shown by `TestTornSaveReadsAsNoSave` before the fix:
  `2/2 B` replaces `1/2 b`).
* `bootstrap` takes the restart branch as soon as `wal.Exist` (`bootstrap.go:77`): a crash between
  `wal.Create` (in `bootstrapNewWAL`) and the first `Save` restarts raft with `RestartNode` on an empty
  log and no configuration.

**The design, as implemented** (refined from the lead's (1)-(3)):
1. `Save` with entries always ends with a state record: `st`, or the current `w.state` when `st` is
   empty (a new `encodeState`; `saveState`, which skips empty states, stays for `cut`'s header and for
   commit-only `Save`s). After `Create`, `w.state` is the empty `HardState`, so a state record may be
   empty; it still counts as a record.
2. `readAll` holds decoded entry records in `pending` and applies them (the old code, unchanged) when
   **any** later record arrives; at the end the trailing entry records are dropped. In write mode the
   tail is zeroed and synced from the offset before the first dropped record, and the encoder continues
   the CRC chain from before it (`pendOff`, `pendCRC`), so the next `Save` writes over them; `w.enti`
   counts only applied entries. "Any later record" rather than "a later state record": the same for a
   WAL the fork writes (a `Save`'s entry records are always followed by its own state record, and all
   records of one `Save` are in the tail: `cut` runs after the state record), and simpler to state:
   *a WAL reads as its records with the trailing run of entry records removed*.
3. `wal.Unsaved(dir)`: read from the first segment (`0-0`), no state record, no snapshot record above
   index 0, no entry record followed by another record (it reads `walFresh`). `wal.DiscardUnsaved(dir)`:
   if so, rename `dir` to `dir.tmp` (Create's temporary directory, which `Create` removes) and sync the
   parent; one atomic step, after which `Exist` is false. `bootstrap` calls it before
   `bootstrapBackend` and clears `haveWAL` when it discarded; an unreadable WAL is kept (the restart path
   reports it as before). A WAL with a snapshot record and no state record (a joining member that crashed
   between `SaveSnap` and its first `Save`) is not unsaved: today's restart path, outside `etcd_safe`'s
   static cluster.

**Soundness checks (by reading; the tests below exercise 1-3).**
* *Nothing is acknowledged from a `Save` before its fsync.* Raft v3.7 self-acks a leader's entries only
  after persistence (on `Advance`, `stepsOnAdvance`); a follower's responses go out after `Save`
  (`etcdserver/raft.go`, the `!islead` branch); a leader's pre-`Save` sends are appends and heartbeats,
  not acks. So a torn `Save` is a crash before the `Save`, a case raft's crash law already has
  (`nodeCrash`).
* *Every `Save` with entries is synced* (`MustSync` with entries; `cut` syncs), so only the last one can
  be torn; unsynced commit-only `Save`s write only a state record, whose loss is covered by
  `StorageHolds` (a stored commit in `[wcommit, commit]`).
* *Snapshots*: `SaveSnapshot` is synced and writes no entry; the raft loop's `SaveSnap` precedes its
  `Save`, so a torn `Save` after it is the existing "crash between `SaveSnap` and `Save`" case.
* *The apply thread receives a `Ready`'s committed entries before its `Save`* (`r.applyc <- ap`), so after
  a torn (or skipped) `Save` the backend can be ahead of the WAL: finding 2, unchanged. For the first
  `Ready` this means a re-bootstrap after a torn first `Save` can meet a backend holding the applied
  bootstrap conf changes (consistent index `n`): T3 must cover it (finding 3 grows by this case).
* *Force-new-cluster* (`AppendAndCommitEntries`, `Save(&HardState{}, ents)`) now writes the read
  `HardState` after its entries: the same durable meaning.
* *Not upstream-compatible as is*: a WAL written by an earlier etcd may end with a synced, acknowledged
  entry-only `Save`, which the new `ReadAll` drops; an upstream version needs a format marker (a new
  record type, or a version in the metadata). For the fork every WAL is written by the fixed code.

**Go tests** (go1.27.3, `GOWORK=off`, in `server/`):
* `server/storage/wal/torn_save_test.go`: `TestTornSaveReadsAsNoSave` (four torn batches, two
  overwriting index 2; the read keeps the last full `Save`, and a later `Save` with an empty `HardState`
  writes over the torn records), `TestSaveEntriesEmptyHardStateWritesState`, `TestUnsaved` (created, torn
  first `Save`, first `Save`, state only, snapshot; `DiscardUnsaved` then `Create` again), and
  **`TestRestartWithEntriesButNotCommit`**: raft's scenario with five `RawNode`s (PreVote,
  CheckQuorum), node 1 persisting every `Ready` to a real WAL, its crash a `Save` with the entry
  records written and synced and no state record, its restart `Open`+`ReadAll` into a fresh
  `MemoryStorage`. **Fails without the wal.go change** exactly as the issue (`expected "1/4 EntryNormal
  \"y\"", actual "2/4 EntryNormal \"\""`, index 4 committed on nodes 3 and 1); passes with it (node 1
  restarts at index 1, node 2 rejects its pre-vote). `TestTornSaveReadsAsNoSave` and
  `TestSaveEntriesEmptyHardStateWritesState` also fail without it.
* `server/etcdserver/bootstrap_unsaved_test.go`: **`TestBootstrapUnsavedWALBootstrapsFresh`**: a
  single-member new cluster; the first `bootstrap(cfg)` creates the WAL and the backend; "crash" (close,
  no `Save`); the second `bootstrap` must take the fresh branch (`haveWAL` false, one peer: `StartNode`);
  after a `Save` of the bootstrap batch the third takes the WAL (commit 1, one entry). **Fails without
  the bootstrap.go change** (the unsaved WAL taken as a saved one; no peers); passes with it.
* Suites: `go test ./etcdserver/ ./storage/ ./storage/schema/ ./storage/backend/` pass; `etcdutl`'s
  `go test ./...` (snapshot restore and migrate write WALs) passes; `go test ./storage/wal/...
  -skip TestWALByteMix` passes after two existing tests were updated in the same commit:
  `TestRepairWriteTearLast` (its 1024-byte cut now keeps 20 one-entry `Save`s, not 40: each also
  writes a state record) and `TestWALTypeTearStale` (it pinned the misread of
  `nonissues/etcd-wal-record-type-outside-crc.md`: a torn state record whose Type byte reads as
  `EntryType` replaced the committed entry 2; now that record and the batch's entry are trailing entry
  records, dropped, and entry 2 reads as written). `TestWALByteMix` (failing by design: synthetic
  stale-byte Type tears, `nonissues/etcd-wal-record-type-outside-crc.md`), `-short`, same 8,563,550
  images at `bc2b5f4d0` and with the fix: wrong content stale+0 808 → 321, stale-shifted 50 → 52 (all of
  the known class: a Type byte outside the CRC, `03`→`05`, a state record read as a snapshot record;
  the fork's `O_TRUNC` excludes the stale bytes it needs), 0 over zero old bytes as before.

**Phase 2 (Lean): the plan, with sizes (rough Lean lines).**

| step | what | files | size |
|---|---|---|---|
| P0 | push done; `etc/goose.py` project `etcd` `rev` → `768ecf158` (comment: this section); `examples/go.mod`/`go.sum` (`bump-go-mod.sh`); `etc/goose.py --project etcd`, `--check`. Translations that change: `wal.lean` (`readAll`, `Save`, new `encodeState`, `Unsaved`, `DiscardUnsaved`: `wal.toml` translates `*`), `etcdserver.lean` only if `bootstrap` is translated (today names-only: its contract is `bootstrapContract`/`bootstrapCrashContract`) | `Code/`, `GeneratedProof/` | generated |
| P1 | `Save`: the state record with entries (`encodeState` split off `saveState`); the history op `.save h es` keeps its meaning (`phsNext` of an empty `h` and of `w.state` agree) | `WAL__Save`, `WAL__saveState*`, `SaveRecs`, `SavePure`, `SaveAbs` (≈2,000 lines today) | 150-300 |
| P2 | the crash image: `walImg` loses its torn disjunct (`I = H.take j` only; a strengthening of the proved crash law, no trusted text added: `walImg` is the statement's vocabulary in `GooseLang/Ext/AbsDisk/Impl.lean`); the record-level image keeps "records of `H.take j`, then a prefix of operation `j`'s entry records", which the read now drops | `TailCrash*`, `Crash`, `CrashPure`, `WalEncSegsImg`, `WalEncSuffix`, `WalHistLemmas` (`walImg_*`) | 400-800 |
| P3 | `readAll`: the `pending` buffer, the flush at any non-entry record, the cut point (`pendOff`, `pendCRC`), `enti` from applied entries; the fold lemma "decoded records with the trailing entry run removed" | `WAL__ReadAll` (1,901), `ReadAllInv`, `ReadAllLoop`, `ReadAllPend`, `ReadAllReg*`, `ReadAllEnd`, `ReadAllZero`, `ReadAllTail`, `ReadAllWF*`, `WalEncFold` (≈8,000 ReadAll lines today) | 800-1,500 (the largest) |
| P4 | `Unsaved` (a decode loop like `validSnapshotEntries`) and `DiscardUnsaved` (a directory rename and `syncDir`, as `Create`'s `renameWAL`): specs (true ⇒ every crash image reads `walFresh`; after the discard, `wal.bootRes`'s "no WAL, possibly `wal.tmp`") and proofs | new `storage/wal/Unsaved*.lean` | 600-1,200 |
| P5 | the server: `bootstrapCrashContract` and `bootstrapContract` gain the discard branch (a crash image whose WAL is unsaved boots the fresh branch); `memberGen`'s first-start disjunct reached from such an image; **delete** `raftTorn` and `readyCrashTorn.law` (`MemberGen.lean`); T1 (600-1,200) is gone and T2 loses its torn case; T3 covers the new leftovers (`wal.tmp`, a backend with the applied bootstrap batch) | `MemberGen.lean`, `InvCrashImage.lean`, `NewServerCrash.lean`, `WalApi.lean`, `InvBoot.lean`; #34's stage 5 if it proves `bootstrap` | 300-600 (+T3) |
| P6 | the WAL tester: Go `walImgs` (`examples/etcd/wal/ref.go:200`) drops the torn images (its `k` loop); its Lean (`walImgs.lean`, `RestartPure`, `ReadsBack`, `checkRestart`); rerun its Go crash tests | `examples/etcd/wal/`, `WalTester/Proof/.../wal/` | 150-400 |
| P7 | interfaces (`etc/gen-interface.py`), `etc/tcb-report.py --check` (no axiom change expected), the issue files' `blocks-proof:` (yes once D6's proof uses the fork fix) | | — |

Total about 2,400-4,800 changed lines, net of T1 and T2's torn case it saves; P3 is the critical path
and P2/P4/P6 can run beside it once P0 lands. The upstream-report candidate is recorded in the two
issue files' `## Fix` sections (an etcd fix, with the format caveat above); an etcd-side issue file of
its own (the WAL keeps a torn `Save`'s entries, with `TestRestartWithEntriesButNotCommit` against the
real WAL) is the natural report if the lead wants one.

### Phase B progress (P6, branch `etcd-safe-walfix-p6`)

- 2026-11-24: E0 (`WalNorm.lean`), E1 mostly written (not compiled), E3's pure core begun
  (`WalEncFoldPend.lean`). **Hard stop**: `encodeState` of an empty `w.state` needs `proto.Marshal` to
  return a non-nil empty slice, which `proto.MarshalPb.spec` (trusted) does not say; write-up and the
  proposed change in `notes/wal-p6-handoff.md`, "The hard stop".
- 2026-11-24 (session 2): the coordinator's answer applied (`proto.MarshalPbNonNil.law`, the
  undischarged non-nil fact; `walStIn` for `w.state`). Compiled bottom-up through `WalEncFoldPend`
  (**E3's fold lemma `readAllFoldP_append`**), `Abs`, `Handle`, `Inv`, `SaveHandle`, `saveState`. E2's
  design settled (`notes/wal-p6-handoff.md`, "E2 settled"): `PendStop` in `CrashTo` and `tailStop`,
  ghost image `d.H.take j`, W1 needed for the pending-tail crash. Next: `CrashPure`/`TailCrash*`.
- 2026-11-25 (session 3): **E2 compiles** (the crash image a prefix of `d.H`, `PendStop`, `LastDec`); W1 for a
  pending run (`pendStop_transfer`, used for a repaired tail); E3's pure layer (the running decode, its end,
  `readAllFoldP_wal`, `readAll_success` over the new fold); `VsePure` over normalized histories; the
  release/open positions invariant under normalization. Left: `WAL__ReadAll` (E3 proper), `TailPend` with a
  pending run, `RepairReg` (E4), then `Save`/`encodeState`/laws and the rest (`notes/wal-p6-handoff.md`,
  "Session 3").
- 2026-11-25: the hard stop resolved: Upamanyu approved (#8, 00:38Z) `proto.MarshalPb.spec`'s post
  `⌜l ≠ null → d ≠ slice.nil⌝` (trusted text, this one change); `proto.MarshalPbNonNil.law` deleted, the
  `ZeroStLaw`/`walStMarsh` proofs take the spec.
- 2026-11-25 (session 4): **E3's `WAL__ReadAll` loop** over `pending` (`02067e4964`, `f8518a494c`): the
  forward-determinism plan (`DecReach`: `Reach`, `reach_det`, `reach_files`; `RdLoopP`; `rdLoopP_eof_wal`:
  `pendOff = wr`, `pendCRC` the chain's CRC), the flush as an inline range loop, the write-mode exit's
  `endOff`/`endCRC`. Left in the file: `ZeroToEnd`'s zero word at `wr` with a pending run (item 2, `TailPend`
  with a pending run) and `w.state`'s provenance (`CloneStLaw`).
- 2026-11-25 (session 5): item 2 (`TailPend` := `RepOld`; **premise removed** from our `ZeroToEnd.specWalTail`:
  the zero length word at `wr`) and `WalPbIn.CloneStLaw` (proved for raftpb over `proto.ClonePb.spec` and
  `proto.MarshalPb.spec`; no axiom): `WAL__ReadAll` builds. `wal.Link` regenerated; it fails only in
  `RepairReg` (E4: `Repair` truncates at `wr + |pending run|`, the specs `*.specRepTail` and
  `walTail_truncSup` to generalize; `notes/wal-p6-handoff.md`, "Repair with a pending run").
- 2026-11-25 (session 5, later): E4's `Repair` with a pending run done (truncate at `LastOffset` ∈ `[wr, size]`,
  the run kept; fsync and put-back by the pending token, the synced layout `TailPend` past a run; our specs
  `os.File.Truncate.specRepTail`/`fileutil.Fsync.specRepTail` restated, `os.File.Truncate.specAu`'s closure
  widened, all ours and proved); `WAL__Save` over the normalized op. **`wal.Link` builds** (real `lake build`,
  kernel-checked); its axioms (`#print axioms` of all 254 linked results) are exactly the
  `wal-fsext.txt` baseline, no `sorry`. `etc/tcb-report.py --check` itself needs a full build of the
  worktree (965+ stale modules of other parts), not run. Left: the WalTester consumers of `CloneStLaw`,
  `Unsaved`/`DiscardUnsaved` (new functions, no spec yet), E5.
- 2026-11-25 (session 5, end): WalTester over `CloneStLaw`/`ZeroStLaw` (its Link regenerated, `Adequacy`);
  its `TopLevelRobustness` builds. **Hard stop at P4**: `DiscardUnsaved`'s post (no WAL at `dir`) is
  unreachable in the trusted abstract disk (no step removes a WAL, a crash never drops a named one); two
  steps proposed (`"WalUnnamed"` at the rename, `"WalDiscard"` at the parent's fsync), with the minimal
  program and the real code: `notes/wal-p6-handoff.md`, "The hard stop: `DiscardUnsaved`". `Unsaved`
  needs no semantics change (its spec proposed there).
- 2026-11-25 (session 6): **`Unsaved` specified and proved** (`Spec/.../wal/Unsaved.lean`, `Proof/.../wal/Unsaved.lean`,
  pure `UnsavedDefs.lean`; linked as `walfs.wal.wp_Unsaved`, no new axiom): `true` ⇒ a WAL at `dir` whose history
  is blank (`walBlank`: `Save`s of nothing, snapshots at index 0), prefix-closed (`walBlank_take`, every crash
  image). `walInv_openAll` also returns the step bound `⧖ |H|` (the first segment's sequence below `2^64`).
  **`DiscardUnsaved`: the approved order relaxation ("lower bounds read while present") is not enough**:
  `bootstrap` re-`Create`s the WAL in the same generation after the discard, so a persistent fact of the
  discarded WAL (`walNamed`, `walSyncedLb`) would read as a fact of the new one (`walGhost_raiseNamed` would
  name a WAL that a crash may still drop). The facts need the WAL's incarnation; design and the question in
  `notes/wal-p6-handoff.md` START HERE.
