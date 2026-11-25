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

* **Q1 (the torn bootstrap batch; recommendation (a))**: (a) fix the fork so that `Save` is atomic across a
  crash: always end a `Save` with a state record, and have `ReadAll` drop entry records after the last
  state record (they belong to an unfinished `Save`; nothing was acknowledged from them, since
  messages leave after `Save` returns); the WAL's `walImg`/`walRead` then read a torn `Save` as none, and
  T1 is not needed; (b) prove T1 and add a test-backed `issues/` entry for the bootstrap variant, with a
  premise excluding it; (c) restrict the theorem. (a) is a Go change with its own `issues/` report.
* **Q2**: `W1` becomes a premise of every member machine's crash (finding 4); it is pending review. Decided by the lead: into the semantics (`etcdCQ`), not a top-level premise; owner packet below (§Q2 packet).
* **Q3**: the received-snapshot crash window (`σ.b > i` with a `.snap.db`): extend `wal.crashImage` or
  show etcd's order (`SaveDBFrom` synced before `SaveSnap`) excludes it.
* **Q4**: the storage registry across a crash. `ρ.rd.raft` names the registry (`SrvRaft.reg`), and
  `restartNames` keeps it; a crash's new heap needs a fresh registry (or a proof that a registry naming
  dead locations is harmless). `memberRestart` leaves the registry name free (`γ' = {C.γ with reg := r}`);
  T4 decides.
* **Q5**: D4b's crash interpretation (§5).

## §Q2 packet: `W1` as `etcdFsSem`'s crash premise (for the owner, 2026-11-24)

**Today.** `etcdFsSem := Fs.fsSemWithS etcdSQ (fun _ _ => True)` (`examples/lib/etcdstart/FsExts.lean`): a member's
crash is any `OsCrash` (any byte-wise mix of each unsynced byte's candidates). The WAL's crash proof
(`walInv_crash`) needs `W1`, which the single-machine WAL tester assumes as its crash premise (`tQ`,
`WalTester/.../wal/Adequacy.lean`); `etcd_safe` cannot use the WAL proof without it.

**With this change** (branch `etcd-safe-crashskel/2026-11-24`, trusted lines in `FsExts.lean`):
```lean
abbrev etcdCQ : Fs.OsState → Fs.OsState → Prop := fun st st' => WalFs.W1 walCodec st st'
@[reducible] def etcdFsSem : ExtSemantics Fs.fsExt := Fs.fsSemWithS etcdSQ etcdCQ
```
`W1` (`Proof/go_etcd_io/etcd/server/v3/storage/wal/W1.lean`, unchanged): every WAL frame a fresh reader accepts
after a crash has its core as of one change. The crash corollary and the skeleton use it
(`etcdNetExtsCrashInterp` with `fs_crash_interpS etcdSQ etcdCQ`; `EtcdBootC`'s `CrashBootWpG etcdCQ`). New semantics
example `examples/osfs/semantics/premise_w1.go` (indexed in `doc.go`).

**Why.** The WAL's recovery is correct only if a torn frame is rejected, which etcd delegates to the CRC
(`decoder.go:133-150`); the semantics allows any mix. In the semantics, not a top-level premise (the lead's decision):
the same place as the existing step premise `etcdSQ` (no I/O error), and no theorem whose machines never crash sees
it (the single-process theorems, `etcd_safe_nocrash`, `putget_safe`: `Robust []` has no crash step; they rebuilt
unchanged).

**Risk.** Review `notes/axiom-review/w1-etcdfssem.md` (suspect, by design): `W1` excludes real crashes beyond CRC
collisions: an intended frame whose zero tail is still in the encoder's buffer (real on C; for etcd byte-identical
to an allowed later crash image), and a torn `Type` field over stale nonzero bytes (not produced by etcd's file
handling). It covers every `.wal` file on a member's machine, so it is a claim about the deployment's programs
(only etcd's member runs there), not about Linux. Satisfiable (`W1Sat`), so no execution is cut short by it.

**Recommendation.** Accept for `etcd_safe` as the WAL tester's premise reused (rule: reuse audited premises), and keep
the planned restatement to the CRC-only target (*no CRC-32C collision on the `Data` of a frame over zeros*,
`notes/wal-fsext-plan.md`, "W1's target") as the follow-up that removes the two excluded real-crash classes.

## T6: the snapshot directory across a crash (design, 2026-11-24, branch `etcd-safe-d6t6/2026-11-24`)

**What the directory holds at this pin** (fork `8c28a4296`, `server/etcdserver/api/snap/`): only database
snapshots `<index>.snap.db` and `tmp*` temporaries. There is no `SaveSnap`/`Load`/`LoadNewestAvailable`:
`snapshotter.go` has `New` and `ReleaseSnapDBs` only; the raft snapshot lives in the WAL's snapshot record
and the backend. `bootstrapSnapshot` (`bootstrap.go:211-252`) removes `tmp*`, `db.tmp*` and `*.snap` files at
every start.

**etcd's crash handling, read at the pin: safe.** `SaveDBFrom` (`db.go:39-99`): `CreateTemp(dir,"tmp")`,
copy, `Fsync(f)`, `os.Link(tmp, <i>.snap.db)` (never replaces: `ErrExist` keeps the old one and syncs the
directory again), `Remove(tmp)`, `fsyncSnapDir(dir)`, then returns; the receiver processes the `MsgSnap` (and
the WAL's snapshot record is written) only after. So a `.snap.db` the WAL can name is durable, whole, under
its name. A crash before the directory sync leaves (a) nothing, (b) the `tmp*` (removed at the next start), or
(c) the linked name, whole (the file was synced before the link). `ReleaseSnapDBs` (`snapshotter.go:45-78`)
removes `.snap.db` files below the snapshot index with no directory sync: after a crash a removed file may
**reappear**, harmless (it is below the applied snapshot; the next `ReleaseSnapDBs` removes it again;
`DBFilePath` looks up by exact index). Nothing for `issues/`.

**Why the lemma cannot be stated over today's `snapDirInv` alone** (two gaps, both in a trusted vocabulary):
1. *Durability is not recorded.* `snapDirInv`'s files are `backend.fileAt (snapDBPath sd i) D` (the name's
   claim naming an inode whose bytes hold `D`), with no claim that the bytes and the name's entry are
   synced. The new generation can keep a file only if it was durable, so the invariant has to say so:
   `SaveDBFrom`'s axiom (`Spec/.../snap/Snapshotter__SaveDBFrom.lean`, trusted) puts a file into `M` only
   after its two syncs, which is what Go does, but its post (the invariant) does not carry it.
2. *No crash disjunct.* The invariant is `inv snapDirN (snapDirInv …)` over the old generation's file
   ghost state; after a crash its contents must be taken out and the invariant closed, which needs the
   WAL's shape (`walInv`: `body ∨ crashed L ∗ walCrashTok`). `snapDirInv` is sealed (`@[no_expose]`) and
   is the vocabulary of three axioms (`SaveDBFrom`, `ReleaseSnapDBs`, `storage.Release`): changing its
   body is a trusted change.

**Proposed trusted change (packet to write after the lead's go-ahead):** `snapDirInv`'s body becomes
`snapDirIs p γd ∗ ((∃ M E, … as today, each file `fileAtDur` …) ∨ (crashed L ∗ snapCrashTok γd))`, with
`fileAtDur path D` = `fileAt path D` plus "every byte durable and the name's entry durable" (the file
extension's durable view, as `fileStart`/`osShared`'s logged entries); the axioms' statements unchanged
(they hold the invariant, and inside one generation the crash disjunct is excluded by `notCrashed`).
Removed files are not tracked (their reappearance after a crash leaves `M` unchanged).

**The law (statement, `Proof/.../rafthttp/SnapDirCrash.lean`, to write once the shape above is decided):**
```lean
abbrev snapDir_crash.law (Q : Fs.OsState → Fs.OsState → Prop) : Prop :=
  ∀ (L L' : GooseLocalGS GF) (V' : Fs.Hist) (R : Fs.Roots) (D : List Ino) (sd : GoString) (γd : GName)
    (img : w64 → backend.Data → IProp GF) (Rm Rm' : w64 → IProp GF),
    L.goose_go_local_context = lctx → L'.goose_go_local_context = lctx →
    ⊢ (letI : HeapGS .hasLC GF := ⟨G, L⟩; inv snapDirN (snapDirInv sd γd img Rm)) -∗
      snapCrashTok γd -∗ crashed (hC := L.goose_crashGS) -∗ □ (∀ j, Rm j ={⊤}=∗ Rm' j) -∗
      Fs.osSharedInv (L := L) R -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) D true V' -∗
      snapDirNames (L := L') sd V' ={⊤}=∗
      ∃ D' : List Ino,
        (letI : HeapGS .hasLC GF := ⟨G, L'⟩; inv snapDirN (snapDirInv sd γd img Rm')) ∗ snapCrashTok γd ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) (D' ++ D) true V'
```
`snapDirNames L' sd V'`: the new generation's claims on the directory's `.snap.db` names (carved by the
member's restart from `osShared L' R V'`, as the WAL's `BootCrash` carves its area's); `Rm → Rm'` is the
caller's (T7: a removed index `j` is below the backend's consistent index, which the crash image's counter
`γm` covers: `c ≤ i + 1`). `γd` is kept (persistent ghost names survive a crash), so the restarted member's
`snapSaved γd j` facts still hold. Size: the law's proof ~300-500 lines over `crashRest_take_runs_keep`
(bytes), the names' log (entries durable), `osInv_alloc` at `L'`; the trusted change adds ~50 lines and the
three axioms' docstrings.

**T6 review outcome (2026-11-24): the go-ahead's "axioms' statements unchanged" does not suffice**
(`notes/axiom-review/snapdir-crash.md`). A crash between `SaveDBFrom`'s `os.Link` and its directory sync leaves a
linked, whole file whose index the atomic axiom never recorded (its name still claimed free), so the new
generation cannot re-establish `snapFree` and `snapDir_crash.law` is unprovable. Needed (a further trusted
step, for the lead/owner): `SaveDBFrom` linearized at the link (the index into `M`/`E` there, bytes durable,
entry not), its post a persistent `snapDurable γd i`; the body's `E \ M` case `Rm i ∨ ¬ snapDurable`; T2 carries
"the WAL's snapshot index is `snapDurable`". `snapDir_take` becomes a crash-token update (two callers). No Lean
change made on this branch yet.

**T6, second design round (2026-11-24, after the lead's approval of "linearize at the link"):**
- *Durability needs no new name and no axiom statement change*: let the saved map `E` mean **saved and durable**.
  The ghost steps of `SaveDBFrom` become: at the link, the index enters `M` only (bytes durable, entry not); at
  the directory sync, it enters `E`. `snapSaved γd i` (the post, unchanged) then *is* `snapDurable`; raft's
  `snapLocal` (elements of `γd`) only gets stronger. Body: `M ∩ E` files `fileAtDur`; `M \ E` files pending
  (bytes durable, entry maybe not); `E \ M` has `Rm i` (as today); `snapFree` over the indices in neither `E`
  nor `M`. After a crash, a pending file that survived stays in `M` (its certificate is persistent), one that
  vanished frees its name. The `ErrExist` branch syncs and adds the kept index to `E`. T2's "the WAL's snapshot
  index is durable" is the receiver's `snapSaved` (`netSnapRecv`), already there.
- *The crash disjunct's token has no name to live at.* `inv snapDirN (body ∨ crashed L ∗ tok)` needs `tok`
  exclusive and owned by the crash frame (`Keep L`), so that the crash law finds the body still there (the WAL's
  `walCrashTok` is at a name in `WalGS`). `snapDirInv sd γd img Rm` has only `γd`, whose ghost map's key and value
  types (`w64`, `Unit`) are shared with raft's `snapLocal`, every key a possible index. Options: (a) a fifth
  parameter `γk` of `snapDirInv` (25 uses in 19 files, threaded through `bootOk`'s and the restart's statements);
  (b) `snapDirIs p γd` (trusted, `snap/Defs.lean`) carries the token's name, allocated by `snapDirOwn`'s update;
  (c) `E`'s key type `Option w64` (`none` the token), changing raft's `snapLocal` type. Recommendation (b): one
  trusted line next to the one changed, no signature ripple.

**T6 decisions, round 3 (2026-11-24, the lead's delegation; each with its one-line why):**
1. *The crash token's name: an existential handle, not `snapDirIs`.* (b) as approved turned out impossible
   without an axiom: a persistent `snapDirIs p γd` duplicates its `∃ γk`, so two copies need not agree on `γk`,
   and agreement needs a cell at a name known from `γd` (none: `γd`'s map type is raft's). Decision: the
   user-facing handle becomes `snapDirInvH sd γd img Rm := ∃ γk, inv snapDirN (snapDirInvK sd γd γk img Rm)`,
   `snapDirInvK`'s body `snapDirIs ∗ (body ∨ crashed L ∗ token γk)`; `snapDir_init` returns the handle and
   `token γk` (the crash frame's `Keep`), which owns its own copy of the same `inv`. Why: the crash law opens the
   `inv` named in `Keep` (same `γk`, so its token refutes the crashed side), and a handle of another generation
   is a different proposition (the body is at the ambient generation), so no stale handle can be used. Cost: the
   text `inv snapDirN (snapDirInv …)` becomes `snapDirInvH …` at 25 sites (19 files, 7 of them `Spec/`, four
   axioms' statements among them: a renaming of the same claim).
2. *Durability: `E` = saved and durable* (approved). Representation: `M ∩ E` files `fileAtDur`, `M \ E` pending.
   `fileAtDur path D` = `fileAtF` with (i) the name's claim history committed (`osCommitLb h.next`, the shared
   mode's committed prefix, `TreeCommit.lean`) and (ii) the bytes durable (every `ByteG` a `durB`, size bounds
   collapsed). (ii) needs a durable variant of bbolt's sealed `fileHoldsM` (`Spec/go_etcd_io/bbolt/Api.lean`,
   `fileHoldsMDef` in `Inv/FileImg.lean`): `fileHoldsMDur i D ⊢ fileHoldsM i D`, a new law in bbolt's API
   (`etc/api/bbolt.txt`), outside T6's package. Why not avoid it: without durable bytes a surviving file's bytes
   may be any mix of candidates, which is no bbolt image, so the law cannot give `fileAt` at `L'`.
3. *`snapDir_take` becomes `|NC={⊤}=>`* (`inv_nc_acc` on `snapDirInvK`), its two callers use `wp_ncfupd`.

**Status: implementation not started on this branch.** (2) adds a law to bbolt's API and (1) touches 19 files;
both are best done together with the law's proof, by the helper that writes it, since the exact shape of
`fileAtDur` is decided by what `crashRest_take_runs_keep`/`RegionCrashed` let that proof conclude. The law's
statement (with (1)'s names): from `Keep := inv snapDirN (snapDirInvK sd γd γk img Rm) ∗ token γk` at `L`,
`crashed L`, `□ (∀ j, Rm j ={⊤}=∗ Rm' j)`, `osSharedInv L R`, `crashRest Q L L' D true V'` and the new
generation's claims on the directory's names, `={⊤}=∗ ∃ γk' D', Keep at L' (with `img`, `Rm'`) ∗ crashRest …
(D' ++ D) …`. Proof plan: open the old `inv` (token refutes the crashed side), take the body, close with
`crashed L ∗ token γk`; per file of `M` take its runs from `crashRest` (`osCrash_take_runs_keep`): a `M ∩ E` file
is durable so it survives whole (`FileCrashedR` + durable bytes), its name kept (`RegionCrashed` with the
committed bound); a `M \ E` file survives whole or not at all (bytes durable, entry maybe), its name then free;
rebuild `fileAt`/`fileFree` at `L'` from the claims (`crashRest_treeS'`'s `osShared L'`), `E` kept (`γd`
persists), `Rm'` from `Rm`, allocate the new `inv` and token.

**T6, round 4: what the implementation found (P7, 2026-11-25, branch `etcd-safe-p7`; no Lean written yet).**
Reading the file extension's crash machinery (`crashRest_region'`, `RegionCrashed`, `crashRest_take_runs_keep`,
`osFileStart`) against round 3's plan, three gaps the plan did not see, each needing a fact the body or the boot
must carry, and two simplifications:

1. *The directory's inode across a crash (gap, the largest).* The new generation's claims (the law's premise) are
   on the directory `J'` that `sd` resolves to in the crashed tree `V'.now`; the old files are named at the old
   directory `J`. `sd = dd/member/snap` is two components below the data directory's root `dd`
   (`osPathS`: a root, then a spine of fractional claims on `member` and `snap`); nothing in today's body says
   those two entries are committed, so `J' = J` is unprovable (a crash could, in the ghost state, undo `member`
   or `snap`). Go is safe: `TouchDirAll(MemberDir())` and `TouchDirAll(SnapDir())` sync the parent
   (`fileutil.go:49-85`, F-N2), and ext4 commits the whole journal. Fix: the spine durable, `∃ n, osCommitLb n`
   with every entry of both spine claims below `n`, carried in `snap.snapDirOwn` (it holds the spine already);
   source: `bootFs.touchMember.law`'s post (`bootFs.dirFresh`, an unproved law whose `TouchDirAll.spec` gives
   `osCommitLb n`, `h'.next ≤ n` for `member`) and `TouchDirAll(SnapDir())`'s post in `bootstrapSnapshot` (`snap`).
   The law then proves `lookupH R V' sd = some (.dir J)` (`lookup_joinPath`) and takes `J'` with
   `⌜lookupH R V' sd = some (.dir J')⌝` from its caller.
2. *Free names durable at the first start (gap).* `snapFree`'s claims must be free after every crash, else a
   stray at an unsaved index has no certificate and no `Rm`. For later generations this is free (claims
   `namesOf V'`, nothing logged). For the first, `bootstrapSnapshot` carves them from `TouchDirAll(SnapDir())`'s
   new directory claim, whose history is unconstrained in `TouchDirAll.spec`. Fix: `TouchDirAll.spec`'s
   success post adds that every entry of the new directory's claim writing a name other than `.touch` is below
   `n` (true: `mkdir` is entry `x`, `hJ.next = x + 1`, and `n = x + 1`; `IsDirWriteable` writes `.touch` only);
   `carveFree` turns it, with `osNames_histCoh`, into "every crash leaves the name free" (`DurAt` below).
3. *A pending file removed before its directory sync (gap in the ghost steps).* `ReleaseSnapDBs` may remove a
   file between `SaveDBFrom`'s link and its sync; the removal is not durable, so the file may reappear at an index
   in neither `E` nor `M`. Fix (ghost step of `ReleaseSnapDBs`/`Release`, a docstring change): the removed
   index joins `E` with its `Rm j` (given). So `E` is "durable in `M`, or removed with `Rm`", which is all the
   crash law and T2 need (`snapSaved` + a refutation of `Rm` still finds the file in `M`).
4. *Simplification: no new bbolt law.* `fileHoldsMDur i D` is definable outside bbolt from its public API:
   `osMeta i 1 m ∗ osBytes i 0 1 (bs.map durB) ∗ ⌜m.maps = ∅ ∧ m.size = bs.length ∧ m.lo = m.hi = m.size ∧
   boltImage bs D ∧ bs.length ≤ boltMaxMapSize⌝ ∗ boltImageRcpt bs`, and `fileHoldsM_of_image` (exists) gives
   `fileHoldsM`. One small API law is needed instead: `boltImageRcpt` at generation `L` gives it at `L'` (its
   body is `fileRcpt`, a time receipt, global).
5. *Simplification: one durability predicate.* `nameCrash h j b P := ∃ n, osCommitLb n ∗ ⌜∀ K, (∀ xe ∈ h.ents,
   xe.1 < n → K xe.1) → P (h.valAfter j K b)⌝`, the form `RegionCrashed` concludes: durable file `P = (· = some
   (.file i))`, pending file `P v = (v = none ∨ v = some (.file i))`, free name `P = (· = none)`.
6. *The law's `Rm → Rm'`* must be a plain persistent wand `□ (∀ j, Rm j -∗ Rm' j)`, not `={⊤}=∗`: the body
   keeps `□ ∀ i, … → Rm i` for every index, which no update over infinitely many indices can rebuild.

Trusted text these change: `snapDirInv`'s body (round 3's shape plus 1-3), `snap.snapDirOwn` (1), the
docstrings of `SaveDBFrom`/`ReleaseSnapDBs`/`storage.Release` (3), and the statement of the unproved law
`bootFs.touchMember.law` (1, through `bootFs.dirFresh`). Proved-spec changes: `TouchDirAll.spec` (2),
`snapFree`/`snapFreeAll` (2). Size estimate now 1500-2000 lines.
