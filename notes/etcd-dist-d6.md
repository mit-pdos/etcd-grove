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

## P11, P10: `etcd_safe`'s crash skeleton on `Robust`'s thread bound (2026-11-24, branch `etcd-safe-crash/2026-11-24`)

* **P11, the bridge.** Perennial (pin `b3f2fc48`) has `goose_dist_mixed_crash_adequacy_below` (the thread
  bound on the execution, `DistCrashNstepsBelow`), so no Perennial change was needed. `Net/Statement/
  DistCrashAdequacy.lean` gains the thread-bound forms beside the old ones (`CrashBootWpET`, `crashPreET`,
  `nodeStart_of_crashBootET`, `robust_of_dist_crash_adequacyT`; with the file extension `CrashBootWpGT`,
  `crashBootWpET_of_GT`, `robust_of_dist_crash_adequacy_fsT`), as `robust_of_distBootILT` for the all-stable
  bridge: an execution of `n` steps below `threads` threads runs at `threadBound = threads` and `max (n+1) lo`
  receipts. `robust_of_dist_crash_adequacy_etcdNet` (`etcdstart/NetExtsCrash.lean`) is restated over it:
  crashing machines `Net.CrashBootWpGT etcdCQ (etcdIdCrashRest C) threads lo bound`, their first generation at
  `threadBound = threads`, stable machines `Net.DistBootWpSLT threads lo bound`.
* `EtcdBootC`/`EtcdBootCBad`/`etcd_safe_of_boot` (`dist/TopLevelRobustness.lean`) at `threads := etcdThreads`,
  `bound := etcdSteps`, no receipt floor (`srvLevelK` and `2^28 - 1` gone), matching `etcd_robust.spec`.
* **P10.** `EtcdBootCBad`'s member obligation is from the generation's empty package state (`emptyPkgs`,
  which the crash gives back), not `True`. `etcdBootCBad_holds` (`dist/BootBad.lean`), proved from
  `serverBadWp`/`clientBadWp`/`nodeBadWp` (the three boot proofs' WPs factored out of `serverBootBad` &c.,
  which now apply them) and `crashBootBad_of_wp`; `etcd_safe_of_bootWF (Hctx) (HS : EtcdBootC)`. Same `Hctx`
  hypothesis as the no-crash side.

## Crash interim axioms (2026-11-24, branch `etcd-safe-crash/2026-11-24`)

Each reviewed by a fresh `axiom`-skill agent given the statement and the Go code; reports in
`notes/axiom-review/c-i{1,2,3}-*.md`. None is used by a proof yet.

* **C-I1** (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`, four axioms over the opaque
  `dbCrashKeep γ path Dl Dn` and `dbSyncs γ path`): `dbCrashKeep_new` (from `dbSyncs`, `bPath`, `dbHalf` and a
  fresh write transaction at the committed `D`: the record `(D, D)`), `dbCrashKeep_half` (the half lent to
  one atomic update; a change moves the fallback), `dbCrashKeep_close`, `dbCrash` (under the crash premise
  `BoltCrashWhole`, from the record, `crashed`, `crashRest … Dx` and the new generation's name claim at
  `path`: `fileAtF path D'` with `D' = Dl ∨ D' = Dn`, `crashRest … (i :: Dx)`). The lead's
  `dbDurLb γ D` is not needed: the record carries the fallback. Review: `_half` and `dbCrash` refuted as
  first stated, fixed (one-step lending; the name's commit in `dbSyncs`; `BoltCrashWhole` for torn
  `Truncate` sizes and FNV mixtures). **Open**: `dbSyncs`' producer (bbolt's persistent `NoSync`/
  `NoGrowSync` fields and the directory sync; until then the laws are vacuous) and `BoltCrashWhole`'s
  statement (a world premise for the owner, as `W1`); a closed database (defrag, the snapshot install)
  has no law.
* **`nonissues/bbolt-init-not-crash-safe.md`: not refuted.** The fork's `needsInit` covers a crash before
  `init`'s first sync; between its two syncs the model can tear both metas, `Open` fails, etcd's
  `newBackend` panics. Now `blocks-proof: yes`; C-I1 is restricted to opened databases. Proposed fork fix:
  `needsInit` also reinitializes a four-page file whose pages 2-3 are the first write's and whose metas
  are each zero or invalid.
* **C-I2** `bootstrapCrashContract.law` and **C-I3** `bootstrapLeftContract.law`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/CrashInterim.lean`): **laws (`abbrev … : Prop`), not
  axioms**, because both are false of the pinned etcd (`bc2b5f4d0`: torn `Save`s read back, unsaved WALs
  restarted) and true only of the torn-`Save` fork `768ecf158`; each becomes an axiom when the pin moves
  (the fix's P0, with layer 1 re-proved over the fork's `Save`). C-I2 review: refuted as first stated
  (unguarded `γ`/`dir`/`id`; an unsaved WAL beside an applied backend), fixed (the deployment's names as
  hypotheses, as `bootPremiseR`; `γ.cl.bootLen ≤ σ.commit` added to `bootstrapCrashContract`). C-I3
  review: survives, suspect (`walAreaUnsaved` wider than `wal.Unsaved`: restate over the history; the
  opaque data-area disjunct removed, so only WAL leftovers are covered).
* **Findings for T3/T4/T7.** (1) An unsaved WAL beside a backend that applied the bootstrap batch is
  likely reachable with the fork's fix (raft hands out the committed bootstrap batch before its `Save`,
  etcd applies before `Save`, the backend commits on its timer; code reading, no Go test yet): the fix's
  fresh branch is then wrong; neither law covers it. A Go test and an `issues/` file are next; a fork fix:
  `DiscardUnsaved` only at consistent index 0. (2) `srvCrashImageAt` requires `γ.cl.bootLen ≤ i`, false of a
  crash after the first `Save` and before the backend's first commit (`i = 0`): `memberGen_crash.law` needs
  that case.

### The combined fork head and the decisions after the first reviews (2026-11-24)

* **Fork head for `etcd_safe`: `upamanyus/etcd` `goose-lean-crashfixes` @ `71295dd6d`** = the applySnapshot
  guard (`goose-lean-slicessort-on-fmtattrs-snapguard` @ `8aa40fd5c`) merged with the WAL torn-`Save` fix
  (`goose-lean-fmtattrs-tornsave` @ `768ecf158`), both on `bc2b5f4d0`, plus the directory sync after the
  database renames of defrag and the snapshot install (`nonissues/etcd-backend-rename-without-dir-sync.md`;
  decision (b) of the coordinator). Not bumped in `etc/goose.py` here: done at integration.
* **Which change makes each law true.** C-I2 (`bootstrapCrashContract.law`): the torn-`Save` fix (`ReadAll`
  drops an unfinished `Save`, `DiscardUnsaved` removes unsaved WALs, so a WAL with `bootLen ≤ σ.commit` reads
  as complete `Save`s); the applySnapshot guard is not needed by `bootstrap` (it is the raft loop's). C-I3
  (`bootstrapLeftContract.law`): the torn-`Save` fix's `DiscardUnsaved`. C-I1's name durability: the dir-sync
  change for the two renames; a fresh `bolt.Open`'s name is durable once `bootstrapNewWAL` syncs a directory
  (the model's `DirSync` commits every logged operation).
* **`dbSyncs`' producer (for T7, a law to prove once `dbSyncs` is a definition):** for etcd's three paths,
  from bbolt's persistent fields `NoSync = false`/`NoGrowSync = false` (`Inv/Bolt.lean`) and a commit lower
  bound covering the operation that made `path` name the database's inode: a fresh `Open` (covered by the
  WAL's first directory sync), defrag's and the snapshot install's renames (covered by the fork's new
  syncs). Not stated in Lean yet: `dbSyncs` stays opaque, so C-I1 is vacuous until T7 writes its definition
  and this law (the definition changes what the C-I1 axioms say: they are re-reviewed then).
* `BoltCrashWhole` (the opaque crash premise on `Q`): accepted by the coordinator as a trusted item of the
  final packet, like `W1`.

### Re-review of the restated set (2026-11-24, a fresh `axiom`-skill agent)

C-I1: `dbCrash` false of the model before the commit point (the new meta's bytes are crash candidates from
its `pwrite`) and `dbSyncs` unsound once produced (renames undo a persistent durable name): both fixed (the
record announces the commit in flight, `dbCrashKeep_announce`; `dbSyncs` split into persistent `dbOpts` and
exclusive `dbNameDur`, not returned by `_close`); `BoltCrashWhole` now takes the inodes it covers, still opaque
(to be defined for the owner packet); `_new`, `_half`, `_close` survive. C-I2 survives. C-I3 survives but is
too narrow (its new case is unreachable on one file system; the backend leftovers are what T3 must cover) and
depends on the WAL's whole-sector premise. Reports: `notes/axiom-review/c-i{1,2,3}-*.md`. The last C-I1 fixes
were not re-reviewed again.

### Third review of C-I1 (2026-11-25)

No panicking program; `dbNameDur` (path-indexed) would make `dbCrash` false once produced: removed. The
record now names γ's inode `i0` (`dbCrashKeep γ path i0 Dl Dn pd`, from `boltIno` at `_new`), `dbCrash` gives
`fileHoldsM i0 D'` under `Named V'.now i0` (the caller derives which inode `path` names from the file
extension's crash facts). `BoltCrashWhole` stays opaque, with the weak forms in its docstring (to be
defined for the owner packet). Open: the in-flight txid's receipt. Final C-I1: `dbCrashKeep_new`,
`dbCrashKeep_announce`, `dbCrashKeep_half`, `dbCrashKeep_close`, `dbCrash`; opaque `dbOpts`, `dbCrashKeep`,
`BoltCrashWhole`. `notes/axiom-review/c-i1-bbolt-crash.md`.

### Fourth review of C-I1 (2026-11-25)

No refutation. A stale-announcement gap fixed (`_close` only with nothing announced; `dbCrashKeep_clear` with a
fresh write transaction); `BoltCrashWhole` restricted in its docstring (open database, no extending write since
the last sync; the size part to move into the file extension); `dbOpts`' producer: `Open`'s postcondition. The
last fix is not re-reviewed. Final C-I1: `dbCrashKeep_new`, `_announce`, `_half`, `_clear`, `_close`, `dbCrash`.
