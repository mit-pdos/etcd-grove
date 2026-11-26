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
| `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/crash/MemberGen.lean` | defs | `MemberCl`, `memberFirst`, `memberRestart`, `memberGen`, `atCtx`, `memberPc`, `memberGen_crash.law` (`raftTorn`, `readyCrashTorn.law` retired by T7, 2026-11-25) |

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
  `sync`, outside the model. `issues/bbolt-init-not-crash-safe.md` (a crash inside the first
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
  **Decided (T4, 2026-11-24): a fresh registry name per generation, at `M = ∅`.** The crash law
  (`memberGen_crash.law`, T7) allocates `memStorRegAuth ∅` at a fresh `r` and the generation runs at
  `γ' = {C.γ with reg := r}`; the old generation's authority is not carried across the crash (it names
  dead locations, and keeping it would need it inside the run's crash invariant). `NewServer.specC` is
  unchanged: it quantifies over `γ` and `M`, and its post is at `γ`, whatever its `reg`. What this
  asks of T7: the global facts it hands `specC` (`srvRaftLogInv`, `kvInvM`, `srvPropMint`,
  `srvRdCtxInv`, the image's `srvRLogLb`/`confAt`/`walSnapCert`, `restartNames ρo ρ`) at `γ'`, i.e. their
  bodies must not read `reg` (the cluster's facts are already per-member-registry: `memberGOk`).
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

## 9. T4 status (2026-11-24, branch `etcd-safe-d6t4/2026-11-24`)

`NewServer.wp_proofC` (`Proof/.../etcdserver/NewServerCrash.lean`), WIP, not linked (built on the VM 2026-11-24 with `NewServerR`, the only `sorry` the case below): over
`NewServer.specRAt` (`NewServerRAt.lean`: `specR` with `bootstrap`'s contract at the image,
`bootstrapAtR`; `NewServer.wp_proofRG` now proves it, and `specR` follows, `NewServer.specR_of_RAt`).

* `i ≤ σ.commit`: proved (`srvCrashImageAt_disk`, `bootstrapAtR_of_crash`).
* `σ.commit < i`: `sorry`. Where the graceful proof needs `|A| ≤ σ.commit` (`|A| = i`):
  `restart_idx` → `NodeStartSpecR`'s `A₀.length ≤ σ.commit` and `bootLen ≤ σ.commit` →
  `rnBootPre .restart` (`bootstrappedRaft.newRaftNode.spec`), `replaySeed_facts` (needs `|A₀| ≤ σ.last`),
  and `isRaftNode`'s `rnRestartOk` (`|a0| ≤ commit0`), used by `raftNode.start` (`rnRestartOk_a0_le` →
  `rnStopImage`'s `a0 ≤ σ.commit`, `onStop`) and by the apply side (`rnRestartOk_winAbove` →
  `EtcdServer.run`/`applyAll`'s "a `Ready`'s snapshot is above the backend's log").
* The last is **false after a crash** (inference from the code, not tested): a follower applies
  committed entries before its `Save` (raft v3.7 hands unstable committed entries; `raft.go`'s `applyc`
  before `Save`), so its backend can be past even the WAL's last index `σ.last`; restarted, a leader's
  snapshot at `k ∈ (σ.last, i]` is restorable (raft's `restore` rejects only a snapshot whose entry it
  holds), `applySnapshot` checks only `k > appliedi` (and `appliedi` restarts at `σ.b`), so the backend
  goes back from `i` to `k` (`OpenSnapshotBackend`, `kv.Restore`). Probably not a linearizability bug
  (a linearizable read waits for `appliedi ≥` the leader's commit `≥ i`), but the apply-side window
  must admit it. Plan: drop `|a0| ≤ commit0` from `rnRestartOk` (keep `snap0 ≤ |a0|`), restate the
  window as "snapshot above `appliedi`, possibly at or below the backend's index" through
  `applyAll`/`ApplyAllSnap` (the backend's index may move down at a snapshot inside the replay window),
  `replaySeed_*` over `min(|A₀|, σ.last)`, `rnStopImage` without `a0 ≤ σ.commit` (so the graceful stop
  image drops `i ≤ σ.commit` too: one image), then `specRAt` over the crash image.
* `specR` from `specC`: **not as stated**. `specC` needs `walReadFacts σ` in the image (the graceful
  image lacks it: the restart contract promises it after `bootstrap`) and the crash contract, which is
  stronger than the restart one (all `i`, not only `i ≤ σ.commit`); and the graceful image's vacancy
  is armed (`nodeVacantA`), which cannot be unarmed into the crash image's `nodeVacant`. `specR`
  derives from `specC` once `wal.stopImage` carries `walReadFacts`, #34 proves `bootstrapCrashContract`
  (giving the restart one), and the crash image holds the vacancy armed (next bullet). Today both are
  instances of `specRAt` instead.
* Vacancy: `specC` arms the image's `nodeVacant` with `nodeVacant_armD`, dropping raft's crash token,
  as the graceful boot does; a generation that must survive its own crash needs that token kept (T2/T7:
  arm in the crash law and keep the token in the generation's invariant, i.e. the image carries
  `nodeVacantA`, or `specC`'s post returns `nodeCrashTok`).

### T4 round 2 (2026-11-24)

* `specC`'s post returns raft's crash token (`∃ x, nodeCrashTok γ.cl id x`, beside the old post;
  lead's decision): the proved case arms with `nodeVacant_arm`. `MemberGen` names `specC` only in
  prose; T7 takes the token into the generation's invariant.
* `NewServer.wp_proofRAt` (`NewServerR.lean`) is linked (`etcdserver_NewServer+RAt`, server `Link.lean`
  regenerated); `wp_proofC` gets its `NewServer+C` entry once its `sorry` is gone.
* **The backend-ahead case, scoped (not started).** The snapshot regression is a non-issue for clients
  (`nonissues/etcd-crash-backend-ahead-snapshot-regress.md`, branch `etcd-safe-snapreg`), but the proof
  must model it, and the apply side's ghost state is monotone where Go's backend is not:
  `applyAll.specSnapM` takes the snapshot strictly above the ghost applied index `g` (`= |a0|` in the
  window) and installs the snapshot's image as the KV state at `g`; the mvcc API's history
  (`mvccImage`, `kv.Restore`'s spec) and the ghost applied log `A` (`srvAppliedOwn`, lower bounds given
  to readers) only grow. Admitting a snapshot at `k ∈ (ai, g]` means a second ghost track for the
  backend (its index `ci ≤ g` and data `model(A.take ci)`, regressing at such a snapshot, re-applied
  up to `g` before the ghost moves) through `applyAll`, `ApplyAllSnap`, `applyEntries`/`applyEntryNormal`
  (the skip `index ≤ ci` now against the backend's track), `kv.Restore`/`lessor.Recover` at a lower
  revision, and `rnRestartOk`/`raftNode.start` (`|a0| ≤ commit0` dropped), `replaySeed_*` (`|A₀|` may
  pass `σ.last`), `NodeStartSpecR`/`rnBootPre`, `rnStopImage` (then the graceful stop image drops
  `i ≤ σ.commit` too). Estimate: several thousand lines over the server's largest proofs.
* **Recommended instead (a fork change, proof-driven, rule 14):** in `applySnapshot`, when the
  snapshot's index is at or below the backend's consistent index (only inside a restart window, after a
  crash), do not swap the backend: advance `appliedi`/`appliedt`/`confState` to the snapshot's and
  keep the backend, which already holds every entry up to `ci ≥ k` (the replay skips them). Go then
  never regresses the backend, `specSnapM`'s branch at `k ≤ g` is a skip (as `applyEntryNormal`'s
  `index ≤ ci`), and the monotone ghost state stays. What remains after it is the raft-side
  generalization (`rnRestartOk`, `replaySeed`, `NodeStartSpecR`, `rnStopImage`), smaller. Needs the
  lead's decision (a fork change, with a `nonissues/` cross-reference).

### T4 round 3 (2026-11-24): the fork guard

**Packet (changes verified etcd behavior; untrusted, a fork change under rule 14).**
* *Today* (pin `6b942d23f`): after a crash left a follower's backend ahead of its WAL, `applySnapshot`
  installs a leader snapshot at `k ≤ ci` like any other: it swaps in the snapshot's database and
  recovers lease, mvcc, alarm, auth and membership from it, moving the backend from `ci` back to `k`
  (not client-visible: `nonissues/etcd-crash-backend-ahead-snapshot-regress.md`).
* *With this change* (fork `goose-lean-slicessort-on-fmtattrs-snapguard` @ 8aa40fd5c, on `6b942d23f`):
  ```go
  <-toApply.notifyc
  if ci := s.consistIndex.ConsistentIndex(); toApply.snapshot.Metadata.GetIndex() <= ci {
      lg.Info("backend already covers the snapshot; keeping it", ...)
      ep.appliedt = toApply.snapshot.Metadata.GetTerm()
      ep.appliedi = toApply.snapshot.Metadata.GetIndex()
      ep.diskSnapshotIndex = ep.appliedi
      ep.memorySnapshotIndex = ep.appliedi
      ep.confState = toApply.snapshot.Metadata.ConfState
      return
  }
  ```
  Not done on this path, and why not needed: the backend swap and the stores' recovery (the backend
  and the stores built from it already hold every entry up to `ci ≥ k`); `storage.Release` (only
  frees older WAL files and `.snap.db`s; the next snapshot releases them); `cluster.Recover` and the
  transport's peers (the membership is the backend's); `NewUberApplier` (nothing it reads changed);
  `ep.replayConf` stays (the backend is still the bootstrap one, which is what it describes). Raft's
  storage applied the snapshot in the raft loop as before.
* *Why*: the proof's apply-side ghost state (the applied log, mvcc's history) is monotone; Go no longer
  moves the backend back, so the crash restart needs no regressing ghost track.
* *Risk*: a snapshot at `k ≤ ci` with a conf state different from the backend's membership at `ci`
  (conf changes in `(k, ci]`): `ep.confState` takes the snapshot's, and the replay of those entries'
  conf changes (applied to raft regardless of `ci`) brings it to `ci`'s, as at any restart. Tests:
  `TestApplySnapshotBelowBackend` (new; fails without the guard), the etcdserver snapshot unit tests
  (`TestSnapshot*`, `TestMergedSnapshot*`, `TestPurge*`, `TestConcurrentApplyAndSnapshotV3`) and the
  integration tests `TestSnapshotAndRestartMember`, `TestRestartMember`, `TestV3StorageQuotaAfterSnapshot`,
  `TestV3AlarmsDuringSnapshotInstall`, `TestV3AuthSerializableGetDuringSnapshotRestore` pass (go1.27.3).
* *Recommendation*: keep (pin bumped); combine with the WAL torn-save fork fix (`goose-lean-fmtattrs-tornsave`
  @ 768ecf158) when that lands.

**Proof plan after the guard.** `applySnapshot.specSnapM` keeps its meaning with `hle` made strict
(`ciEff < k`, which its callers have: `ci ≤ g < k` in `applyAll.specSnapM`), the new branch refuted
there (needs `ConsistentIndex`'s spec in the walk, reading `ciEff γ st.k`). A second spec
`applySnapshot.specKeep` for `k ≤ ci` (post: `ep` moved, everything else kept) serves the crash
window: `applyAll.specSnapM`'s premise `g < k` gets a sibling case `ai < k ≤ ciEff` (then `g` stays,
the snapshot is a skip). Then the raft side: `rnRestartOk` without `|a0| ≤ commit0`, `rnRestartOk_winAbove`
weakened to "above `appliedi`, or at or below the backend's index" (both cases now handled),
`replaySeed_*` over `min(|A₀|, σ.last)`, `NodeStartSpecR`/`rnBootPre` without `|A₀| ≤ σ.commit`,
`rnStopImage` without `a0 ≤ σ.commit` (and `wal.stopImage` without `i ≤ σ.commit`), then
`specRAt` over the crash image and `wp_proofC`'s `sorry` gone.

**Build after the pin bump (VM, 2026-11-24):** every server module up to `SnapApplyWalk` builds; the
only break is `SnapApplyWalk.lean:308` (`applySnapshot_walk`), at the guard's new code after
`<-toApply.notifyc`: it must read `s.consistIndex.ConsistentIndex()` (as `applyEntryNormal`'s
`tail_skip` does, `wp_ci_get hC γ ci b st Hp`, with the apply state's `Pci`/`Hci`/`Hinv`/`Hst`/`Hbe`)
and refute `k ≤ ciEff γ st.k` from a strict `hle`. So `applySnapshot_walk` and `wp_proof_snapM` take
`consistentIndex.ConsistentIndex.spec` (Link: `consistentIndex__ConsistentIndex` in
`EtcdServer__applySnapshot`'s line) and `specSnapM`'s `hle` becomes `<` (its callers' `ci ≤ g < k`).

### T4 round 4 (2026-11-24): `applySnapshot.wp_proofKeep` builds; the remaining steps scoped

**Built (VM, `fec7d8cf82`):** the server's `Link` and `Results` with the fork guard: `applySnapshot`'s
`specSnapM` (strict `ciEff < k`) and `specKeep`, both proved. `NewServer.wp_proofC` keeps its one
`sorry` (`NewServerCrash.lean`, the case `σ.commit < i`).

**What the five steps of "Proof plan after the guard" turn out to need** (read off the code, nothing
written yet). Each item is more than its line in the plan says:

1. **`applyAll`'s keep case is not only `applySnapshot.specKeep`.** After the guard, `applyAll` runs its
   whole tail at `k`: `applyEntries` (nil), `Trigger(k)`, both `notifyc` receives, `raftAdvancedC`,
   `snapshotIfNeededAndCompactRaftLog` (`specNoop`: disk = memory = applied = `k`, which `specKeep`
   gives), and the `msgSnapC` merge. The merge is reachable: the snapshot's `Ready` can also carry this
   node's election in a later term (`node.run` keeps stepping while a `Ready` is pending), so
   `m.GetTerm() == apply.raftTerm` can hold. With `ci > k`, `createMergedSnapshotMessage` takes its
   window branch (`replayConf != nil`, the bootstrap backend: `specKeep` leaves `replayConf`), which
   needs the payload's `replayTerms` facts (`replayImageMetadata`, `rnReplayJob γ terms rt n`), as the
   batch's merge does (`mergedCreate_window_replay`). **`rnApSnap` carries only `taReplayField`**, so
   `raftNode.start`'s snapshot hand-off must also give `rnReplayJob` for the snapshot payload
   (`terms = nil.appendEntries(rd.Entries)`, `raft.go:232-236`). The keep tail is then the batch's tail
   (`wp_proofBatch`, ~600 lines, its merge branch included) at `ms = []`, `ai = k`, with the payload's
   two-receive `notifyc` and its `srvFrozenAt`/`srvFrozenBelow` in place of `srvFrozenTerms`. Two ways
   to write it: a copy of that tail in a new `applyAll.specKeep`; or one proof, `specBatch` taking
   either no snapshot or a kept one with no entries. The second needs the run's keep arm to rebuild
   `specBatch`'s precondition at `A'` (as `run_job_body` does) and a receive lemma over either notify.
   The run's side is simple: in the window (`|A| < k ≤ |A₀|`) the ghost log stays `A₀`
   (`ghostOf_in`, `A' <+: A₀`), so `applyResR … A'` differs from `applyResR … A` only in Go's rows
   (`ai`, the term, `ep.confState`, `srvSnapState`, the cursor, `epReplayCfg`, whose second disjunct
   holds in the window).
2. **`rnRestartOk`'s `|a0| ≤ commit0`** feeds `rnRestartOk_winAbove` (the run's `hwin`) and
   `raftNode.start`'s `rnStopImage` (`rnRestartOk_a0_le`, two uses). With item 1 the run needs no
   `hwin` (`k ≤ |ghost|` is the keep case), and `rnStopImage`/`wal.stopImage` drop their commit bound
   (item 4), so the conjunct can go.
3. `replaySeed_*`: not yet read beyond its header (`replaySeed_facts` reads the replayed terms off
   the WAL's entries up to `|A₀|`, which may pass `σ.last`).
4. **`NodeStartSpecR`/`rnBootPre`'s `|A₀| ≤ σ.commit` is raft's.** It is the configuration point of
   raft's own `RestartNode.spec` (`a ≤ σ.commit`, `Spec/go_etcd_io/raft/v3/RestartNode.lean`), which a
   backend ahead of the WAL breaks (etcd hands raft the backend's conf state at `i`). Changing raft's
   spec is not needed: the server's membership is fixed (`srv_confAt_simple`: the configuration
   after any committed prefix is `Membership.simple cfg`), so the composition can give `RestartNode`
   the point `a' = min |A₀| σ.commit` (the conf state reports the same `m`; `confAt γ a' m` from
   `srv_confAt_simple` over the committed `A₀`). What then moves is the driver's view index:
   `nodeConfig ⟨a', m⟩`, not `⟨|A₀|, m⟩`. The conf entries in `(a', |A₀|]` come back from raft and
   are re-applied to raft (`ApplyConfChange` at or past the view's index) instead of skipped: the
   view's bridge (`NodeBridge`, `rnView`, `applyConfChange`) must accept that, over the same `m`.
   Then `rnStopImage` drops `a0 ≤ σ.commit` and `wal.stopImage` drops `i ≤ σ.commit` (whose
   consumers are the restart proofs: item 5).
5. `specRAt` over the crash image: `srvCrashImageAt_disk` without `hc`, then `wp_proofC` is
   `specRAt`'s instance in both cases (the proved case's pattern), and the `NewServer+C` Link entry.

**Size.** Item 1 is a new proof of about the batch tail's size plus a change to `raftNode.start` (its
snapshot hand-off); item 4 reaches the node bridge's view proofs. This is several sessions of work,
not one: the plan's "smaller" was against the regressing-ghost alternative (several thousand lines).

**2026-11-24, step 1 (`rnApSnap`'s replay terms): blocked on a raft law.** What the snapshot payload
must carry is `rnReplayJob γ terms rt k`: for a `MsgSnap` this node sent at the payload's term `rt`,
with `k < |a0|`, the payload's `terms` cover `|a0|` with `a0`'s last term. At a snapshot `Ready`
`raftNode.start` resets `terms` to `nil.appendEntries(rd.Entries)` (`raft.go:232-236`). Until now it got
the fact from `rnReplayState.empty` (`|a0| ≤ k`, i.e. `rnRestartOk_winAbove`), which a kept snapshot
(`k < |a0|`) breaks. The tool for the other case exists, `ReplayJob.lean`'s `rnReplayJob_of_history`
(the runs describe the durable state `S`'s entries above `k`, which after the reset they do: `S` is the
snapshot at `k` and `rd.Entries`), but its premise is raft's leader completeness through the node API:
`sentMsg … sm` (a `MsgSnap` at term `rt`, from this node) `⊢ ⌜DurAgrees S (a0.map toLE)⌝`, for `S` the
node's durable state at the `Ready` whose `HardState` term is `rt`, `a0` committed. No API law says
this: the raft proof has leader completeness at the protocol level (`TraceSimFacts.allFacts_leaderCompleteness`,
`TracedRaftStepRecvUT.leaderComplete_of`), and the API only `snapshotLeader` (`sentMsg_localSnapshotLeader`,
`snapshotLeader_terms_ne`). It is true of Go: a leader at `rt` holds every committed entry, and its log
at a `Ready` of term `rt` is its log at its election (a candidate's log does not change during its
term; a node elected in a later `Ready` of the same term was a candidate at this one). Without it the
fact is false of a follower: after a power loss its log can hold, at an index the backend applied, an
entry that a later leader overwrote (the overwrite applied before its WAL `Save`, `raft.go:240` before
`:264`).

The same law is what step 3 needs: after a crash the initial replay terms come from the WAL's entries
up to `σ.last`, which may hold such a stale entry at an index `≤ |a0|`, so `replaySeed_facts`'s
"`terms` give `a0`'s last term" is false without the same-term-leader premise.

**Next:** a raft API law, proved in the raft proof, roughly
`raftState γ id S ∗ isCommittedLogLb γ l ∗ snapshotLeader γ id S.hs.term ⊢ ⌜DurAgrees S l⌝` (or
in the form `rnReplayJob_of_history` takes, over the `Ready` whose hard-state term the leader's), with
its interface regenerated (`etc/api/raft.txt`). Then steps 1 and 3 discharge `rnReplayJob` by
`rnReplayJob_of_history`. Needs a decision: who proves it (raft-proof work), and its exact form.

**2026-11-24, step 3 (the configuration point `a' = min |A₀| σ.commit`): does not work; blocked on raft's
`RestartNode`.** Round 4's item 4 assumed that giving raft an earlier configuration point only makes the
conf entries in `(a', |A₀|]` re-applied to raft. Go does not re-apply them: `applyConfChange` calls
`s.r.ApplyConfChange(cc)` only when `shouldApplyV3` (`server.go:2078`), false at or below the
consistent index, so in the replay window raft's view stays at `a'`. The next conf entry `k > |A₀|`
then needs `node.ApplyConfChange.spec`'s `skippedIn γ l a' k` (`InvNodeRule.lean:594`): every conf
entry in `(a', k)` decided `.skip`. The ones in `(a', |A₀|]` were decided `.apply` (the server's rule
applies every v1 conf entry, `srvRule`; conf entries are not confined to the boot log, `ccBootOk`
only makes them no-op adds), so the premise is false. The view has to be at `|A₀|`, as etcd's
`bootstrap` makes it (the backend's conf state at `i`), so raft's `RestartNode.spec` must take
`a ≤ |l|` for a committed log `l` (the backend's, `confAt γ a m` already names it) in place of
`a ≤ σ.commit`. Inside the raft proof that premise is `RInv`'s `a ≤ commit` and its
`cfgFold … ((fp ++ log).take a) = some (stOf m)` (`RestartNode.lean:795-810`): the configuration is a fold of the node's
own log up to `a`, which a node whose log ends below `a` (`σ.last < |A₀|` after a power loss) does not
hold. Changing it means changing raft's dynamic-configuration invariant (the configuration point
ahead of the node's own log), not a local edit: a raft-proof design task of its own.

**State of the five steps:** step 1 needs the leader-completeness law (above); step 3 needs raft's
restart with a configuration point past its stored log (this entry); steps 2, 4 and 5 depend on them.
Nothing else landed this round; the last green build is `fec7d8cf82`.

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
* **`issues/bbolt-init-not-crash-safe.md`: not refuted.** The fork's `needsInit` covers a crash before
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

### Checkpoint (2026-11-25, end of the crash-axioms session; branch `etcd-safe-crash/2026-11-24`)

**Done.** P11 (crash bridge on `Robust`'s thread bound) and P10 (`etcdBootCBad_holds`, `etcd_safe_of_bootWF`),
no axiom or sorry. C-I1 in Lean (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`), final
set: `dbCrashKeep_new`, `dbCrashKeep_announce`, `dbCrashKeep_half`, `dbCrashKeep_clear`, `dbCrashKeep_close`,
`dbCrash`, over the opaque `dbOpts` (persistent), `dbCrashKeep γ path i0 Dl Dn pd` (exclusive) and the crash
premise `BoltCrashWhole I`. C-I2/C-I3 as laws (`bootstrapCrashContract.law`, `bootstrapLeftContract.law`,
`Proof/.../etcdserver/CrashInterim.lean`), not axioms: false at the pinned etcd, true of the fork head
`goose-lean-crashfixes` @ `71295dd6d`. Four reviews of C-I1, two of C-I2/C-I3 (`notes/axiom-review/c-i*`).

**Open, for the next agent.**
1. Re-review `dbCrashKeep_close` (now only with `pd = none`) and the new `dbCrashKeep_clear` (the fix of the
   fourth review's stale-announcement gap): not reviewed yet.
2. Write `BoltCrashWhole` out as a definition: only while the file is an open bbolt database with no extending
   write since its last sync; a validating meta page equals the page's page-cache contents at some moment since
   the last sync (FNV-64 collision as an explicit probabilistic premise); check some `Q` refining `OsCrash`
   satisfies it; a configuration-C example in `examples/osfs/semantics/`. Move the size part (an extending
   `ftruncate` crashes to the old or the target size) into the file extension's `CrashFile` (a trusted change).
3. `dbOpts`' producer: in bbolt `Open`'s postcondition behind γ's ghost names (not an entailment from persistent
   field cells), with `UnsafeNoFsync = false` from the Go configuration. Until then all C-I1 laws are vacuous.
4. The in-flight txid's receipt: the fourth review found it backed (receipts are global); optionally carry it
   in the record (`announce` taking it).
5. C-I2/C-I3: become axioms only after the pin moves to `71295dd6d` and the WAL's layer 1 is re-proved over the
   fork's `Save`; C-I3 to be widened to the backend leftovers (T3) and restated over the WAL history
   (`walAreaUnsaved`); its dependence on the WAL's whole-sector premise to be stated.
6. Handed to another agent (not this session): the torn-`Save` fix's fresh-start hole (an unsaved WAL beside a
   backend that applied the boot entries) and the bbolt `init` fork fix. Done: "Torn-Save fix: fresh-start
   hole" below (fork head `goose-lean-crashfixes2` @ `d49d01a07`).
7. T4/T7 finding: `srvCrashImageAt`'s `γ.cl.bootLen ≤ i` excludes a crash between the first `Save` and the
   backend's first commit.
8. Not run: `etc/tcb-report.py --check` (needs a local full build; no result uses the new axioms, so the
   baseline should not move).

### Torn-Save fix: fresh-start hole (2026-11-25)

**The hole (tested).** The raft loop sends a Ready's committed entries to the apply thread before
it saves the Ready (`raftNode.start`, `server/etcdserver/raft.go:250-276` at `71295dd6d`), and raft
(synchronous storage writes) hands out the bootstrap conf changes as committed in the first Ready.
So the backend can commit members and consistent index `n` before the first `Save` is durable. A
crash then leaves an unsaved WAL beside an applied backend; `goose-lean-crashfixes` (`71295dd6d`)
discarded the WAL and bootstrapped fresh over that backend. No panic, members and raft's
configuration right, but the bootstrap entries are replayed at or below the consistent index, where
`applyConfChange` does not call `ApplyConfChange` (`server.go:2078`): `ep.confState` stays the
fresh snapshot's empty one, is written to the backend (`beHooks.SetConfState`), and every raft
snapshot the member makes and sends (`server.go:2158`, the merged snapshot `server.go:1013`) has
`ConfState{}`; raft v3.7's `restore` rejects a snapshot not naming the receiver, so a follower that
needs one from this member never catches up (liveness; no safety violation found: a follower sends
nothing before its first `Save` returns). Test: `TestBootstrapUnsavedWALAppliedBackend`
(`server/etcdserver/bootstrap_unsaved_applied_test.go`: a real `NewServer`, the first `Save` held,
the bootstrap entry applied and committed, the data dir copied as the crash image) at `730b7bf62`:

```
control:   {members:1 raftVoters:[6e17..] backendCS:[6e17..] snapshotIndex:33 snapshotCS:[6e17..]}
restarted: {members:1 raftVoters:[6e17..] backendCS:[]     snapshotIndex:33 snapshotCS:[]}
```

Fork-only (upstream has no `DiscardUnsaved`), so no `issues/` file.

**The fix (decision: discard the backend with the WAL).** `bootstrap` (`8ceb22f8d`): when
`wal.Unsaved`, remove `member/snap/db` (absent is fine) and fsync `member/snap`, then
`DiscardUnsaved`. Until its first `Save` completed the member sent nothing, so whatever the backend
applied (the bootstrap entries, or more if a leader's append was stepped before the first Ready) is
fetched again from raft. Order: backend first, so a crash in between leaves the WAL unsaved and no
backend, and the next start discards again (tested: the restart from that image matches the
control). For the laws: C-I2/C-I3's fresh case now holds a fresh backend too (no `beExist` leftover
from an applied boot); T3's "first start with leftovers" keeps only the pre-WAL leftovers
(`bootstrapBackend` before `bootstrapNewWAL`, consistent index 0).

**bbolt's init (`issues/bbolt-init-not-crash-safe.md`).** `upamanyus/bbolt`
`v1.5.0-init-crashsafe` @ `19e0771` (on v1.5.0 `e7a8b2d`, the version etcd's `go.mod` names): `init`
syncs the freelist and root pages before writing the metas; a writable `Open` re-initializes a file
of at most four pages whose every byte is zero or `init`'s and which is not `init`'s whole image
(covers before the first sync, between the two syncs, and the old single write's leftovers).
`TestOpen_InterruptedInit` fails at v1.5.0 (one case panics), passes with the fix. The etcd fork uses
it through `replace go.etcd.io/bbolt => github.com/upamanyus/bbolt v0.0.0-20261125003757-19e0771281fa`
in `go.mod`, `server/go.mod`, `etcdutl/go.mod`, `tests/go.mod`; `TestBackendOpensInterruptedInit`
(`server/storage/backend`) panics without it.

**Port to the verified bbolt: done (2026-11-25, P13):** `upamanyus/bbolt` `goose-lean-init-crashsafe` @ `ea5656d`
(on `7d335aa3`), pinned in `etc/goose.py`, `Open.spec` unchanged (`Open/InitPartial.lean`). What follows is the state before it. The proof verifies `upamanyus/bbolt` @
`ca88bb6a` (`etc/goose.py`), 17 commits past v1.5.0 (`git log v1.5.0..ca88bb6a`: the goose forms,
the bbolt#1311 fix, the two-sync `init` 3207bac and `needsInit` 42c80a7, the `Open` sync c5a6065,
the entry limit, the leaf split, ...). Its `init` already syncs in two steps; its `needsInit` accepts
only zero metas over a subset of the data pages, so the window between the two syncs stays open
there. The port is the widened check (every byte zero or `init`'s image, not the whole image; about
25 lines replacing `metasZero`), then `DB__init`/`Open`'s proofs and `SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`.
Until it lands, the binary etcd runs (v1.5.0 + this fix) and the verified bbolt differ by those
17 commits, as they did with v1.5.0.

**Combined fork head:** `upamanyus/etcd` `goose-lean-crashfixes2` @ `d49d01a07` = `71295dd6d`
(snapshot guard, torn-`Save` fix, directory syncs) + `730b7bf62` (the test) + `8ceb22f8d` (backend
discard) + `d49d01a07` (bbolt `replace` and its backend test). Tests (go1.27.3): every package of
`server/etcdserver/...` and `server/storage/...` passes but `storage/wal`, whose whole suite runs past
`go test`'s 10-minute default (the byte-mix tests; the package neither imports bbolt nor changed since
`71295dd6d`), where the torn-`Save` tests pass (`TestTornSaveReadsAsNoSave`,
`TestSaveEntriesEmptyHardStateWritesState`, `TestUnsaved`, `TestRestartWithEntriesButNotCommit`);
`etcdutl/...` passes; bbolt `go test -short .` passes (`tests/failpoint` fails the same at v1.5.0: it
needs a gofail build).
Not bumped in `etc/goose.py`.

### C-I1 finished (2026-11-25, branch `etcd-safe-crash/2026-11-24`)

* **`BoltCrashWhole` written out** (a definition, still a premise on `Q`, `dbCrash`'s `hQ`): for a file of `I` whose
  size has not changed since its last sync and with nothing in flight past its end, a meta page of the crash image that
  validates (`boltMetaValidates`: magic, version, FNV-64a checksum, on the raw little-endian bytes, not importing
  bbolt's internal `Model/Meta`) is, on its 56 checksummed bytes, the slot as of one change (`valAt`): only the FNV-64a collision, as
  minibolt's P1. Satisfiable from every reachable state with a crash (`boltCrashWhole_exists`, over `Tests.durCrash`,
  moved from `P1Sat.lean` into `GooseLang/Ext/Fs/Tests.lean`).
* **The size part moved into the file extension** (trusted change, **pending the user's review**): `OsFile.szCrash`
  (the sizes a crash may leave: the synced size, an `ftruncate`'s/`O_TRUNC`'s target exactly, every size a `pwrite` or
  `fallocate` passed through) and `CrashFile`'s third size clause (with a change in flight, an `ftruncate`'s target).
  ext4 sets a truncate's `i_disksize` in one journal handle. Example `examples/osfs/semantics/data_truncate_size_exact.go`
  (indexed in `doc.go`; `data_resize_chunks.go` narrowed to `fallocate`), measured on C by
  `notes/axiom-review/fs-config/trunc-size.sh` (40 power losses, every size a target) and by the reviewer (a mix with
  appends, 40 more). Test `Tests.crash_trunc_size_exact`. It removes behaviours only: no proof constructing a crash
  broke but the tests' witnesses (`crashFile_of` takes the new clause, by default from `sz = f.size`/`f.sizeLo`).
* **`dbOpts`' producer**: `storage.OpenBackend.spec`'s post (an axiom) gains `⌜cfg.UnsafeNoFsync' = false⌝ -∗
  backend.dbOpts γ.db`; `dbOpts` moved to `backend/DbOpts.lean` (importable). Not yet in `OpenSnapshotBackend`'s spec
  (the snapshot install's reopen): for T7.
* **`dbCrashKeep_close`** now also takes (and gives back) a live write transaction begun at `Dn`, any pending changes
  (`wView Dn S G`; fifth review: suspect without it; sixth: survives, and proposed `wView` over `wr Dn` for defrag).
* Reviews: fifth (whole final set: no refutation, `_close` suspect, fixed) and sixth (`_close`: survives), in
  `notes/axiom-review/c-i1-bbolt-crash.md`. Final C-I1: `dbCrashKeep_new`, `_announce`, `_half`, `_clear`, `_close`,
  `dbCrash`, over `dbOpts` (opaque, produced), `dbCrashKeep` (opaque), `BoltCrashWhole` (defined).
* **Build**: a full VM `lake build` at `37a88a324f` (28052 jobs): every module built but one,
  `SpecPlan.Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.membership` (`failed to synthesize IsPkgInit …
  pkg_id.encoding.binary`), a generated SpecPlan package initializer that imports nothing this change touched (by
  inspection; not rebuilt at the base). Not done: interfaces (`etc/gen-interface.py etc/api/backend.txt`, new
  `DbOpts`) not regenerated (needs a local build); `etc/tcb-report.py --check` not run (axiom names unchanged).

## The WAL crash facts rest on `W1` (integration round 2, 2026-11-25, branch `etcd-safe-main/2026-11-24`)

**What rests on `W1`.** Every WAL crash fact `etcd_safe` uses comes from `walInv_crash` (the WAL tester's crash
lemma), which takes `W1 walCodec` as the crash premise (`etcdFsSem`'s `etcdCQ`, §Q2): C-I2's `walReadFacts σ` of a
crash image (`InvCrashImage.lean`, `bootstrapCrashContract.law`) and T5's `srvFiles`/`walReadFacts` at a new
generation (table above). None holds without it. `W1` today is the stronger statement of `W1.lean` (every frame a
fresh reader accepts after the crash came back as of one change); its target, the planned restatement
(`notes/wal-fsext-plan.md`, "W1's target"), is **no CRC-32C collision on the `Data` of a frame whose bytes under it
were zero**: the CRC does not cover a record's `Type`, so a frame written over another frame's stale bytes can come
back as a record of the stale type with a valid CRC (`nonissues/etcd-wal-record-type-outside-crc.md`), and only a
frame written over zeros is protected by the CRC alone. So under the target the proof also needs that **the WAL
writes every frame over bytes that are durably zero**.

**The torn-`Save` fix creates no frame over stale bytes** (checked by reading the fork at `e94f33b50`, `goose-lean-fmt1c-crashfixes`, the pin of branch `etcd-safe-main-pin/2026-11-24`; no
test written for this property). `WAL.Save` (`wal.go`, `Save`/`saveEntry`/`encodeState`) writes only by appending
through the encoder at its current offset: the entry records, then the state record (`encodeState`, the hard state
given, or `w.state` when it is empty and there are entries), then `sync` when `MustSync`, then `cut` past
`SegmentSizeBytes`; it never seeks back. The encoder's offset starts where `readAll` in write mode left it, and that
is where the fix moved the cut: the dropped entry records of an interrupted `Save` (`pending`) are cut with the tail
(`endOff = pendOff`, the CRC chain `pendCRC`), and the region from `endOff` on is zeroed (`fileutil.ZeroToEnd`:
`Truncate` then `Preallocate` to the old length) **and made durable** (`fileutil.Fdatasync`, `wal.go:723-729`)
before the encoder is created, and the directory synced (`wal.go:730-735`). So the next `Save`'s frames, written
where the torn `Save`'s entry frames were, lie over durable zeros, as the frames after an ordinary torn tail did
before the fix (the same zeroing, at `LastOffset`). The other places a frame is written: a new segment (`cut`: the
pipeline's `N.tmp`, created with `O_TRUNC` and preallocated, `file_pipeline.go:75-91`; its headers synced before
the rename to `.wal`, and appends after that sync over its preallocated zeros), and `Create` (a fresh temporary
directory, removed first if left; `DiscardUnsaved`, new in the fix, renames an unsaved WAL to that directory, which
`Create` removes). The one torn frame the WAL can still produce is `cut`'s `Truncate` at the file offset inside a
frame the page writer has not flushed: pre-existing, and excluded by `W1` as stated (`AsOfW.not_rz_window`, resize
zeros write no frame); under the target it is a frame over zeros too. Not checked here: `Repair` (not on the
member's path) and `ReleaseLockTo`'s renames (no frame written).

## 9b. T1's result (from branch `etcd-safe-walfix-p6`, numbered there §9) (2026-11-24, branch `etcd-safe-d6t1/2026-11-24`)

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
  name a WAL that a crash may still drop). The facts need the WAL's incarnation.
- 2026-11-25 (coordinator's decision): incarnations go in a follow-up **P6b** (`notes/wal-p6-handoff.md`,
  "P6b"), with the tester's torn-free `walImgs` (d6 plan's P6). **`DiscardUnsaved` stays unspecified in P6's
  landing**: P5's owner (`bootstrap`'s discard branch) needs its spec from P6b. P6 otherwise done:
  `issues/raft-commit-lost-with-entries-kept.md` `blocks-proof: yes` (the fork fix in `## Fix`); no interface
  step (removed on `lean`); ready for the full build, `tcb --check` and the gates.
- 2026-11-25 (coordinator-E, #50): P6 stays off `lean` (the one `etcd_safe` packet). Re-pinned to `e94f33b50`
  (`goose-lean-fmt1c-crashfixes`; its WAL identical to `2bd3048d7`'s): no WAL proof changes; `bootstrap`,
  `applySnapshot`, `OpenSnapshotBackend` bodies change (integration round 2). W1: the crash facts rest on it
  alone; no `Save` frame over stale bytes (`notes/wal-p6-handoff.md` START HERE).


### P8 progress (T5, branch `etcd-safe-p8`; `notes/wal-p8-handoff.md`)

- 2026-11-25 (session 1): the T5 lemmas are built. `storage/WalCrashRead.lean` proves I1-I4 of any read
  `walRead I` from `walIdxLe (2^61-1) I` and `walCommitLe I`, and that both conditions pass to prefixes.
  `storage/wal/CrashS.lean` adds the crash view with whole operations (`walCrashWalS`, `walImgS`) and its keep
  lemma, plus **`walInv_crashS.law`** (statement only). `storage/WalRecsCrash.lean` adds `walFilesC` and
  `walFilesC_crash`. `etcdserver/SrvCrash.lean` adds `walReadFacts_of_read`/`_of_take`, `srvFilesC` and
  `srvFiles_srvFilesC`. No axiom and no `sorry`.
  Three proposals to T2/T4 are in the handoff: the crash image takes `srvFilesC`, because a crash keeps the
  abstract synced mark; T2's crash callback returns `j` and a wand from `walRead … = some σ`; and T2's
  invariant keeps `walIdxLe`/`walCommitLeFrom`.
  One P6 change discharges the law: `crashTo_start`/`CrashGood`/`walCrash_pure` return `walImgS`, which
  they already construct.
- 2026-11-25 (session 2): the coordinator's decisions (1)-(3) are done as commits on `etcd-safe-p8`. (1)
  `8244ae66c1`+`1dce32d84a`: `walCrashWal` is over `walStCrashS`, so `walInv_crash` gives whole-operation
  images and `walInv_crashS.law` is gone (pushed alone first, for P6b). (2) `cb9d0ce180`: `srvFilesC` in
  `srvCrashImageAt`, `bootstrapCrashContract` and C-I2 (copies of `etcd-safe-crash`'s files). (3)
  `64aa0b94eb`: T2's crash law over `walRecsH_crash`, with `HistReadOk` (per-prefix `walCommitLe`) in
  `rnDurBodyK` and `walReadFacts σ` in the post (copies of `etcd-safe-d6t2`'s files). All of it builds, with
  no axiom and no `sorry`. Left for T2: maintain `HistReadOk` in its steps and at allocation.
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

**T6, round 4 checkpoint (P7, 2026-11-25).** The coordinator took (b) for gap 1: no spine durability in
`snapDirOwn`; the law takes `lookupH R V' sd = some (.dir J)` (and the persistent `snapDirKept`) as T7's
obligation (Go: `TouchDirAll`'s parent syncs). Gaps 2 and 3 and simplifications 4-6 as above (3 recorded as
`nonissues/etcd-snapdb-removed-before-dirsync.md`). `snapDir_crash_law_holds` proved
(`etcdserver/SnapDirCrash.lean`); `bootFs.touchMember.law` untouched.

**2026-11-24, the leader-completeness law: statement and proof route (nothing written in Lean yet).**

*Use.* `rnReplayJob_of_history` (`ReplayJob.lean`) takes, at the `Ready` that hands the payload (durable
state `S` after its `Save`, `rt` its hard state's term, `S.term = rt` when the hard state is non-empty):
`□ ∀ sm, ⌜sm.msg.Type' = MsgSnap ∧ sm.msg.Term' = rt ∧ n < |a0|⌝ -∗ sentMsg γ.node.cl N γ.id sm -∗
⌜DurAgrees S (a0.map toLE)⌝`, with `a0` committed before the restart (`srvRLogLb γ.srv a0`). The
`raftNode.start` side holds `raftState γ.node.cl γ.id S` (exclusive) at that point and must make this
persistent implication before giving `S` up.

*Statement (raft API, `Spec/go_etcd_io/raft/v3/Api.lean`, proved in `InvNode.lean`).* Roughly:
`raftState γ id S ⊢ raftState γ id S ∗ □ (∀ l, isCommittedLogLb γ l -∗ snapshotLeader γ id S.term -∗
⌜DurAgrees S l⌝)`, with `l` committed **before** the witness is made (a committed log that grows later
in a higher term can overwrite `S`'s uncommitted tail, so the law must take the commit witness at the
`raftState`'s time, e.g. as a hypothesis of the persistent implication's construction:
`raftState γ id S ∗ isCommittedLogLb γ l ⊢ raftState γ id S ∗ □ (snapshotLeader γ id S.term -∗
⌜DurAgrees S l⌝)`). `sentMsg_localSnapshotLeader` turns the sent `MsgSnap` into `snapshotLeader γ id rt`.

*Why it is true.* A node with `S.term = T` that leads `T` was a candidate at `T` (a follower at `T`
cannot campaign in `T`): its log from its campaign on only grows during `T`, so `S`'s log extends the
campaign log `F0` of `isCamp γ id T F0` (or is it). Leader Completeness (`Protocol/LeaderCompleteness.lean`:
`lc_core`, for entries committed in terms `< T`; `cq_agree` for the same term) puts every entry committed
before `T` in any full log with records that reaches `F0`'s last entry; with equal terms at an index,
the logs agree there (log matching over records, `full_match`).

*What the proof needs from the ghost state (to find or add, in `Protocol/GhostState.lean`):*
(i) from `ownDurGhost γ id S` (`durPers`) and `isLeader γ id S.term`: `S`'s log reaches the last entry of
`id`'s campaign log for `S.term` (the durable log at the campaign, and append-only while the term lasts:
the durable ghost's history at the term); (ii) `logRecs γ base0` of `S`'s full log (records, from
`durPers`); (iii) `isCommittedLogLb γ l` as commit-quorum facts `cq γ t n F` at terms `≤ T` (the
`reCommit` authority's justification, `raftCommitInv`); (iv) the votes table (`votesTbl`) inside the
invariant (`lc_core` takes it), so the law is a view shift opening the cluster invariant (`↑N ⊆ E`).

*Scope.* A raft-proof task: (i) is the open part. If the durable ghost keeps no per-term history
linking `S` to the campaign, it has to be added to `durPers` and kept by every `Ready`'s *enter*
(`StepGhost`), which reaches raft's step proofs. Estimate: several hundred lines in the protocol
layer, plus the API statement and its interface (`etc/gen-interface.py etc/api/raft.txt`), the RaftTla
copies (`etc/gen-raft-tla.py`) and, if `RaftNoAx`'s closure reaches `InvNode`, `etc/copy-part.py`. Not
started in this session: its context is spent on scoping (items 1-4 above).

**2026-11-24, the leader-completeness law: item (i) answered, and the stated form is false (nothing
written in Lean).**

*(i): no.* `durPers γ id S E` relates `S`'s log to nothing of `id`'s campaign: `E.camps` enters only as
a term bound (`∀ T, camps T isSome → T ≤ S.term`), the vote-time logs (`E.vlogs`) only to the
acknowledgements' histories, `klOkD` gives the term's winner without its log, `commitIn`/`isCommitted`
only bound `S`'s committed prefix. With `isLeader γ id S.term` nothing says `S`'s full log reaches the
last entry of `F0` (`isCamp γ id S.term F0`). So a campaign link has to be added to `durPers` (below).

*The stated form is false.* `raftState γ id S ∗ isCommittedLogLb γ l ⊢ raftState γ id S ∗ □
(snapshotLeader γ id S.term -∗ ⌜DurAgrees S l⌝)`, witness at `raftState`'s time: a leader commits
entries of its own term before it persists them (raft v3.7: its own `MsgAppResp` waits in
`msgsAfterAppend` until its storage append, `raft.go:855-863`, so two followers' acks commit an entry in
a 3-voter cluster), and `node.run` steps those acks while a `Ready` is pending. Run: `id` campaigns at
`T`; the `Ready` with hard-state term `T` and log `F0` is entered (`raftState γ id S`, `S.term = T`,
`S`'s log `F0`); `id` wins, appends `e` at `n = |F0|+1`, sends the `MsgApp`s with the next `Ready`; the
followers ack; `id` commits `e` before that `Ready` is entered. Now `isCommittedLogLb γ l` with
`l[n-1] = e`, `raftState γ id S` still, `snapshotLeader γ id T`, and `S`'s log ends at `n-1`:
`DurAgrees S l` is false. Leader completeness covers only entries committed at terms **below** `T`
(`lc_core`'s `t < T`; for `t = T`, `cq_agree` compares two leader logs, and `S`'s is not one that
contains the commit).

*What the server's use has.* `rnReplayJob_of_history`'s `a0` was committed **before the restart**, and
`rt` is a term this node leads **after** it, so `a0`'s certificates are at terms the node cannot lead
any more. A sound pair of laws (to decide; not started):

- (L1, at the witness) `raftState γ id S0 ∗ isCommittedLogLb γ l ⊢ |={E}=> raftState γ id S0 ∗
  cmtBefore γ id S0.term l`, `cmtBefore` sealed and persistent: `l` is a prefix of a commit quorum's
  log `cq γ t n G` (or within the bootstrap log), and every campaign of `id` existing now is at a term
  `≤ S0.term` (the camp fragments are minted only at *enter*, so `ghostMapAuth γc ½ E.camps` bounds
  them).
- (L2) `cmtBefore γ id T0 l ∗ raftState γ id S ∗ snapshotLeader γ id S.term ∗ ⌜T0 < S.term⌝ ⊢
  |={E}=> raftState γ id S ∗ ⌜DurAgrees S l⌝` (raft-side: `DurAgrees` is the server's, so restated over
  `plogTermAt S.base S.ents`).

L2's proof: `t < T` is `lc_core` plus `full_match`, given (i'); `t = T` is excluded by L1's campaign
bound (`T`'s leader is `id`, `isLeader_unique`, whose campaign at `T > T0` did not exist at the
witness); **`t > T` needs a new protocol lemma**: a commit quorum at `t` existing before `id`'s
campaign at `T < t` excludes `id` winning `T` (a voter of both acked `(t, n)` before voting at `T`;
its event history is sorted by term, `EvsOk`/`voteEv`), which no existing lemma states (`tbl_voter` and
`lc_core` take `t < T` only). The server must also supply `T0 < rt` (its restart's durable term below
the term it leads after the restart): a third fact, or L1's campaign bound read with a
`snapshotLeader` obtained later.

(i') The campaign link: a `durPers` conjunct `∀ F0 k, E.camps !! S.term = some (F0, k) → F0 <+: fp ++
S.ents` (or: `S`'s full log has `F0`'s last entry), kept by every *enter* (`cut_durPers`,
`Protocol/Enter.lean`: the cut's log is the node's in-memory log, which for a candidate or leader of
its term extends its campaign log, a volatile-side fact to find in `ownRaftGhost` or add), by
`durPers_rebase`, the restart (`raft_restart`) and the allocation (`RaftState.init`).

*Estimate.* (i') a few hundred lines in `Protocol/GhostState.lean`/`Enter.lean` (one `durPers`
conjunct reaches every proof that rebuilds `durPers`), the `t > T` lemma a few hundred in
`Protocol/LeaderCompleteness.lean`, L1/L2 with sealing in a defs module beside `InvNode` (as
`DurableLogView.lean`), plus the interface, RaftTla copies and RaftNoAx copies. Needs a decision on
the form (L1/L2, and how the server gets `T0 < rt`) before writing it.

Checkpoint 2026-11-24: leader-completeness law stopped at the design (above); no Lean changed; last
green build still `fec7d8cf82`.

**2026-11-24, L1/L2 approved; stopped again before Lean, on `T0 < rt` (the approval's stop condition).**

*`T0 < rt` cannot come from L1's campaign bound.* `snapshotLeader γ id rt` (`isLeader`) and
`sentMsg … sm` are persistent, so they hold for a term `id` led in an *earlier lifetime*, and the
server's `rnReplayJob` quantifies over every sent `MsgSnap` at `rt`, old ones included. With `rt = T0`
L2 is false: `id` leads `rt`, commits `e` through the followers before saving it (the run above),
crashes; it restarts with `S0` (`S0.term = rt`, no `e`); L1 is taken there (`T0 = rt`; `e`'s
certificate is at `t = rt` with leader `id`, and `t ≤ T0` holds); `S = S0`, `snapshotLeader γ id rt`
from before the crash, `DurAgrees S l` false. So L2 needs `T0 < S.term` from outside: either the server
narrows `rnReplayJob` to snapshots sent in the current lifetime and gets `rt > T0` from that, or raft
gives a lifetime-scoped leadership fact (a third law). Decision needed; nothing is written.

*What the rest needs (read off the code; for whoever continues).*

(A) The campaign link. A pure `E.camps` link is false (a candidate that loses `T` becomes a follower at
`T` and the winner's `MsgApp` can cut its campaign log), and a leader can become a follower at its own
term (CheckQuorum step-down, `becomeFollower(r.Term, None)`; and every restart). Proposed:
`campLink γ id camps T F := ∀ F0 k, ⌜camps !! T = some (F0, k)⌝ -∗ ⌜F0 <+: F⌝ ∨ ∃ L, isLeader γ L T ∗ ⌜L ≠ id⌝`.
- `campOwn` (`GhostState.lean:585`): the follower case becomes `campLink γ id camps s.term F` (today
  `True`); the leader case adds `⌜∃ k, camps !! s.term = some (F0, k)⌝` (true at the win,
  `Refinement.lean:937-979`, where `F0` is the candidate's own map entry).
- Maintenance: same-term log changes of a follower come from messages with `m.src ≠ id` and
  `isLeader m.src m.term` (`step_app_accept`, `snap_restore`, `snap_fastfwd`, `heartbeat` already
  take `m.src ≠ id`), giving the right disjunct; a term change leaves no camp at the new term
  (`Hcamps_ok`); a leader stepping down keeps `F0 <+: F`. Sites: `Hcown` in `Refinement.lean` (~10),
  `StepGhost.lean` (~8), plus every step that frames `Hcown` across a follower's log change.
- `durPers` gets `campLink γ id E.camps S.term (fp ++ S.ents)`: `cut_durPers` (`Enter.lean:372`, from
  `campOwn` at the cut's virtual maps), `durPers_rebase` (same full log), the restart (`Enter.lean`
  ~1566/1882: the follower's `campOwn` from it), `durPers_init` (`Facts.lean:799`, empty map).
- At L2: `isLeader γ id T` gives `isCampK γ id T F0 k`; the fragment against `raftState`'s half of the
  camps authority (`durShares`) gives `E.camps !! T = some (F0, k)`; the right disjunct contradicts
  `isLeader_unique`. So `F0 <+: fp ++ S.ents`.

(B) The `t > T` exclusion. A voter `v` of both the commit quorum (ack `(t, n)`, minted before the
witness) and `id`'s winning quorum at `T < t` (vote via `votesTbl_just`). Needed changes:
- `voteEv` carries `⌜EvSorted (L0 ++ [Aev.vote T d F])⌝` (as `ackEv` does), from `EvsOk` at *enter*.
  Then `ackEv`'s `La` and the vote's prefix are comparable (`mono_list_lb_valid`) and sorting puts
  the vote event in `La`.
- `EvsOk` gets a vote clause (`Aev.vote T d F ∈ evs → (voted !! T).isSome`), and `ackEv` carries
  `□ ∀ T' d F, ⌜Aev.vote T' d F ∈ La⌝ → ∃ c, isVote γ v T' c`, minted at *enter* from `durFrags`.
- `cmtBefore` (L1) then records, for the certificate's quorum, `∃ c, isVote γ v T' c ∗ ⌜c = id → T' ≤ T0⌝`
  for every vote event of each acknowledgement's `La`, proved at the witness (`votesTbl_just` →
  `isCamp γ id T'` → `raftState`'s camps authority → `T' ≤ T0`). At L2 the vote at `T` for `id` agrees
  with it (fragments of `v`'s vote map), so `T ≤ T0 < T`.

(C) L1 also needs `isCommittedLogLb γ l` back to a raft certificate: `isCommitted γ L` with
`strip L = l`, then `cq γ t n G` covering `|L|` (or the bootstrap log), from `raftCommitInv`.
(D) L2: `t < T` by `lc_core` + `full_match` on `fp ++ S.ents` (reaching `F0`'s last entry,
`prefix_camp_last`); `t = T` by `isLeader_unique` and `cmtBefore`'s `c = id → t ≤ T0`; `t > T` by (B).

*Size.* (A) and (B) both change step-level invariants (`campOwn`, `voteEv`, `ackEv`, `EvsOk`), which
reach `Refinement.lean` (5800 lines) and `StepGhost.lean`/`Enter.lean`: about 1-2k lines and several
VM builds of the raft tree, then (C)-(D) and the API, interface and copies.

Checkpoint 2026-11-24: no Lean changed; waiting on the `T0 < rt` decision; last green build `fec7d8cf82`.

**2026-11-24, L1/L2 implementation, round 1: steps (A), (B), (C) written; L2's `t > T` case is
not what (B) gives in raft's dynamic mode.**

*Written (Lean).*
- (A) `campLink γ id camps T F` (`Protocol/GhostState.lean`: `⌜∀ F0 k, camps !! T = some (F0, k) →
  F0 <+: F⌝ ∨ ∃ L, isLeader γ L T ∗ ⌜L ≠ id⌝`, with `campLink_none`/`_prefix`/`_leader`/`_cand`). Not
  inside `campOwn` but a conjunct of its own of `ownLogGhost` (`"#Hclink"`, at `W.camps`, `s.term`,
  `fp ++ s.log`, every role), so that a leader stepping down keeps it with no new `campOwn` fact; and
  the last conjunct of `durPers` (at `E.camps`, `S.term`, `fp ++ S.ents`). Kept by: `ownLogGhost_upd`
  (its log-change obligation gains a last conjunct: the full log extended, or a higher term, or
  `∃ L ≠ id, isLeader L s.term`; `ownLogGhost_mono'` gives the first, `step_app_accept` and
  `step_snap_restore` the third from the message's `isLeader m.src`), `ownLogGhost_stepDown`, the
  campaign (`campLink_cand`), the win and `pappend` (prefix), `cut_durPers`, `durPers_rebase` (its
  output gains the link), the restarts (both), `durPers_init`.
- (B) `EvsOk` gains a fourth clause (every vote event's term in `voted`); `AcksEvs` (Enter) is now
  `EvsOk`'s last two clauses; `voteEv` carries `⌜EvSorted (L0 ++ [vote])⌝`; `ackEv` carries
  `∀ T d F, vote T d F ∈ L → ∃ c, isVote γ v T c` (minted in `mint_one` from `durFrags`'s vote
  fragments). `ownEvs_ack`/`ownEvs_vote` (unused) deleted.
- (C) `api_committed_cert` (`InvApi.lean`): `clusterInv ∗ isCommittedLogLb γ l ={E}=∗ ⌜l = []⌝ ∨ ∃ P,
  ⌜l <+: strip P ∧ IdxOk P⌝ ∗ isCommitted γ.raft P ∗ (boot log ∨ ∃ t n G ldr, cq γ.raft t n G ∗
  ⌜P = G.take n⌝ ∗ isLeader γ.raft ldr t)`.

*The gap: (B) does not close `t > T` when the cluster is dynamic.* (B)'s argument takes a voter `v` in
both the commit quorum at `t` and `id`'s winning quorum at `T`. In the static mode `CfgAt.overlap`
gives one. In the dynamic mode (`γ.reDyn = some _`, the unified API's clusters, the server's) the two
quorums are of the configurations at `G.take a` and `F0.take kw`, which overlap only when their conf
counts differ by at most one (`CfgAt.overlap_adj`); `lc_core` needs `lc_far_newer`/`lc_far_older` and
its induction for the far cases. The mirror for `t > T`:
- campaign config ≥ 2 newer: `campDyn`'s witnesses are at terms ≤ `T < t`, so `lc_core` at `t` puts
  their conf entries in `G` past `a`: two of them, against `ConfI1 G a` (no timing needed);
- commit config ≥ 2 newer: `cqDyn`'s witnesses (certs at `t' ≤ t`) of two conf entries past `kw`:
  `t' < T` → `lc_core` puts them in `F0` past `kw`, against the campaign's I1; `t' = T` → a cert of
  `id` at `T` that existed at the witness, so `T ≤ T0`; `T < t' ≤ t` → the same argument again, by
  induction on the witness's `a`.
So the timing facts (every cert in the `cqAt` tree: its leader is not `id` or its term is `≤ T0`;
every ack of its quorum: the vote events before it are for `(T', c)` with `c = id → T' ≤ T0`) are
needed for the whole witness tree, not only the top certificate: `cmtBefore` must be a recursive
predicate over `cqAt`'s structure (as `cqAt` is, `termination_by` the config index), proved at L1 by
the same recursion, and L2's `t > T` case is a new theorem of `lc_core`'s size. Estimate 600-1000
lines in `Protocol/LeaderCompleteness.lean` plus the recursive `cmtBefore`.

A cheaper alternative, if the server can discharge it: L2 with a premise that every committed
prefix has one membership (the server's `srv_confAt_simple`), e.g. `□ ∀ k m, confAt γ k m -∗ ⌜m =
m0⌝`; then both quorums are of `m0` and (B)'s single-voter argument works. It needs a bridge from
the API's `confAt` (`decFold`) to the internal `CfgAt` of `G.take a`/`F0.take kw`. Decision needed.

*Built (VM):* the protocol layer, `InvApi`, the modules that unfold the changed definitions
(`DurableLogView`, `InvRawnode`, `CommitWit`, `Term0`, `TraceSimFacts`, `TracedRaftStepPropBundle`)
and raft's `Link`, `Linked`, `Results`: 3475 jobs, green. RaftTla copies regenerated
(`etc/gen-raft-tla.py`, 8 written), RaftNoAx/KvNet copies (`etc/copy-part.py`); `etc/tier-check.py
--check` ok. No axiom, no `sorry`, no spec or top-level statement changed.

Not written: `cmtBefore`, L1, L2, the API laws, the T0-lifetime law ("a term this node leads in its
current lifetime is > its restart term": it falls out of the same camps bound as L1's, `durPers`'s
`camps T isSome → T ≤ S.term` at the restart state, plus `campLink`; not yet stated).

*Next lemma (whichever option is chosen), exact statement:* L1,
`raftState γ id S0 ∗ isCluster γ N ∗ isCommittedLogLb γ l ⊢ |={E}=> raftState γ id S0 ∗ cmtBefore γ id S0.term l`
(`↑N ⊆ E`), from `api_committed_cert` and, for the certificate's leader `ldr`, `isCamp γ ldr t F0`
(`cq_base`, `leadFull_camp`) against `raftState`'s half of the camps authority (`durShares`):
`ldr = id → t ≤ S0.term`.

**2026-11-24, L1 and L2 proved (`Proof/go_etcd_io/raft/v3/LeaderCompleteLaw.lean`, exposed in `Api.lean`,
listed in `etc/api/raft.txt`).** No axiom, no `sorry`, no spec or top-level statement changed.

- `cmtBefore γ id T0 l` (sealed, persistent; body `cmtBeforeR` over raft's names): `l = []`, or
  `l <+: strip γ.reBoot`, or `l <+: strip (G.take n)` for a commit certificate `cqAt γ t n G a c q`
  (`0 < n`) whose leader `ldr` has `ldr = id → t ≤ T0`, and every quorum member's acknowledgement at `t`
  has a recorded history (`ackBefore`: a sorted event list holding the ack, every vote event in it for
  some `c`, with `c = id → T' ≤ T0`).
- `confFixed γ E m0 := □ ∀ l, isCommittedLogLb γ l ={E}=∗ confAt γ l.length m0` (the fixed-membership
  premise; the server discharges it with `srv_confAt_simple γ l l.length le_refl E ..`).
- `durLogAgrees S l` (raft's copy of the server's `DurAgrees`, the same body).
- **L1** `raftState_cmtBefore (γ N E) (HE : ↑N ⊆ E) id S0 l :
  raftState γ id S0 ∗ isCluster γ N ∗ isCommittedLogLb γ l ⊢ |={E}=> raftState γ id S0 ∗ cmtBefore γ id S0.term l`
  (from `api_committed_cert`; the leader's and the votes' timing from `durPers`'s camps bound against
  `durShares`'s camps authority; the votes through the vote table, threaded with `bigSepM_fupd_thread`).
- **L2** `raftState_cmtBefore_agree (γ N E) (HE : ↑N ⊆ E) m0 id T0 S l : uint.Z T0 < uint.Z S.term →
  isCluster γ N ∗ confFixed γ E m0 ∗ cmtBefore γ id T0 l ∗ raftState γ id S ∗ snapshotLeader γ id S.term ⊢
  |={E}=> raftState γ id S ∗ ⌜durLogAgrees S l⌝`. `campLink` gives `F0 <+: fp ++ S.ents` (`id`'s
  campaign log at `S.term`); then `t < T` by `lc_core` + `full_match`, `t = T` by `isLeader_unique` and the
  mark, `t > T` by a voter of both quorums (`quorums_meet`: static `CfgAt.overlap`; dynamic, both
  configurations are `cfgOf m0` by `confFixed` + `confAt_agree`, then `D.adj` at one prefix), whose vote
  at `T` for `id` is in the marked history (`ev_vote_mem`, sorting) against `T0 < T`. Re-checked against
  the commit-before-save run: it needs `T0 = rt`, which the premise excludes.

**The lifetime law (task 3): not written; it is not derivable over the current API.** Every leadership
fact the API has (`snapshotLeader`, `sentMsg`, `isLeader`) is persistent and carries no lifetime: after a
restart at `S0.term = T0` the node still has `snapshotLeader γ id T0` and its old `sentMsg` MsgSnaps at
`T0`, and `raftState` does not hold the node's role. `durPers`'s camps bound and `campLink` say that a
campaign the node *makes* after the mark is at a term `> T0`, but nothing the server receives tells a
current-lifetime MsgSnap from an old one. What it needs is a raft-side fact on the messages a `Ready`
hands out (e.g. with each MsgSnap at `rt`, a persistent `ledSince γ id T0 rt` with `T0 < rt`, where `T0`
is the restart mark), i.e. a change to `node.Ready`/`isReadyChan_recvAu`'s post (and `RestartNode`'s, for
the mark), which this task may not touch. Decision needed.

**Left for the server:** (1) narrow `rnReplayJob` (`InvRaftNode.lean:2140`) to MsgSnaps with `T0 < rt`
(given the lifetime fact above), then discharge `rnReplayJob_of_history`'s premise with L2 (L1 taken at
`raftNode.start`'s restart with `l = a0`); (2) discharge `confFixed` by `srv_confAt_simple`
(`srvRaftLogInv` is persistent: `iintro !> %l #Hl; iapply srv_confAt_simple γ l l.length (Nat.le_refl _) E hC hL $$ Hinv Hl`).

*Built (VM, `25c7bb088e`):* `LeaderCompleteLaw`; raft's `Link`, `Linked`, `Results`, `Api`; the server's
`ReplayJob`; and the `RaftTla`, `RaftNoAx` and `KvNet` copies of `LeaderCompleteLaw`, `Api` and `Link`:
7626 jobs, green. `etc/gen-raft-tla.py --check`, `etc/copy-part.py --check`, `etc/tier-check.py --check`
and `etc/api-check.py etc/api/raft.txt --check` pass. This branch has no `interface/` directory.
Not rebuilt: the rest of `Api`'s 2675 importers. They gain one import, and none of the new names
clashes with an existing one (checked by grep).

Checkpoint 2026-11-24: L1 and L2 done. **Next statement:** the lifetime fact (above), which needs a
decision on changing `node.Ready`'s post. Then the server's `rnReplayJob` narrowing.

**2026-11-24, T4 round 5: the lifetime law (decision: change the API's posts).** No axiom, no `sorry`, no
new premise on any API spec.

*Raft side (built, VM).*
- The attachment's term floor: `StorNames.t0 : w64` (default `0`; `Defs.lean`), set by `RestartNode` to
  the stored term `σ.hs.Term'` (in the `storKeyNames` tuple too). Raft's queue invariant gets
  `LifeOk s l` as `XfOk`'s last conjunct (`InvRaftPhys.lean`): `t0 ≤ s.term`, `t0 < s.term` at a leader
  or candidate, and `t0 < m.Term` for every queued `MsgSnap`. Kept by: `raft.wp_store_stateC`'s new
  premise `Hrt0` (leader/candidate past `t0`: `becomeCandidate` from `ownRaftPhysC_t0` before its
  `reset(term+1)`; `becomeLeader`'s new spec premise `uint.Z s.gh.sn.t0 < uint.Z s.term`, which
  `stepCandidate` gets from its candidate role), `send`'s `SendOk` `MsgSnap` clause (new last conjunct
  `t0 < s.term`; `maybeSendSnapshot`'s new premise, which `maybeSendAppend` gets from its leader role),
  the queue pushes (`Hxq`'s new last conjunct), `XfOk.term_le` (term raised), `XfOk.drain` (a `Ready`),
  and `newRaft`/`NewRawNode`/`setupNode`'s new premise `uint.Z sn.t0 ≤ uint.Z hs.Term'` (callers:
  `RestartNode` `le_refl`, `StartNode` `0 ≤ 0`).
- `handoutOrigins` (`InvRawnode.lean`) gains `⌜∀ q ∈ ms, MsgSnap → uint.Z sn.t0 < uint.Z q.st.msg.Term'⌝`
  (from `LifeOk` at the hand-out), so `readyGot`'s statement is unchanged: the fact is inside the sealed
  `readySnapSources` it already gives.
- **The mark** (`InvNode.lean`, sealed, persistent): `nodeStartTerm (n : NodeH) (T0 : w64)`, body
  `⌜n.names.sn.t0 = T0⌝`; `nodeStartTerm_agree`.
- **The lifetime fact** (`InvNodeRule.lean`): `readySnapSources_startTerm γ n id term ms bound installed T0 :
  readySnapSources γ n id term ms bound installed ∗ nodeStartTerm n T0 ⊢
  ⌜∀ q ∈ ms, q.st.msg.Type' = MsgSnap → uint.Z T0 < uint.Z q.st.msg.Term'⌝`.
- **Posts changed:** `RestartNode.spec` only: `nodeStartTerm n S.term` after `nodeArm n γ x` (clients'
  patterns gain one slot: kv, kvreconf (2), kvdurable, kvnet (KvNet's own `StartNode.lean`), the
  server's `newRaftNode`). `StartNode.spec` unchanged (a first start's `rnReplayJob` is vacuous,
  `a0 = []`). Internal specs changed: `raft.send` (`SendOk`), `raft.maybeSendSnapshot`,
  `raft.becomeLeader` (and its untraced/traced wrappers), `newRaft`, `NewRawNode`, `setupNode`.
- RaftNoAx's own `newRaft.lean` patched by hand (the same two edits).

*Server side (written; see the build line below).*
- `rnBootPost`'s restart arm gives `nodeStartTerm n S.term`; `rnRestartOk`'s restart disjunct carries
  `nodeStartTerm γ.nl γ.t0` (`NodeStartLinked`: `γw.t0 = σ.hs.Term' = S.term`, `StorageHolds`).
- `rnReplayJob` narrowed to this run's `MsgSnap`s: its premise takes `rnMessageSource γ ⟨ml, sm⟩` (which
  `rnSnapMsg` carries; `applyAll` passes `%m Hsrc`). `ReplayJob.lean`: `rnReplayJob_lifetime`
  (`rnRestartOk γ ∗ rnMessageSource γ ⟨ml, sm⟩ ⊢ ⌜MsgSnap → a0 ≠ [] → uint.Z γ.t0 < uint.Z sm.msg.Term'⌝`),
  and `rnReplayJob_of_history` now takes `rnRestartOk γ` and its premise only at `uint.Z γ.t0 < uint.Z rt`.
- `srv_confFixed` (`ReplayJob.lean`): `srvRaftLogInv γ ⊢ confFixed γ.raft.cl E (Membership.simple γ.raft.cfg)`
  for `↑srvConfN ⊆ E`, `↑srvLogN ⊆ E`.

*Not done: `rnReplayJob_of_history`'s premise from L2.* Its premise is a persistent wand returning a pure
fact (`□ ∀ sm, … -∗ sentMsg … sm -∗ ⌜DurAgrees S a0⌝`), but L2 (`raftState_cmtBefore_agree`) is an
update that needs the exclusive `raftState γ id S` (its camps authority identifies the leader's campaign
record). So L2 cannot be fed into that premise as stated. Two ways: (a) a raft law of the wand form
`raftState γ id S ∗ … ⊢ |={E}=> raftState γ id S ∗ □ (snapshotLeader γ id S.term -∗ ⌜durLogAgrees S l⌝)`
(needs, from the authority at the update, a persistent fragment of the camps entry at `S.term`, and for
an absent entry a persistent "no campaign at `S.term`" fact: a change to `durShares`'s camps ghost);
or (b) the producer (`raftNode.start`'s snapshot hand-off) applies L2 at its update with a
`snapshotLeader` it obtains first, which needs the `MsgSnap` in hand, i.e. reorder the job's
quantifier. Decision needed (raft-proof work for (a)).

*Built (VM, `e3572c99c0`):* raft's `Link`, `Linked`, `Results`, `Api` (3474 jobs); the server's `Link` and
`ReplayJob`, kv/kvreconf/kvdurable `Link`, `RaftTla`'s raft `Link`, `RaftNoAx`'s raft and kvdurablenoax
`Link`, `KvNet`'s kvnet `Link` (13763 jobs); every module naming a changed name (`etc/importers.py
--uses` for `rnRestartOk`, `rnReplayJob`, `rnReplayJob_of_history`, `rnBootPost`, `RestartNode`,
`StorNames`, `XfOk`, `handoutOrigins`: 102 modules, plus `etcdstart.Restart` and `NewServerCrash`; 5495
jobs): all green. `etc/gen-raft-tla.py --check`, `etc/copy-part.py --check`, `etc/tier-check.py --check`,
`etc/api-check.py etc/api/raft.txt --check` pass. Not rebuilt: the rest of `Defs.lean`'s cone (9156
modules; `StorNames` gains a defaulted field, which only its two constructions and `storKeyNames_agree`
enumerate). `etc/tcb-report.py --check` not run (needs a local build).

*Left for `wp_proofC`:* step 1 (the snapshot payload's `rnReplayJob` by `rnReplayJob_of_history`) needs
the L2 bridge above; step 3 (raft's restart configuration point past the stored log: the other branch's
option D); steps 2, 4, 5 after them; `NewServerCrash.lean`'s `sorry` (the case `σ.commit < i`) stays.

Checkpoint 2026-11-24: the lifetime law proved and exposed (`e3572c99c0`); next decision: the L2
bridge's form (a) or (b) above.

**2026-11-24, decision: option (b) for the L2 bridge (L2 applied at the producer, not a raft ghost
change). Not started; the next agent's starting point.**

*Where the `MsgSnap` is in hand.* Not at `rnApSnap`'s production (`raftNode.start`'s snapshot hand-off):
the payload's `rnReplayJob` quantifies over `MsgSnap`s that reach `applyAll` later through `msgSnapC`,
from this `Ready` or a later one. The raft loop has the `MsgSnap` in hand where `processMessages` puts it
on `msgSnapC` (`rnSnapMsg`, built from `rnRawMsgs` after the WAL `Save`, `rn_enter`), and there it holds
`raftState γ.node.cl γ.id S'` (the busy driver's durable state after the batch is entered). So (b) is:
1. At that point, for a `MsgSnap` `sm` of the `Ready` (`rnMessageSource`), with `nodeStartTerm γ.nl γ.t0`
   from `rnRestartOk` and `readySnapSources_startTerm` (`t0 < sm.term`), `sentMsg_localSnapshotLeader`
   (`snapshotLeader γ id sm.term`), and `sm.term = S'.term` (to check: the `Ready`'s hard-state term is
   the leader's term while it sends; a later step-down raises `S'.term`, then `snapshotLeader` is at an
   older term and L2 does not apply: that case must be shown unreachable at the merge, or the fact
   carried only when the terms agree), apply L2 `raftState_cmtBefore_agree` with `cmtBefore γ id t0 a0`
   (L1 at `raftNode.start`'s restart, `raftState_cmtBefore` with `l = srvLE … a0`, kept in the loop's
   persistent restart data next to `rnRestartOk`) and `confFixed` (`srv_confFixed`). Result:
   `⌜DurAgrees S' (a0.map toLE)⌝`.
2. Carry it in `rnSnapMsg` (a new pure conjunct `sm.msg.Term' = S'.term → DurAgrees S' a0` with `S'`
   existential), and change `rnReplayJob`'s premise to take that conjunct instead of
   `rnMessageSource`.
3. Open question that decides whether (b) works: `rnReplayJob_of_history` needs `replayRunsDescribe runs S n`
   for the **same** `S` as the `DurAgrees`; the payload's runs describe the durable state at the snapshot
   `Ready` (`S` = the snapshot at `k` plus `rd.Entries`), while step 1 gives `DurAgrees` at the `MsgSnap`'s
   `Ready`. Needed: both durable states agree on `(n, |a0|]`, i.e. log monotonicity of the node's durable
   log within a term between the two `Ready`s (a leader's log only grows), or produce the job at the
   merge from the `MsgSnap`'s own `S'`. If neither holds, (b) is blocked and option (a) is the fallback:
   report before starting it.

Next statement to write (`ReplayJob.lean`, server): `rnReplayJob_of_snapMsg` — from `rnRestartOk γ`, the
persistent L1 mark `cmtBefore γ.node.cl γ.id γ.t0 (srvLE γ.srv γ.a0)`, `srvRaftLogInv`, and
`raftState γ.node.cl γ.id S'` with `rnMessageSource γ ⟨ml, sm⟩`, `sentMsg … sm`, `sm.msg.Type' = MsgSnap`,
`sm.msg.Term' = S'.term`, `γ.a0 ≠ []`: `|={E}=> raftState … S' ∗ ⌜DurAgrees S' (γ.a0.map EntryModel.toLE)⌝`
(L2 instantiated; `↑srvClusterN ∪ ↑srvConfN ∪ ↑srvLogN ⊆ E`).

**2026-11-24, option (b): blocked; the S/S' question has no answer over raft's current API and ghost
state. No Lean changed; last green build `e3572c99c0`.**

*What the payload's job needs.* `rnReplayJob_of_history` needs `DurAgrees S_P a0` at the durable state
`S_P` the payload's runs describe: the state after the payload's own `Ready` `P` (`raftTerm = rt` is
`P`'s hard-state term). The `MsgSnap` at `rt` comes from a `Ready` `M` that can be before `P`, `P`
itself, or after `P` (the loop runs ahead of `applyAll`; `applyAll` merges any queued `MsgSnap` with
`m.Term == apply.raftTerm`). L2 holds only at a state `S` with `snapshotLeader γ id S.term` in hand.

*(1) Relating `S_P` and `S_M`: fails.* In Go, if `id` leads `rt` then at `P`'s hand-out `id` is already
a candidate or leader at `rt` (a node at term `rt` campaigns only at `rt + 1`), and from then on its log
only grows, so `S_P` and `S_M` agree below `|a0|`. None of this is visible from `raftState`: the server
sees each `Ready`'s entries, not the node's role, and a follower's durable entry at an index `≤ |a0|` can
change within a term (overwrite by the term's leader). Inside raft, `durPers` at `S_P` gives `campLink`
only for a campaign record that exists in the entered maps at `P` (`E_P.camps !! rt`). When it is `none`
(a follower at `rt` that never voted at `rt`), nothing in the ghost state stops a record at `rt` from being
added later: `PromFresh` only asks that the key be absent, and `durPers`'s camps bound allows `T ≤ S.term`.
The vote map has the same gap (`voted !! rt = none`). Ruling it out needs "no campaign record is ever
added at a term at or below a durable term that had none". That is a persistent fact about the future
(closing the camps map up to the durable term), which means new campaign ghost state in raft.
`EvSorted` and the term registry (`TermsOk`) do not provide it.
*(2) Moving the production site: fails alone.* The payload goes on `applyc` before the `Save` and before
*enter*, so `raftState` is still `S_{P-1}`. After *enter* (before the `notifyc` sends, which `applyAll`
receives before the merge), the loop holds `raftState S_P`. `notifyc`'s deposit can carry a pure fact made
there, so the job could be discharged from it. But L2 still needs `snapshotLeader γ id rt` at that point,
which exists only if `id` already leads `rt` at `P`. A payload of a candidate `Ready` that wins later is
the same gap as (1).
*(3) Server-side ghost state: fails.* A record per `MsgSnap` of `DurAgrees S_M` does not reach `S_P` (as
in (1)); the server cannot observe raft's camps.

*The same gap blocks every later step, not only the kept snapshot.* The batch `Ready`s keep `replayPending`
through `rnReplayState.appendEntries`. Its premise `above` (entries past `|a0|`) comes from `Ha0p`
(`rnRestartOk_a0_le`: `|a0| ≤ commit0`, `raftNode__start.lean:232`, `:1354`). Dropping `|A₀| ≤ σ.commit`
(the crash case) removes that, and after a crash the WAL's entries `≤ |a0|` can be stale (round 4,
step 3). So the crash window needs the history form (runs describe `S_P`, then L2 at `S_P`) for every
payload.

*Two ways forward (a decision for the lead; neither started):*
- (a) raft ghost: the camps map closed up to the durable term, i.e. a persistent "no campaign of `id` at
  `T`" for `T ≤ S.term` with no record. Then the law `raftState γ id S ⊢ |={E}=> raftState γ id S ∗
  □ (snapshotLeader γ id S.term -∗ ⌜durLogAgrees S l⌝)` holds, made at *enter* and deposited in
  `notifyc`. This is new campaign ghost state in raft, which this task excluded.
- (b') a fork change plus a raft law over the existing ghost state. In `raft.go`, set `ap.raftTerm` only
  on a `Ready` whose role is leader (`islead`), else `0`. A `MsgSnap` is then merged only with a leader
  `Ready`'s payload (liveness only: an unmerged `MsgSnap` is reported failed and resent). Raft's `Ready`
  post (`readyGot`/`readyLeaderMsgs`) gains `⌜roleAfter st.role ss = StateLeader⌝ -∗ snapshotLeader γ id
  (phsNext st.hardState h).Term'`. At a leader, `campOwn` already holds the `isCamp`; the win's certificate
  is `leadLogOwn`'s term record. Server: after *enter* of a leader `Ready`, L2 at `S_P` (with `t0 < rt`
  from `LifeOk`'s leader clause, to be exposed with it); `DurAgrees S_P a0` goes in `notifyc`'s deposit;
  the job reads it. The loop keeps `replayHistoryMatches runs S n` (runs describe the current durable
  state above the cursor) through `appendEntries`'s cut (`appendEntries_nonempty`'s `hcut`), the snapshot
  reset and `after`, in place of `replayPending`. The seed is the WAL's entries, which are `S_0`'s.
  Estimate: the fork change and its test, one raft `Ready` law, the loop's replay invariant reworked in
  `raftNode__start.lean` (2000 lines; three `Ready` arms) and `replaySeed_facts`, and `applyAll`'s two
  `notifyc` receives.

Checkpoint 2026-11-24: (b) blocked as above. **Next statement** (once (a) or (b') is chosen): for (b'),
raft's `readyLeaderMsgs` widened to `⌜roleAfter st.role ss = StateLeader⌝ -∗ readyMsgs γ N id ms ∗
snapshotLeader γ id (phsNext st.hardState h).Term' ∗ ⌜uint.Z n.names.sn.t0 < uint.Z (phsNext st.hardState
h).Term'⌝`. For (a), the raft law above.

**2026-11-24, option (a): the campaign map closed up to the durable term; `raftState_leadAgree` proved;
the replay job's premise in the law's form.** No axiom, no `sorry`, no new top-level premise, no Go change.

*The closure fact (raft, `Protocol/`).* A closure value on the existing campaign map, no new resource:
- `campNone := ([], W64 (2^64-1))` and `isCampNone γ c T := ∃ γc, ⌜γ.reCamp !! c = some γc⌝ ∗ T ↪[γc]□ campNone`
  (`Ghost.lean`, persistent): node `c`'s campaign map key `T` is closed, for good. `isCampNone_campK`:
  `isCampNone γ c T -∗ isCampK γ c T F k -∗ False` (a record's commit index is within its log;
  `campNone_ne`).
- A promise `Prom.close T` (`GhostState.lean`): fresh when the key is free, `promNeed` trivial, entering
  it inserts `campNone` (`mint_one`) and mints `isCampNone`; `durFrags`' camps part is `campFrag`
  (`isCampK ∨ (⌜x = campNone⌝ ∗ isCampNone)`).
- The cut closes the node's term's key when it has none (`Enter.lean`: `cutClose V πc s.term`, the
  pending list with `.close s.term` appended iff `(virt V πc).camps !! s.term = none`; `ownLogGhost_close`,
  `campOwn_close`, `campLink_close`). This is raft's fact: a node campaigns only at `term + 1`.
- `durPers γ id S E` gains a last conjunct `⌜uint.Z S.term = 0 ∨ (E.camps !! S.term).isSome⌝`
  (`cut_durPers` takes `(W.camps !! s.term).isSome`). With the map's fragments (persistent), the key of
  every durable term is final: a record or `campNone`.

*The law* (`LeaderCompleteLaw.lean`, exposed by `Api.lean`):
`raftState_leadAgree (γ N E) (HE : ↑N ⊆ E) m0 id T0 S l : uint.Z T0 < uint.Z S.term →
isCluster γ N ∗ confFixed γ E m0 ∗ cmtBefore γ id T0 l ∗ raftState γ id S ⊢
|={E}=> raftState γ id S ∗ □ (snapshotLeader γ id S.term ={E}=∗ ⌜durLogAgrees S l⌝)`.
It reads the key's fragment through the slot (`Enter.durShares_frags`); in the wand, a record is
the leader's campaign record (`isCampK_agree`) and `campLink` + `cmtBefore_core` (L2's core) give the
agreement; `campNone` refutes the leadership. **The wand is an update, not pure** (as the notes' form
had it): L2's core opens the vote table (`lc_core`) and the membership (`confFixed`) at the time the
leadership is shown, so no pure form is provable.

*Server (built only as far as noted below).* `rnReplayJob`'s conclusion is now `|={⊤}=> ∃ runs r, …`
(`applyAll` `imod`s it; `rnReplayState.job` `imodintro`s); `rnReplayJob_of_history`'s premise is
`□ ∀ sm, … -∗ sentMsg … sm ={⊤}=∗ ⌜DurAgrees S (a0.map toLE)⌝`; new `rnReplayJob_premise_of_lead`
(`ReplayJob.lean`): the law's wand at `S` with `S.term = rt` gives that premise
(`sentMsg_localSnapshotLeader`).

*Built (VM, raft at `efec220057`):* raft's `Link`, `Linked`, `Results`, `Api`, `DurableLogView`, the
protocol modules, `RaftTla`/`RaftNoAx` raft `Link`, `RaftNoAx` kvdurablenoax `Link`, `KvNet` kvnet
`Link`, the server `Link` (before the server edits): 13236 jobs, green. `gen-raft-tla --check`,
`copy-part --check`, `tier-check --check`, `api-check etc/api/raft.txt --check` pass.
*Built (VM, with the server edits):* the server's `Link` and `ReplayJob`: 9494 jobs, green.

*Not done (next, in order).* Nothing of `wp_proofC`'s steps closed yet; its `sorry`
(`NewServerCrash.lean:77`) stays.
1. **L1 at the restart.** In `raftNode.start` (restart arm, where `rnRestartOk`'s `nodeStartTerm γ.nl γ.t0`
   and `raftState γ.node.cl γ.id S0` with `S0.term = γ.t0` are in hand): `raftState_cmtBefore` with
   `l = γ.a0.map EntryModel.toLE` (its `isCommittedLogLb` from `srvRLogLb`; note `srvLE` prefixes `γ.pre`),
   kept as a persistent `cmtBefore γ.node.cl γ.id γ.t0 (γ.a0.map toLE)` in the loop's restart data.
2. **The law at each *enter*.** After `rn_enter`/`rn_enterS` (`raftNode__start.lean:721, :1540`), with
   `raftState … S'`: if `uint.Z γ.t0 < uint.Z S'.term`, `raftState_leadAgree` (with `srv_confFixed`) gives
   `□ (snapshotLeader … S'.term ={⊤}=∗ ⌜durLogAgrees S' (a0.map toLE)⌝)`.
3. **The deposit.** `rnApR` (batch) and the snapshot's `isNotify2` first-send deposit carry
   `∃ S, ⌜replayRunsDescribe runs S n ∧ S.term = rt⌝ ∗ (⌜t0 < rt⌝ -∗ law-wand at S)` for the payload's runs;
   the loop keeps `replayHistoryMatches runs S n` (runs describe the current durable state above the
   cursor) in place of `replayPending` through `appendEntries`' cut, the snapshot reset and `after`.
4. `rnReplayJob` then takes the deposit (received before the merge) instead of being a payload
   field; `applyAll` discharges it with `rnReplayJob_of_history` + `rnReplayJob_premise_of_lead`.
5. T4 round 4's steps (drop `|A₀| ≤ σ.commit`, step 1, step 2), the merge of
   `origin/raft-restart-confpoint/2026-11-24`, then `wp_proofC` and its Link entry.

Checkpoint 2026-11-24: raft (a) and the law done; server job in the law's form. **Next statement:** item 1,
`rnRestart_cmtBefore` (server, `ReplayJob.lean`): `rnRestartOk γ ∗ raftState γ.node.cl γ.id S0 ∗
⌜S0.term = γ.t0⌝ ∗ srvRaftLogInv … ∗ srvRLogLb γ.srv γ.a0 ⊢ |={⊤}=> raftState … S0 ∗ cmtBefore γ.node.cl
γ.id γ.t0 (γ.a0.map EntryModel.toLE)`.

**2026-11-25, option (a), item 1 closed; item 3's pure lemmas proved.** No axiom, no `sorry`, no new
top-level premise, no Go change.

*Item 1, L1 at the restart (done, `c62ac989e4`).* Made at the producer, not in `raftNode.start` (whose
loop state has moved past `S0` by then): `NodeStartLinked`'s restart arm holds `raftState γr.cl cv.ID' S`
with `σ.hs.Term' = S.term` (`StorageHolds`), `isCluster` and the image `isCommittedLogLb (A₀.map toLE)`
(already there for `replaySeed_facts`), and applies `raftState_cmtBefore`. The mark goes in the restart
data: `rnRestartOk`'s restart disjunct gains `cmtBefore γ.node.cl γ.id γ.t0 (γ.a0.map EntryModel.toLE)`.
New (`InvRaftNode.lean`): `rnRestart_cmtBefore (γ) : rnRestartOk γ ⊢ ⌜γ.a0 ≠ []⌝ -∗ cmtBefore γ.node.cl
γ.id γ.t0 (γ.a0.map EntryModel.toLE)`. Built (VM): `NewServerCrash`, `NodeStartLinked`, `ReplayJob`,
`AuthCompRows` and their cones (4993 jobs), green.

*Item 3's pure lemmas (`ReplayCoverage.lean`; built with the server's `Link`, 9494 jobs, green).*
- `replayHistoryMatches_append rs S S' n k first rest idx (h : replayHistoryMatches rs S n)
  (hcut : replayCutIndex rs first.index k) below here : replayHistoryMatches ((first :: rest).foldl
  replayAddEntry (replayRetain rs k first.index)) S' n`, with `below : ∀ ci t, n < ci → ci < first.index →
  plogTermAt S' ci = some t → plogTermAt S ci = some t` and `here : ∀ ci t, n < ci → first.index ≤ ci →
  plogTermAt S' ci = some t → ∃ e ∈ first :: rest, e.index = ci ∧ e.term = t` (`appendEntries_nonempty`'s
  output; replaces `rnReplayState.appendEntries`' `above`, i.e. `Ha0p`).
- `replayHistoryMatches_same rs S S' n m h (hb : S'.base = S.base) (he : S'.ents = S.ents) (hm : n ≤ m)`
  (an empty batch, the tick arm).
- `plogTermAt_next_batch S term vote commit first rest idx (hb : uint.Z S.base.index' < uint.Z
  first.index) (hwf : PlogWf S'.base S'.ents)` with `S' := S.next term vote commit none ((first ::
  rest).map toM)`: `below ∧ here` (without the cursor). `hwf` from `raftState_logView` at the entered
  `S'`; `hb` from `rnReadyData`'s `p.Commit' < first.index` plus `S.base.index ≤ p.Commit'` (to find:
  `rnLoopTokP`/`durPers`; else take it from raft's `Ready` post).
  For a snapshot `Ready`: `S.next … (some sn) es` has the base/ents of `{S with base := snapId, ents :=
  []}.next … none es` (by `rfl` on the fields), and `replayHistoryMatches [] {base := snapId, ents := []}
  n` holds for `n ≥ snapIdx` (no entry above), so the lemma applies after the reset.

*The design for items 2-4 (read off the code; not started).* The job is `applyAll`'s precondition
(`taReplayBatch`, `EtcdServer__run.lean:1436` from the payload's field) and is used only after
`<-apply.notifyc` (`EtcdServer__applyAll.lean:214`, the merge at :481). So:
- `rnReplayState γ view n` → `rnReplayState γ view S n := ∃ runs, view ↦*□ runs ∗ ⌜replayHistoryMatches
  runs S n⌝`, `S` the loop's durable state (`rnLoopTokP`'s); the seed is `replaySeed_facts`' `DurAgrees`
  form (the WAL's entries are `S0`'s); `.advance` by `replayHistoryMatches_after`, `.appendEntries` by
  the lemmas above, with `S'` the receive's (`rn_ready_recv` names it before the `Save`).
- The payload (`rnApN`, `rnApSnap`, `InvRaftLoop`'s copy): `∃ S, rnReplayHist γ ap.replayTerms' S n ∗
  ⌜S.term = ap.raftTerm' ∨ uint.Z ap.raftTerm' = 0⌝` in place of `rnReplayJob`, and the same `S` in the
  `notifyc` deposit: `isNotify γnc ap.notifyc' (rnApR γ F ce ∗ rnLeadLaw γ S)` with `rnLeadLaw γ S :=
  ⌜γ.a0 ≠ [] ∧ uint.Z γ.t0 < uint.Z S.term⌝ -∗ □ (snapshotLeader γ.node.cl γ.id S.term ={⊤}=∗
  ⌜durLogAgrees S (γ.a0.map toLE)⌝)` (the snapshot's `isNotify2`: on the first send).
- Item 2: after `rn_enter`/`rn_enterS` (`raftNode__start.lean:721, :1540`), `raftState_leadAgree` with
  `rnRestart_cmtBefore`, `srv_confFixed` and `isCluster` (from `rnEnvOk`'s `srvClusterOk`) gives
  `rnLeadLaw γ S'`; the `notifyc` sends deposit it.
- Item 4: `taReplayBatch` carries the history; `applyAll` builds `rnReplayJob` after the receive by
  `rnReplayJob_of_history` + `rnReplayJob_premise_of_lead` (its law premise made conditional as above).

Checkpoint 2026-11-25. **Next statement:** `rnReplayState` over the durable state, `def rnReplayState
(γ : RNNames GF) (view : GoSlice) (S : RaftState) (n : Nat) : IProp GF := iprop(∃ runs, view ↦*□ runs ∗
⌜replayHistoryMatches runs S n⌝)`, with `rnReplayState.appendEntries` re-proved over
`replayHistoryMatches_append`/`plogTermAt_next_batch` (`S → S'`), then the loop invariant of
`raftNode.start` (`Hhistory`) at `rnLoopTokP`'s `S`.

## 10T2. T2: the server's crash-aware durability invariant (2026-11-24, branch `etcd-safe-d6t2/2026-11-24`)

After §9 (the torn-batch law retired; the WAL fork fix makes a torn `Save` read as none), T2 states the
per-generation invariant that ties raft's durable state to what a crash can leave of the WAL.

**What a crash leaves.** `walSaveAtomic.law` (`storage/WalRecsH.lean`, pure, the fork fix's obligation
on the WAL re-proof; false of today's model): every image `I` of a history `H` at synced mark `n`
(`walImg`) reads, from every purge position, as a complete prefix `H.take j`, `n ≤ j ≤ |H|`. So the
invariant only has to say what each complete prefix from a synced lower bound reads as.

**The invariant** (`etcdserver/InvWalCrash.lean`, `rnDurInvK γn id νk h`): `rnDurInv`'s rows (the loop's
view, now `WalViewK = WalView × Option (WalView × GName)`, half; the handed log's authority; the
records as the view says, with their certificate), plus the records' history (`walRecsH`, a new
sealed variant of `walRecs` exposing the history, `storage/WalRecsH.lean`, with `walRecs_iff_H`), a
synced lower bound (`walSyncedLb`), every snapshot record of the history certified (`walHistCerts`),
the handed logs committed (`rnLogLbsK`), the pure crash fact `CrashReadsHold Hs n (crashOk vk)`
(every prefix `j ∈ [n, |Hs|]` reads records holding the view's durable state within its handed log, or,
while a batch is pending, the state before it), and kvnet's crash split: `raftState (durOf vk) ∗
rnPendK` (the pending batch's *enter* record, recognized by a saved proposition) or `crashed ∗ token tk`.
The WAL rows stay outside the split because the WAL contract's atomic updates commit without
`notCrashed`. The stop's taken state is `rnDurInv`'s plus a persistent mark (`rnTakenK`).

**Steps (statements, `abbrev … .law`)**: `rnDurK_alloc`, `rnDurK_save` (deposit at the `Save`'s commit),
`rnDurK_saveSnap`, `rnDurK_enter` (after the `Save` returned: the sync's lower bound, or a commit-only
batch, whose older prefixes still hold the entered state since `RaftState.next` keeps `wcommit`),
`rnDurK_ownSnap`, `rnDurK_take`, `rnDurK_crash`; and the WAL contract with the history and the sync
bound, `walSaveH.law`/`walSaveSnapH.law` (`storage.Save.spec`'s post already has the bound; the
server's `isWalStorage` drops it).

**Proved** (`InvWalCrashLaws.lean`): `rnDurK_crash_law_holds` (open with the crash token, borrow the
records for the WAL's crash `Φ`, then `nodeCrash` or `readyCrashEnter` by which state the read prefix
holds; the image's certificate by `walRead_snapSrc` + `walHistCerts_snapCert`).

**Remaining (plan)**: (1) the other laws' proofs, each `rnDur_*_au`'s proof plus the crash fact's pure
step lemmas: `walRead (Hs ++ [snap m])` = `walRead Hs` when `m` is above the last commit (received
snapshot); the new save prefix reads as the fold (`walRead_of_fold`); `walOwnSnap_holds` for every
prefix; the commit-only lemma from `RaftState.next`. (2) `walSaveH.law`/`walSaveSnapH.law` in the
contract (`isWalStorage`'s two fields over `walRecsH`, `walRecs_saveAU` with the history; the old
`walSaveSized_spec` derived). (3) The loop's integration: `raftState` leaves `rnDrv`/`rnBusyN`/
`rnPendEnter` for the invariant (the loop keeps only its view half), `raftNode__start`'s `Ready`
handling calls `rnDurK_save` at the `Save` and `rnDurK_enter` after it (with `notCrashed` and two
credits), `newRaftNode` keeps the arm's crash token (`nodeVacant_arm` instead of `nodeVacant_armD`) for
the run's `Keep`, and `rnDurInv` is replaced by `rnDurInvK` in the run's and stop's specs. Estimated
well above 3k lines across `InvRaftNode`, `raftNode__start` (2039 lines), `EtcdServer__run`, `NodeStart`,
`newRaftNode` and the WAL contract. (4) Open: the stop's taken state (`rnTakenK`): a member whose
server stops gracefully and then crashes has its image in the stop's post, not in the crash's `Keep`;
T7 must exclude it (the member never stops its server) or route the stop image to the crash.

### P5 checkpoint (2026-11-25, branch `etcd-safe-p5`; `notes/wal-p5-handoff.md`)

On round 3 (`57e4d118b7`, then `5a1c41d945` with P7) with d6t2 merged. **Proved** (no `sorry`, no axiom):
the pure steps of `HistOkK` (`InvWalCrashPure`: `Save`, a received and an own `SaveSnap`, *enter*, the
allocation at a first start, `histOk_fresh`, and at a restart, `histOk_restart`); the laws
`rnDurK_{save,saveSnap,ownSnap,enter,take,alloc}` and `walSave{,Snap}H` (`InvWalCrashSteps`; with P8's
`rnDurK_crash`, every step of `rnDurInvK`); the storage contract's `Save`/`SaveSnap` over `walRecsH` with the
history and the synced bound (`isWalStorage`, `RnNewStorage`'s laws, `walSaveRn_spec`, `walSaveSnapH_spec`;
the old record forms derived: `walSaveRnR_spec`, `walRecs_au_toH`); the boot slots with the history
(`walOpenedH`; `wal.bootOk`: `walFresh`, `[]`; `wal.restartOk`: the synced mark at `|Hs|`, the index bound
and the eager commit bound; `wal.Create.specSrv`'s post; `wal.{boot,restart}Ok_startK`). The approved text
said the reader's `walCommitLe`; the slot states the eager fold's `walCommitLeFrom walFresh Hs`, which implies
it and which `histOk_save` needs (ledger, 2026-11-25). Built: the 49 importer leaves on `4167bcf956` and after merging `5a1c41d945` (exit 0).
**Left**: the integration (handoff, "Plan" step 4): `rnDurInvK` in place of `rnDurInv` in `isRaftNode` and
the loop, allocated in `newRaftNode` after `StartNode`/`RestartNode`, the loop's `Save`/*enter*/`SaveSnap`,
the stop's take, the apply thread's own snapshot.

**P5 checkpoint 2 (2026-11-25, `etcd-safe-p5`, P6b `2d2f3cc470` merged).** The restart-independent integration
is in and builds: `rnDurInvK` in `isRaftNode`/`rnWalTokA`; allocated in `bootstrappedRaft.newRaftNode` after
`StartNode` (`rnDurK_alloc_fresh`) and, behind the one hypothesis `hRestartAlloc : rnRestartAllocK.law`, after
`RestartNode`; the loop's `Save`/*enter*/`SaveSnap`, `onStop`'s take, `EtcdServer.snapshot`'s own snapshot and
`SnapApplyWalk`'s read through the K laws. One labelled `sorry`, **P5-RESTART**, in `rnRestartAllocK_law_holds`
(`walHistCerts` of the restart's history; switches with #50's decision on the restart slot). Changes the proof
needed (handoff, "State"): `HistCommitMono` in `HistOkK` and the commit-bounded commit-only *enter*; the
storage contract's `Sync` gives `walSyncedLb` at `Save`'s length bound, and a snapshot `Ready`'s *enter*
follows etcd's explicit `Sync`; the snapshot directory's durability `WalNamesK.sd` is the trivial one until
T6. Built: the change's 58 importer leaves (fk-lean2, 14,036 jobs, exit 0); `etc/tier-check.py --check` ok.
`etc/tcb-baseline.txt` still lacks the P5-RESTART `sorry` (needs a local build to update).

## T7: the member's crash law (plan, 2026-11-25, branch `etcd-safe-t7`; etcd-grove-03)

Base `etcd-safe-p5` @ `f353cbb2fb` (round 3 `5a1c41d945`, P6b `2d2f3cc470`, P5's T2 integration). File
`dist/crash/MemberCrash.lean` (defs tier: it imports only defs and the proved defs-tier laws).

**The law as it stands** (`MemberGen.lean`): `memberGen_crash.law C cfg id Keep Q` — for generations `L`, `L'`
at the statement's Go context, `Keep L -∗ £ 1 -∗ crashed L -∗ Fs.crashRest Q L L' [] false V' -∗ Fs.osInv L'
={⊤}=∗ memberGen (at L') C cfg id`. `Keep` and `Q` are parameters: T7 chooses `Keep` (`memberKeep`, what a run
of a generation keeps for its crash) and proves the law for it under a premise on `Q`. `memberGen` =
`clusterFacts ∗ (memberFirst ∨ memberRestart)`, `memberRestart` = `memberRestartFacts γ' ρo id ∗
srvCrashImage γ' ρo id dd` (`InvCrashImage.lean`).

**Inputs** (source; status):

| input | what T7 uses | source | status |
|---|---|---|---|
| T1 raft torn law | — | `readyCrashTorn.law` (`MemberGen.lean`) | **retired**: the torn-`Save` fix (Q1 (a), fork `e94f33b50`) makes a torn `Save` read as none; T7 deletes `raftTorn`/`readyCrashTorn.law` (P5 plan step) |
| T2 raft + WAL records | `raftState S`, `nodeVacant`, `StorageHolds S σ`, `walReadFacts σ`, `σ.b ≤ |l|`, `DurAgrees S l`, `walSnapCert`, `walSnapDur`, `isCommittedLogLb l`, and the WAL's borrowed `walRecsH`/`walSyncedLb` for the files | `rnDurK_crash.law` / `rnDurK_crash_law_holds` (`InvWalCrashLaws.lean`) | **proved**; its second disjunct `rnTakenK` (the stop took the records) must be excluded by `Keep` (decision D-T7-3 below) |
| T2 allocation | — (the run's, not the law's) | `rnRestartAllocK.law` | named hypothesis of `newRaftNode` (P5-RESTART `sorry`), consumed as stated by T8's run, not by T7 |
| T5 the WAL's files | `walFilesC` at `L'` from `walCrashWal`, the old `walDiskAtI`/`walSyncedLb`/`walNamed` | `walFilesC_crash` (`storage/WalRecsCrash.lean`); `walInv_crash` (`storage/wal/Crash.lean`, premise `Q → W1`); `walBootCrash` (`BootCrash.lean`) | **proved** |
| T5 read facts | `walReadFacts σ` | `walReadFacts_of_take`; T2's post already carries it | **proved** |
| T6 snapshot directory | `snapDirKeep` at `L'` | `snapDir_crash.law` / `snapDir_crash_law_holds` (`SnapDirCrash.lean`) | **proved**, with two premises owed by T7: `lookupH R V' sd = some (.dir J)` and `snapDirKept R V' sd` (item 2 below) |
| A1 bbolt after a power loss | `bbolt.fileHoldsM i0 D'`, `D' ∈ {Dl, Dn, pd}` | `backend.dbCrash` (C-I1, `storage/backend/CrashInterim.lean`) | **interim axiom** (reviewed six times), premise `Q → BoltCrashWhole (· = i0)`; its record `dbCrashKeep` is made by `dbCrashKeep_new` at boot, used by no run yet |
| `Q`'s premise | `Q → W1 walCodec` and `Q → BoltCrashWhole I` | `etcdCQ` (`etcdstart/FsExts.lean`) has `W1` only | **open**: `BoltCrashWhole` accepted for the packet, not yet in `etcdCQ`; T7's theorem takes `hQ` |
| the backend's image across a crash | for each of `Dl`, `Dn`, `pd`: a committed prefix `A` with `i = ai0 + |A|`, `imageRestAt`, `imageStOk`, `mvccImage`, `confAt i m`, `srvRLogLb A`, `σ.b ≤ i`, `bootLen ≤ i` (all of `srvCrashImageAt`'s backend rows) | none: the apply thread's commits must deposit them beside `dbCrashKeep` (an invariant of the run, "D6.4") | **open, no task owns it** (proposed T10 below) |
| the backend file's name after the crash | `Named V'.now i0` and `config.backendPathOf dd` naming `i0` in `V'` (`backend.fileHolds`) | the name's commit (`dbOpts`, the WAL's first directory sync, the fork's syncs after the renames; `renamedDur` from `OpenSnapshotBackend`, not persistent as stated: add the instance) | **open** (C-I1's note: "the caller derives which inode `path` names from the file extension's crash facts") |
| the request ids | `memberRestartFacts γ' ρo id` (persistent, global) | the generation's boot (`memberRestartFacts_alloc`) kept in `Keep`; D4b's `idIssue` crash interpretation for the new incarnation | facts **proved**; D4b's crash interpretation open (Q5), not T7's |

**Obligations** (what T7 proves, in order):
1. **`memberGen` first** (the predicate both the first boot and the crash law produce and `NewServer` consumes):
   (a) delete the torn law; (b) the rows the next generation's `Keep` needs that today's `memberRestart` drops:
   the snapshot directory's crash token (`srvCrashImageAt` holds only the handle `snapDirInvH`; the next
   crash law needs `snapDirKeep`, i.e. the token, with the same `γk`), raft's crash token (`specC` returns
   it: T4 round 2), the WAL area's `walInv`/`walCrashTok` at `L'` (from `walInv_crash`/`walBootCrash`), and
   the durable spine of `sd` (item 2). (b) changes `srvCrashImageAt` (shared with `NewServer.specC`, T4):
   **reported, not done** (D-T7-2).
2. **P7's two premises from `TouchDirAll`**: a persistent durable spine `osPathDur R sd J` (each component's
   claim held at a discarded fraction, with `nameCrash` at its directory: what `TouchDirAll`'s post gives,
   `h'.next ≤ n` and `osCommitLb n`, plus `osNames_histCoh`); `osPathDur_crash`: with `crashRest`,
   `lookupH R V' sd = some (.dir J)`; `osPathDur_agree`: every spine of `sd` at the same roots ends at `J`, so
   the fixed-root form of `snapDirKept` holds. P7's `snapDirKept` quantifies over the roots `R0` of any
   `osSharedInv R0` and is a plain wand (no update): unprovable as stated (two shared invariants' roots agree
   only under an update), see D-T7-1.
3. **The assembly** `memberGen_crash_law_holds` for `memberKeep`: open `rnDurInvK` (T2), inside its `Φ` the
   WAL's crash (`walInv_crash`, `walBootCrash`, `walFilesC_crash`: T5), the backend (`dbCrash`: A1, and the
   image invariant: open), the snapshot directory (`snapDir_crash_law_holds` with item 2), the new
   registry (`memStorRegAuth ∅` at a fresh name, Q4's decision), then `srvCrashImageAt` at `ρo`.

**What blocks 3** (each needs a decision or a task outside T7; found by reading, 2026-11-25):
* **B1 the backend's image invariant** (above): `Keep` must carry, for the data a crash can leave, the image
  facts; nothing in the run records them. A task of its own (T10: the apply thread deposits each commit's image
  facts next to `dbCrashKeep`; `dbCrashKeep_new`/`_announce` at its commit points).
* **B2 Q3, the received-snapshot window**: between the WAL's `SaveSnap` (synced) and the apply thread's
  rename of `<k>.snap.db` to `db` (`OpenSnapshotBackend`), a crash leaves `σ.b = k > i` (the old `db`);
  Go recovers by opening the `.snap.db` at restart (`recoverSnapshot`). `srvCrashImageAt`'s `σ.b ≤ i` is then
  false: the image (and `bootstrapCrashContract`) needs the `.snap.db` case (shared spec: T4's).
* **B3 `γ.cl.bootLen ≤ i`** (C-I1 checkpoint item 7): after the first `Save` and before the backend's first
  commit `i = 0`; `srvCrashImageAt` and `bootstrapCrashContract` exclude it (shared spec).
* **B4 the first generation's boot phases**: a crash before `newRaftNode` allocates `rnDurInvK` (after
  `bootstrapBackend`, `wal.Create`, an unsaved first `Save`) must give `memberFirst` (with T3's leftovers), so
  `Keep` is a disjunction over the boot's phases (kvnet's `kd_boot_choose`); `memberFirst`'s slice is consumed
  by `NewServer.specG` by then. Needs T3 and T8's boot.
* **B5 `Keep` out of the run** (T8): `NewServer.spec{G,C}`'s posts return raft's crash token only; `rnDurInvK`'s
  token and names, `snapDirKeep`, the WAL area's `walInv`/token, `dbCrashKeep`, the durable spine must come out
  of `NewServer` into the member's program.

**Decisions taken in T7 (D-T7-*)**:
* D-T7-1 `snapDirKept` at fixed roots: T7 proves `□ ∀ dq j, osPathS R sd dq j -∗ ⌜lookupH R V' sd = some (.dir j)⌝`
  (the law's own `R`); P7's `snapDirKeptF` should take `R0 := R`, and `old_dir` get `R0 = R` from the two shared
  invariants and `crashRest` (`crashRest_roots`, T7 proves it). A premise of P7's law weakened: ledger entry
  2026-11-25; not edited here (shared law statement).
* D-T7-2 `srvCrashImageAt` carries `snapDirKeep` (handle and token) instead of `snapDirInvH`, and `NewServer.specC`'s
  post returns the token (as raft's crash token): T4's spec; reported.
* D-T7-3 the stop excluded: `Keep` holds `token νk.ν.stop` (the member's program never stops its server, so the run
  never takes it); `rnDurK_crash`'s `rnTakenK` case is refuted by it. Asks of T8: the run's specs do not need the
  stop token (or route the graceful stop's image to the crash, §10T2 (4)).
* D-T7-4 the durable spine is persistent: the boot discards a fraction of the claims on `member` (in `dd`) and `snap`
  (in `member`) after `TouchDirAll` (`gElem` persist; Go never writes those names again: `DiscardUnsaved` renames
  `member/wal`, the bootstrap fix removes `member/snap/db`, both other claims). Asks of T8: the discard at boot.

**Order**: (1a) delete the torn law; (2) `osPathDur` and its lemmas (proved now); (1b)/(3) after B1-B5's decisions.
Estimate for (3) once unblocked: the table's 600-1000 lines for the assembly alone, plus T10 (B1, 800-1500) and T8.

### T7 status and handoff (2026-11-25, session 1; branch `etcd-safe-t7`)

**Done** (built on fk-lean2 in the P8/P5 worktree, `lake build …dist.crash.MemberCrash`, 4497 jobs, exit 0; no
axiom, no `sorry`; `etc/tier-check.py --check` ok, the new file is defs tier):
* (1a) `raftTorn`/`readyCrashTorn.law` deleted from `MemberGen.lean` (no user; T1 retired by the torn-`Save` fix).
* (2) `dist/crash/MemberCrash.lean`: `osSpineDur`/`osPathDur` (persistent durable paths), `osPathDur_root`,
  `osPathDur_child` (from `TouchDirAll`'s post: the claim at a discarded fraction, `h.next ≤ n`, `osCommitLb n`),
  `osSpineDur_crash`/`osPathDur_lookup` (**T6's premise `lookupH R V' sd = some (.dir J)`**, from `crashRest`),
  `osPathDur_agree`, `snapDirKeptR`/`snapDirKeptR_of` (**T6's `snapDirKept` at the law's roots**), `crashRest_roots`
  (two shared invariants of the crashed generation agree on their roots: what `old_dir` needs for the restatement);
  `rnTakenK_stop` (D-T7-3: T2's crash law's stop case refuted by the stop's token).
* Ledger entries (2026-11-25): T6's `snapDirKept` unprovable as stated (D-T7-1); `srvCrashImageAt`'s three
  gaps (D-T7-2, B2, B3). Neither statement edited.

**Next, in order** (each waits on the decision named):
1. D-T7-1 approved → in `SnapDirCrash.lean`: `snapDirKeptF := snapDirKeptR`'s body, `old_dir`'s three callers
   get `R0 = R` from `memberCrash.crashRest_roots` (move it, or `osPathDur`'s file, below `SnapDirCrash` if the
   import direction requires: `MemberCrash` imports `SnapDirCrash` today).
2. The producer side of `osPathDur R sd J` (T8's boot): after `bootFs.touchMember` (`member`) and
   `bootstrapSnapshot`'s `TouchDirAll(SnapDir())` (`snap`), persist a fraction of each claim (`gElem` persist,
   `DFrac.update_discard`) and apply `osPathDur_root` (the data directory is a root?) then `osPathDur_child`
   twice (`dd` is a root of the shared invariant, P7 round 4 gap 1, so `sd`'s spine is `[member, snap]`).
3. B1 (the backend's image invariant): a design note first (who deposits the image facts at each backend
   commit; `dbCrashKeep_new`/`_announce`/`_clear` at the apply thread's commit points; the facts must cover
   `Dl`, `Dn` and `pd`).
4. (done, session 2: see below) The WAL+raft part of the assembly.
5. B2/B3/D-T7-2 decided (T4's `srvCrashImageAt`) → the image assembly; B4 (T3, T8's boot phases) → the
   `memberFirst` case; B5 (T8) → `memberKeep` as a definition and the law proved.

### T7 status and handoff (2026-11-25, session 2; branch `etcd-safe-t7`)

**Done** (built on fk-lean2, `lake build …dist.crash.MemberCrash`, 4499 jobs, exit 0, no warning in the file;
no axiom, no `sorry`; tier and API checks ok):
* `storage/WalRecsHGen.lean` (new, imports `WalRecsH` with `import all`, so nothing above rebuilds):
  `walRecsH_gen`, the records at one generation are the records at another (both at the statement's Go
  context: `go.Semantics` is over a `GoLocalContext`, so the generations are `{L with goose_go_local_context
  := lctx}`, i.e. `etcd_dist.atCtx`). `walFilesC` needs no such lemma: T5's `walRecsH_crash` states it at the
  new generation directly, so the callback runs at `L'` and only the records cross.
* `MemberCrash.lean`, section `durDefs` (one `HeapGS` each; see the pitfall below): `memberDurKeep` (T2's
  invariant, `token νk.tk`, `nodeCrashTok`, the stop's `token νk.ν.stop`: D-T7-3), `memberWalKeep h` (`walInv` at
  `walCodec`/`walSrvMr`, `walCrashTok`, `osSharedInv h.R`), `memberWalCrashW h W'` (`walCrashWal`, `W'`'s lock
  token), `memberWalCrash h W'` (that and the WAL directory's call permission's half), `memberDurOut` (T2's
  outputs: `raftState`, `nodeVacant`, the image facts, `walSnapCert`, `walSnapDur`, the committed log);
  `memberDurOut_gen` (`.rfl`).
* `memberWal_crash`: `walInv_crash` at the member's WAL, first of the crash lemmas (`D = []`): `W'`,
  `memberWalCrashW` at `L'`, `W'.roots = h.R ∧ TreeWf h.R V'.now`, the crash rest with the area's files.
  The new generation's `walStart`/boot files are dropped: `memberGen`'s restart case holds only the files
  (`srvFilesC`), so `walBootCrash` is **not** needed by T7 (the restarted server's area is `bootstrap`'s crash
  contract's business; noted, not a blocker of T7).
* `memberDur_crash` (T2 + T5): `memberDurKeep` at `L`, `isCluster`, **one** credit, `crashed` at `L`,
  `memberWalCrash` at `L'` ⊢ `∃ S σ l, walFilesC (L') {h.toWalA with W := W'} id cid σ true ∗ memberDurOut (L)`.
  `rnTakenK_stop` now needs no credit (the contradiction is pure under the later, `▷ ⌜False⌝`), so the
  law's single `£ 1` goes to T2. **But `snapDir_crash.law` also takes a `£ 1`**: the assembly needs a second
  credit, which `Keep` must carry (`£ 1` in `memberKeep`, deposited by T8; B5's) unless T6's law is
  restated credit-free (its body is not timeless).

**Pitfall (cost three builds).** In a statement over two generations, `G : GooseGlobalGS`, `L`, `L'` are all
local instances (a binder of class type is one, brackets or not), so a predicate written directly in the
statement gets instances Lean picks (`nodeCrashTok`'s `InvGS` came out as `invGS (goose_irisGS G L')`), not
the law's (`… ⟨G, atCtx L⟩`), and `iapply`/`$$` fails with `IntoWand` on syntactically equal-looking
terms. Fix: name each generation's resources by a definition over one `[hG : HeapGS]` and use it at
`(hG := ⟨G, atCtx L⟩)`; predicates over `GooseGlobalGS` alone (`walCrashWal`) are fine.

**Next, the assembly** (`memberGen_crash_law_holds`, one named hypothesis per blocker). Design:
* `Keep L := memberKeep KeepF KeepB L`, two abstract keep pieces (parameters) for the blocked parts:
  `clusterFacts …` (persistent) `∗ £ 1 ∗ (KeepF L ∨ memberKeepR KeepB L)`, where `memberKeepR` =
  `∃ h νk γn ρo r cid …, memberDurKeep ∗ memberWalKeep h ∗ dbCrashKeep … ∗ snapDirKeep … ∗ osPathDur R sd J ∗
  memberRestartFacts γ' ρo id ∗ KeepB L ∗ ⌜h.toWalA = etcdWalArea … ∧ h.md = walMetaEnc id cid ∧ h.dir =
  srvWalDirOf dd ∧ …⌝`. The equation `h.toWalA = etcdWalArea …` is needed: `memberWalKeep`/`walInv_crash` are at
  `h.ext`, the law's `crashRest` at the ambient `ExtSemantics`; `cases h` + `subst` makes `h.ext` the ambient
  `inferInstance` definitionally.
* Named hypotheses (each an `abbrev memberCrash.<name>.law : Prop` with a docstring naming its blocker):
  - **B4** `memberFirstCrash.law KeepF`: `KeepF L` (and the crash's inputs) `={⊤}=∗ memberFirst` at `L'`.
  - **B1** `memberImage.law KeepB`: `KeepB L`, the backend's `fileHoldsM i0 D'` (from `dbCrash`) and
    `memberDurOut` give the image rows `srvRLogLb A`, `i = ai0 + |A|`, `imageRestAt`, `imageStOk`, `mvccImage`,
    `confAt`, `v3ConfStateIs`, `memStorRegAuth M`, and the backend's `fileHolds (backendPathOf dd) D`
    (the backend file name: B1's too).
  - **B2** `σ.b ≤ i` and **B3** `bootLen ≤ i`: two pure hypotheses over B1's outputs (as stated they are false
    in some runs, ledger 2026-11-25; T4's restatement of `srvCrashImageAt` replaces them).
  - **D-T7-1**: `snapDirKept` from `snapDirKeptR` (the ledger's restatement makes it `snapDirKeptR_of`).
  - **D-T7-2**: the snapshot directory's row of `srvCrashImageAt` (`snapDirInvH … ∗ monoNatAuthOwn γm 1 c`)
    from `snapDir_crash`'s `snapDirKeep` at `L'`.
  - **A1** `∀ st st', Q st st' → BoltCrashWhole (· = i0) st st'` (and `W1`), a plain hypothesis on `Q`
    until `etcdCQ` has it.
* Order of the proof: `memberWal_crash` → `dbCrash` (`Dx` = the WAL's `D`) → `crashRest_treeWf'`,
  `crashRest_treeS'` (`V'.2 = []`, `osShared L' R V'`; the WAL directory's call permission's half out of
  `osCallPerms`) → `osPathDur_lookup` → `snapDir_crash_law_holds` (its `snapDirOwn`/`snapSlot`s from the
  shared claims of `dd`'s directories at `L'`: still to write, D-T7-4) → `memberDur_crash` → the image
  hypotheses → `memberRestart` at `L'` (`memberRestartFacts`, `clusterFacts` moved to `L'`: check they are
  generation-free by `.rfl`, as `memberDurOut_gen`).

### T7 status and handoff (2026-11-25, session 3; branch `etcd-safe-t7`)

Coordinator's ask: write `memberGen_crash_law_holds` with one named hypothesis per blocker (B4, B1, B2, B3, D-T7-1,
D-T7-2, A1), the extra `£ 1` in `Keep` (T8's obligation); then D-T7-4's slots; check the facts carry over.

**Done** (built on fk-lean2, `…dist.crash.MemberCrash`, exit 0; no axiom, no `sorry`):
* `memberClusterFacts` (wrapper over one `HeapGS`) and `memberClusterFacts_gen` (`.rfl`): the cluster's facts carry
  over.
* `memberRestartFacts_gen`: a restart's facts carry over **except `idPfxInv`**, which is heap-level (its invariant
  holds the generators' `prefix` field points-to on the old heap). New blocker **B6**, ledger 2026-11-25
  ("`memberGen`'s restart case asks for the old incarnation's `idPfxInv`…"): as stated, `memberRestart` is
  unprovable after any crash. The lemma takes the new generation's `idPfxInv` as an input; the assembly takes it as
  the named hypothesis B6.

**Not done: the assembly.** Two plumbing facts found while reading its inputs, which fix `Keep`'s pure rows:
* (instances, B7, internal to T7's `Keep`, no spec change) Three file-system instance sources meet: the law's ambient
  `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` (its `crashRest`), the WAL's `h.ext/h.semOk/h.has` (`walInv`,
  `walInv_crash`), and the backend's and snapshot directory's `theFs GF = some c` (`onFs`: `dbCrashKeep`'s
  `bbolt.fileHoldsM`, `snapDir_crash.law`'s `crashRest` at `c`'s instances; `theFs` is a `Classical.choice`). `Keep`
  must carry `⌜h.toWalA = etcdWalArea …⌝` and `⌜theFs GF = some ⟨‹_›, ‹_›, ‹_›, fa, fsa, ne⟩⌝` (ambient ones), and the
  proof `cases`/`subst`s them before applying each crash lemma.
* (D-T7-4) `snapDir_crash.law` takes `snapDirOwn (snapDBPath sd)` and `[∗list] i ∈ snap.allW64, snapSlot sd J V' i`
  at `L'` (each slot: `osInv`, `osSharedInv R`, `osPathS R sd dq J`, a call permission share, the claim on index `i`'s
  name `osNames J (.only [snapDBName i]) 1 …`, `PathFits`). They come from `osShared L' R V'` (`crashRest_treeS'`):
  the whole claim `osNames J (.except []) 1 (namesOf V' J …)` of `sd`'s directory split into `.except snapDirNames`
  and the `2^64` singletons (a lemma over `snap.allW64` by induction, no `[∗list]` materialized: never `iframe` it),
  the path `osPathS R sd dq J` from the claims of `dd` and `member` (fractions split off `osShared`'s whole claims
  along `osPathDur`'s spine), and the call permission from `osCallPerms R`.

**Next, in order:**
1. `memberKeep C cfg id KeepF KeepB L := memberClusterFacts ∗ £ 1 ∗ (KeepF L ∨ memberKeepR KeepB L)` (`£ 1` for
   `snapDir_crash.law`: T8's obligation), `memberKeepR` with the rows of session 2's design plus B7's two pure rows and
   `memberRestartFacts γ' ρo id`.
2. The hypotheses, each an `abbrev memberCrash.<name>.law : Prop` with its blocker in the docstring: `memberFirstCrash`
   (B4), `memberImage` (B1), `memberImageB` (B2, pure, "false in some runs as stated; replaced by T4's restatement"),
   `memberImageBoot` (B3, likewise), `snapDirKeptOf` (D-T7-1: `snapDirKeptR ⊢ snapDirKeptF` at the law's roots),
   `memberSnapRow` (D-T7-2: `snapDirKeep` at `L'` gives the image's snapshot row), `memberPfx` (B6: the new
   generation's `idPfxInv`), `hA1 : ∀ i0 st st', Q st st' → BoltCrashWhole (· = i0) st st'` (A1, until `etcdCQ`), and the
   law's own premise `Q → W1 walCodec` (not a blocker).
3. The proof, in session 2's order, with D-T7-4's split lemma (above) proved first in `MemberCrash.lean`.

### T7 status and handoff (2026-11-25, session 4; branch `etcd-safe-t7`)

**Done** (`dist/crash/MemberCrash.lean`; built on fk-lean2, `…dist.crash.MemberCrash`, 4515 jobs, exit 0; tier check ok; no axiom, no `sorry`):
* **D-T7-4's split** (`section slots`): `snapSlots_of` (induction over an index list: each index's fresh claim
  plus half of the remaining path/call shares gives `snapCrash.snapSlotF`), `snapDir_split` (the new generation's
  whole claim `osNames J (.except []) 1 (namesOf V J (.except []))` with a path share and a call share ⊢ every
  index's slot over `snap.allW64`, the claim on `db` (for B1), and the `.except snapDirNames` claim with shares,
  i.e. `snap.snapDirOwn`'s body). Over `WalFs.osNames_split_only`; `allW64` is never unfolded and no context
  search runs next to its `[∗list]` (every step frames by name).
* **`memberKeep`** (`section keep`): `memberClusterFacts ∗ £ 1 ∗ (KeepF L ∨ memberKeepR C cfg id (KeepB L))` at
  `⟨G, atCtx L⟩`; `memberKeepR` = `∃ k : MemberKN`, pure rows (`k.γ = {C.γ with reg}`, `k.h.dir = srvWalDirOf dd`,
  `k.h.md = walMetaEnc id k.cid`, `k.γ.snapLoc id = some k.γd`, `∃ c, theFs GF = some c`), `memberRestartFacts`,
  `memberDurKeep`, `memberWalKeep`, `dbCrashKeep γb (backendPathOf dd) i0 Dl Dn pd`, `memberSnapKeep` (snapDirKeep
  at the image's `img`/`Rm`), `osPathDur h.R (snapDirOf dd) J`, `KeepB k`.
* **Named hypotheses**: `memberFirstCrash.law` (B4), `memberImage.law` (B1, with B2/B3's bounds as its pure
  output `memberImageB σ i ∧ memberImageBoot γ i`, each a named def whose docstring says "false in some runs as
  stated; replaced by T4's restatement"), `memberPfx.law` (B6), `snapDirKeptOf.law` (D-T7-1). A1 and W1 are plain
  premises on `Q` of the theorem.

**Decisions (session 4).**
* B7 needs no row for the WAL: `h.has.sem_eq` and the ambient `HasExt.sem_eq` give `h.ext = ‹_›` (as
  `snapDir_crash_law_holds` does); `FsSemOk`/`HasExt` are `Prop`s (`Subsingleton.elim`). Only `∃ c, theFs GF = some c`
  is kept (the `onFs`-wrapped resources and `snapDir_crash.law` need `c`).
* B2/B3 are not separate hypotheses: as standalone `∀ σ i` entailments they would be false outright (making the
  law vacuous), so they are B1's pure output, named (`memberImageB`, `memberImageBoot`).
* D-T7-2 needs no hypothesis for this law: the image's snapshot row is `snapDirKeep_handle`'s handle at `L'` plus
  the counter authority `monoNatAuthOwn γm 1 c`, `c ≤ i+1`, which B1 returns (`memberImageRows`). The token is
  dropped (D-T7-2 stays a defect for the *next* crash, T4/T8).
* Q4 (fresh registry): `memberRestartFacts` fixes `ρo.rd.raft = ⟨γ', [], 0⟩`, so the image at a fresh `r'` needs
  `ρo' := ρo` with `rd.raft := ⟨{γ' with reg := r'}, [], 0⟩` and a transport lemma (the bodies don't read `reg`:
  `Alloc3.lean`'s `*_reg` are `entails_refl`; expect `.rfl` up to the pure row).

**Next: `memberGen_crash_law_holds`** with
`(hQ : ∀ st st', Q st st' → WalFs.W1 walCodec st st') (hA1 : ∀ i0 st st', Q st st' → BoltCrashWhole (· = i0) st st')
(hB4 : memberFirstCrash.law C cfg id KeepF Q) (hB1 : memberImage.law cfg id KeepB) (hB6 : memberPfx.law)
(hD1 : snapDirKeptOf.law) : memberGen_crash.law C cfg id (memberKeep C cfg id KeepF KeepB) Q`. Steps:
1. `cases L`/`cases L'` and the context equations so `atCtx L` is `L` definitionally.
2. First case: `hB4` (with the law's credit), frame the cluster facts (`memberClusterFacts_gen`).
3. Restart case: `obtain` `k.h`'s instances equal to the ambient ones (sem_eq), then `memberWal_crash` (D = []),
   `dbCrash` (`Dx` = the WAL's `D`, `i0 ∉ Dx` and `Named V'.now i0`: **still open**, from the backend file's
   durable name: add to `memberKeepR` as a durable path of `backendPathOf dd` — `osPathDur` gives the spine
   but not the file entry; a `nameCrash` for `db` in `J` is what's needed — or into B1's keep),
   `crashRest_treeS'` (→ `osShared L' R V'`), `osPathDur_lookup`, `snapDirKeptR_of` + `hD1`.
4. **The path at `L'`** (T7's own, not yet written): `osPathS R sd (own q) J` at `L'` from `osShared`'s
   `[∗list] j ∈ dirsOf V'` whole claims along `osPathDur`'s spine (claims `.only [c]` split off each spine
   directory; the directories pairwise distinct and in `dirsOf V'`, from `TreeWf` and the walk). Then
   `snapDir_split` at `L'` and `snap.snapDirOwn` via `onFs_some`.
5. `snapDir_crash_law_holds` (second credit from `memberKeep`), `memberDur_crash` (the law's credit; the WAL
   directory's call permission's half from `osCallPerms R`), `hB1`, `hB6` + `memberRestartFacts_gen`, the Q4
   transport, and `srvCrashImageAt` assembled (`srvFilesC`: `walFilesC` with `a.dir = h.dir`, `B1`'s `fileHolds`).

### T7 status and handoff (2026-11-25, session 7; branch `etcd-safe-t7`)

**`memberGen_crash_law_holds` proved** (`dist/crash/MemberCrash.lean`, out of its comment; built on fk-lean2,
`lake build …dist.crash.MemberCrash` green, 4515 jobs; `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` and
the reviewed interim axiom C-I1 `backend.dbCrash`, no `sorry`, nothing new). Statement unchanged from session 6:
`(hQ) (hA1) (hB4) (hB1) (hB1n) (hB6) (hD1) : etcd_dist.memberGen_crash.law C cfg id (memberKeep C cfg id KeepF KeepB) Q`.

* The blocker (T6's `img` of the old generation) closed by the coordinator's option (a) (ledger 2026-11-25, decision
  recorded): `mvcc.api.mvccImage_gen` (`EtcdBackend.lean`, `.rfl` inside the sealed module: `⧖` is global ghost
  state), `srvImageM_gen` (`etcdserver/ImageOn.lean`), and T6's `snapDir_crash.law` takes `img img'` with
  `□ (∀ j Dt, img j Dt -∗ img' j Dt)`. Both generation laws fix the Go context (`{L with goose_go_local_context :=
  lctx}`): `go.Semantics` takes a `GoLocalContext`. Only importer of the T6 law: `MemberCrash`.
* `etc/tier-check.py --check` ok. `etc/api-check.py etc/api/backend.txt --check` reports one error that predates this
  session (`MemberCrash` imports `backend.CrashInterim`, not importable; the C-I1 interim axioms' module).
* **Left for T8/T10**: the named hypotheses: B4 `memberFirstCrash.law` (T8's boot phases), B1 `memberImage.law` and
  `memberDbNamed.law` (T10's backend image invariant and the `db` file's durable name), B6 `memberPfx.law`, D-T7-1
  `snapDirKeptOf.law`, `hQ` (W1) and `hA1` (bbolt's crash premise, until `etcdCQ` has it); T8 builds `memberKeep`
  (the second later credit, `KeepB`, the spine `member/snap` with its root rows) and applies the law; D-T7-2 stays
  a defect for the next crash (T4/T8); C-I1 (`dbCrash`) is interim.

### T7 status and handoff (2026-11-25, session 6; branch `etcd-safe-t7`)

**`memberGen_crash_law_holds` written, stopped one step short** (`dist/crash/MemberCrash.lean`, the last section, in a
block comment marked WIP so the file builds; no axiom, no `sorry`). With the comment removed, `lean-check` on fk-lean2
(`etcd-safe-p8` worktree) elaborates every step of the session-5 plan and reports **one error**: the snapshot row of
`srvCrashImageAt`. Statement: `(hQ) (hA1 : ∀ i0 st st', Q st st' → BoltCrashWhole (· = i0) st st') (hB4) (hB1) (hB1n)
(hB6) (hD1) : etcd_dist.memberGen_crash.law C cfg id (memberKeep C cfg id KeepF KeepB) Q`.

* **The blocker** (ledger 2026-11-25, "T6's `snapDir_crash.law` keeps the image predicate `img` of the old
  generation"): the kept `snapDirKeep`'s `img = srvImageM γ.authOn γ` is at the old generation's `HeapGS`, the image
  wants the new one's; `mvccImage` is `@[no_expose]` and takes the `HeapGS`, so no `.rfl`. Proposed: an mvcc API law
  `mvccImage_gen` and `img → img'` in T6's law. **Decision needed** before T7 can finish.
* New, compiled (outside the comment): `memberRestartFacts_cluster` (the restart facts give `ρo.rd.raft = ⟨γ,[],0⟩`,
  `c0 = 0` and `isCluster γ.cl srvClusterN`), `memberRestartFacts_reg` (the facts at a fresh registry, term-level:
  `BI.sep_mono (pure_mono …) .rfl`), `crashImage_of` (the image `srvCrashImageAt` at the fresh registry from
  `memberDurOut`, `memberImageRows`, `walFilesC`, the handle and `ghostMapAuth r' 1 ∅`; its `srvImageM` at
  `{γ with reg := r'}` **is** `.rfl`: the registry is not read).
* Recipe learnt (for the rest of the proof): destructure `L`, `L'` (`⟨fl, lc, nh, gs, th, cr⟩`), `subst` the context
  equations, then `letI hG : HeapGS .hasLC GF := ⟨G, L0⟩` (without it `imod` finds no `BIFUpdate`); pass every
  generation-`L'` instance explicitly (`(hG := ⟨G, L1⟩)`, `(L := L1)`), never an anonymous constructor of `FsCtx` at
  `L1` (`theFs` at `L1`: `backend.theFs_eq GF (hG := …) (S := Sc) …`; `FsCtx`'s `hG` is a structure parameter, so
  `theFs` at `L0` is not `theFs` at `L1`); `iexact` unifies only reducibly, so a row equal by unfolding goes through
  `iapply (show P ⊢ P' from .rfl)` (or `have e : P ⊢ P' := .rfl` before `unfold`). `srvClusterN_rnDurKN` is not
  imported here: its proof is inlined.
* Checking: `/shared/tmp/t7-chk.sh [-a] [--goal L:C]` copies the file to fk-lean2's `etcd-safe-p8` worktree and runs
  `etc/lean-check.py` there (seconds per edit).

### T7 status and handoff (2026-11-25, session 5; branch `etcd-safe-t7`)

**Done** (`dist/crash/MemberCrash.lean`, no axiom, no `sorry`; build evidence below):
* The two open items of session 4, decided:
  - **The backend file's durable name goes in B1's keep `KeepB`**, as the named hypothesis `memberDbNamed.law
    KeepB` (crash rest in, `V'.now.entry J "db" = some (.file i0)` out, `KeepB` and the crash rest back). Why not
    `memberKeepR`: the record `dbCrashKeep` holds the claim on `db` (`bPath`), so no `nameCrash` can sit beside it
    (`nameCrash_crash` needs the claim); the name's commits are the backend's run's (bbolt's `Open`, the snapshot
    rename's `renamedDur`), which T10's invariant tracks. T8 only threads `KeepB`. The theorem gets one more
    hypothesis than session 4's list (`hB1n`).
  - **The path at `L'`** (`snapClaims_new`): from `osShared`'s whole claims, the spine `dd/member/snap` at the
    fraction `1` (claims `.only [member]`, `.only [snap]` split off `jd`'s and `jm`'s) and `J`'s whole claim. For it,
    `memberKeepR` now keeps the **concrete spine** `osSpineDur k.jd [member, snap] k.J` (not `osPathDur`; T8 builds
    it the same way, `osSpineDur_snoc`), with pure rows (T8's, from the boot's roots): `(dd, jd) ∈ R`,
    `(h.r, h.jr) ∈ R`, `h.r ≠ dd`, `IsUnder h.r h.dir`, `snapDirOf dd = joinPath dd [member, snap]`, and
    `∀ i, PathFits (snapDBPath sd i)` (`snapDir_split`'s premise). `MemberKN` gains `jd`.
* Pure geometry (`section geom`): `walk_two`; `notInArea` (no file of `J` is in a WAL area directory: `J`'s parent
  `jm` is a child, the area `jr` a root; what `walInv_crash`'s `hD` and `snapDir_crash.law`'s disjointness need);
  `mem_dirsOf`; `spineDirs` (`jd`, `jm`, `J` in the tree, pairwise distinct); `namesOf_only_cur`.
* `osCallPerms_two` (the data directory's and the WAL area's whole call permissions, at the keys of paths below
  them), `osCallPerm_halve`, `root_ne_nil`.
* `memberWal_crash` generalized to files `D` taken before it (`hD : ∀ i ∈ D, ¬ InAreaDir V'.now h.jr i`), its
  post gains `∀ i ∈ D', InAreaDir V'.now h.jr i`.
* `memberImage.law` (B1) returns `memberDurOut` (the image needs raft's state and vacancy after it).

**Next: `memberGen_crash_law_holds`** (`(hQ) (hA1) (hB4) (hB1) (hB1n) (hB6) (hD1) : memberGen_crash.law C cfg id
(memberKeep C cfg id KeepF KeepB) Q`), in this order (each step's lemma exists unless marked *new*):
1. `intro L L' V' hL hL'`; `obtain ⟨fl, lc, nh, gs, th, cr⟩ := L` (and `L'`), `simp only at hL hL'`, `subst` (as
   `BootBad.serverBadWp`), so `atCtx L` is `L` up to whnf. `iintro Hk Hlc #Hcr Hrest #Hosi` (`crashed`, `osInv`
   persistent). `iunfold memberKeep at Hk`; `⟨#Hcf, Hlc2, (HF | HR)⟩`; `memberClusterFacts_gen` for the cluster row.
2. First case: `hB4 L L' V' rfl rfl $$ HF Hlc Hcr Hrest Hosi`; `memberGen` = facts ∗ `ileft`.
3. Restart case: `iunfold memberKeepR`; `⟨%k, %hk, #Hrf, Hdur, Hwal, Hdb, Hsnap, #Hsp, HKB⟩`. Destructure `k` and
   `k.h` (`WalH` = `⟨⟨ext, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γ, md, γh⟩`),
   `subst` `ext = S` (`has.sem_eq.symm.trans` the ambient's; `semOk`/`has` are proofs, defeq), likewise `c`
   (`⟨S, ok, has, fa, fsa, ne⟩`); `hfs' : theFs (hG := new) = some c := hfs` (defeq: `theFs` ignores `hG`);
   `haveI := inj`.
4. Old generation: `iunfold memberWalKeep at Hwal` → `⟨Hwi, Hwt, #Hsh⟩`; `osSharedInv_rootsOk` → `RootsOk R`;
   `crashRest_treeWf'` → `TreeWf R V'.now`; `osSpineDur_crash … [member, snap] jd J $$ Hsh Hrest Hsp` → walk;
   `walk_two` → `jm`, `h1`, `h2`.
5. `hB1n L L' k Q [] false V' $$ HKB Hrest` → `hdb`; `dbCrash … (hA1 i0) [] (by simp) V' ⟨J, _, hdb⟩ ⊤ $$ Hdb Hcr Hrest`
   → `D'`, `fileHoldsM i0 D'`.
6. `memberWal_crash L L' h Q hQ V' [i0] (notInArea hwf h1 h2 hrR hdb …) ⊤ … $$ [Hwi Hwt Hsh] Hcr Hrest` → `W'`, `Dw`.
7. `crashRest_treeS' … (Dw ++ [i0]) …` → `V'.2 = []`, `osShared (L := L') R V'` (`⟨#Hsh', -, Hperms, -, Hall⟩`),
   crash rest at `true`. `snapClaims_new … hwf hRok hdR hsd h1 h2 $$ Hsh' Hall` → path `1`, `J`'s claim.
   `osCallPerms_two R dd r sd dir … hrne.symm (isUnder from hsd: isUnder_joinPath) hunder $$ Hperms`;
   `osCallPerm_halve` for the WAL's half.
8. `snapDir_split … 1 1 ⊤ … hfit $$ Hosi Hsh' Hp Hcs HJ` → slots, `db`'s claim, `q' qc'` path/perm, `.except` claim;
   `rw [← Qp.half_add_half q', ← Qp.half_add_half qc']`, `osPathS_frac`/`osCallPerm_split`; `snapDirOwn` (`unfold;
   rw [onFs_some hfs']`), the slots as `snapSlot` (`have hslot … onFs_some hfs'`, `simp only [hslot]`; never
   `iframe` next to the list).
9. `osPathDur` at the old generation from the spine and the rows (`unfold osPathDur; iexists dd, jd, [member, snap]`);
   `osPathDur_lookup` → `lookupH`; `snapDirKeptR_of` + `hD1` + `onFs_some hfs` → `snapDirKept`.
   Disjointness for `snapDir_crash.law`: `x ∈ Dw` by `notInArea` (with `hwp`), `x = i0` by uniqueness at `J`
   (`db` ≠ `snapDBName i`: `bootSnap.snapDBName_length`). Apply `snapDir_crash_law_holds L L' c c Q true V' (Dw ++
   [i0]) R J sd γd img Rm Rm …` with `Hlc2`, `Hsnap`, `Hcr`, `□ (∀ j, Rm j -∗ Rm j)`, the kept, `Hsh ∗ Hrest`, the own
   and slots → `snapDirKeep` at `L'` (keep its handle: `snapDirKeep_handle`).
10. `memberRestartFacts` → `ρo.rd.raft = ⟨γ, [], 0⟩` and `isCluster γ.cl srvClusterN` (*new* small lemma: unfold,
    `srvRaftLogInv` → `srvClusterOk` → `isCluster`); `memberDur_crash … ⊤ CoPset.subseteq_top srvClusterN_rnDurKN $$
    Hdur Hcl Hlc [Hwc Hcw]` → `S σ l`, `walFilesC`, `memberDurOut`. Watch the pitfall: `memberDur_crash`'s
    `isCluster` was elaborated with instances Lean picked; if `$$` fails, wrap it as `memberIsCluster` over one `HeapGS`.
11. `hB1 L L' V' k S σ l D' q'.half qc'.half hD' $$ HKB Hdo Hfm Hp2 Hc2 Hdbc` → `memberDurOut`, `memberImageRows`,
    the bounds.
12. Registry (Q4): `ghost_map_alloc_empty (K := Loc) (V := MemStorNamesRec)` → `r'`; `γ' := {γ with reg := r'}`,
    `ρ' := {ρo with rd := {ρo.rd with raft := ⟨γ', [], 0⟩}}`; *new* `memberRestartFacts_move` (as
    `memberRestartFacts_gen`, plus `rw [hr]` and the `*_reg` transports, `entails_refl`, of `Alloc3.lean`:
    `srvRaftLogInv`, `kvInv`, `srvPropMint`, `srvRdCtxInv`; `srvRLogLb_reg` for the image), with `hB6 L' ρo`.
13. `memberRestart` at `L'`: `iright; iexists ρ', γ'`, `⟨r', rfl⟩`-style pure row (`γ = {C.γ with reg := r}`),
    `srvCrashImageAt γ' ρ' id dd S σ i A D m ∅`: rows from `memberDurOut` (`.rfl` across generations,
    `memberDurOut_gen`), `memberImageRows`, the bounds, `srvFilesC` (`walFilesC` at `{h.toWalA with W := W'}`, `a.dir =
    h.dir = srvWalDirOf dd`), the snapshot row (`snapDirKeep_handle` at `L'` + the counter authority; `srvImageM`
    at `γ'` is `srvImageM` at `γ` if it does not read `reg`, else a transport lemma).

Build evidence (session 5): fk-lean2, worktree `etcd-safe-p8` at `f27b5f6d36`, `lake build
…dist.crash.MemberCrash`: `[4515/4515] Built …MemberCrash`, `Build completed successfully (4515 jobs)`, exit 0;
one linter warning (`walk_two`: the `walk` argument of the inner `simp only` is unused). Helper:
`/shared/tmp/t7-build.sh` (pushes `HEAD` as `etcd-safe-p8` to fk-lean2 and builds the module; log
`/shared/tmp/t7-build.log`).

## T10 design: the backend's image across a crash (2026-11-25, branch `etcd-safe-t10`; design only)

Base `etcd-safe-t7` @ `7f26ddec0a`. Discharges T7's `memberImage.law cfg id KeepB` and `memberDbNamed.law KeepB`
(B1), with B2 and B3. Draft statements: `dist/crash/BackendImage.lean` (defs tier, definitions and `abbrev` laws
only; checked with `etc/lean-check.py` on fk-lean2's `etcd-safe-p8` worktree, `/shared/tmp/t10-chk.sh`, 0 errors).
No proof, no axiom, no `sorry`, no shared statement edited.

### 1. The invariant

**Where it lives.** Not in `memberKeepR` (T7): the record `dbCrashKeep` is used at *every* commit
(`dbCrashKeep_announce`, `_half`), so the running backend must hold it, and the crash frame gets it back only
through an invariant with a crash token (the `walInv`/`rnDurInvK`/`snapDirInvK` shape). The natural place is
the backend's commit invariant `cmtInv` (`backend/InvBackend.lean`), which already holds the committed data's
`dbHalf γ.db Dc` (the half `dbCrashKeep` absorbs) and is opened at each commit point:

* `cmtBody` becomes, for a crash-tracked backend (opened with `dbOpts`, etcd's default),
  `∃ Dl Dc pd, dbCrashKeep γ.db i0 Dl Dc pd ∗ KB Dl Dc pd ∗ fkRd … ∗ cmtRegs … Dc` (or `bStopped`), and
  `cmtInvK := inv cmtN (cmtBody ∨ crashed ∗ token γk)`; `KB` is the client's **crash payload** (a parameter of
  the backend's names, as `W`/`Pk` are), untracked backends (tests, `mvccfull`, defrag's temporary) take
  `KB := True` and the old body.
* The backend applies three **client laws** on `KB` (`kbAnnounce.law`, `kbLand.law`, `kbSync.law`, drafted):
  (a) at `unsafeCommit`'s hook step, after `OnPreCommitUnsafe` and before bbolt's `Commit` (with
  `dbCrashKeep_announce`): `KB Dl Dn none ∗ CV S ==∗ KB Dl Dn (some S) ∗ CV S`, `CV S` the batch lock's view of
  the session's data `S` (the lock's `W`, `Pk`, the readers' quarter, the hook's keys, the tracked buckets: what
  `obsWand` already gets); (b) at the commit point inside `dbCrashKeep_half`: `KB Dl Dn (some S) ⊢ KB Dn S none`
  (ghost); (c) after the commit returned, holding the fresh write transaction (`t.tx = begin(true)`): the
  **resync** `KB Dl Dn pd ==∗ KB Dn Dn none`, with the record's resync derived from C-I1 as
  `_clear; _close; _new` (no new axiom; needs C-I1's record without the path, below).
* The server's payload: `KB Dl Dn pd := bkPayload γ ρ Dl Dn pd ∗ ciFloorAuth γc (ciOf Dl)` (drafted:
  `bkPayload`, every data a crash can leave is an image, `bkImgAny`; `ciFloorAuth` a monotone counter at the
  stored index of the fallback, raised by (c), whose lower bound `ciFloorLb γc j` the own snapshot's `SaveSnap(j)`
  takes after its `ForceCommit`: B2's own-snapshot case). Beside it, in the **server's** crash-aware invariant
  (`bkKeepInvK`, T10's, the token in `KeepB`): the durable name of `db` (below), the snapshot directory's removal
  counter's authority `monoNatAuthOwn γm 1 c` with `c ≤ max(ciOf Dl, σ.b) + 1` (the apply thread keeps a
  fraction-free view through the invariant instead of owning it), and which backend (`γb`, `i0`) is current.

**What each commit deposits.** The image facts `bkImg γ ρ i A S m` of the announced data `S` (rows of
`srvCrashImageAt`: `srvRLogLb A`, `i = ai0 + |A|`, `imageRestAt`, `imageStOk`, `mvccImage`, `confAt`, the
membership row) at the hook step, from: (i) mvcc's **`mvccImage_commit.law`** (proposed, mvcc API: the writer's
resource `W` at a commit's hook step gives `mvccImage S σ.log σ.crev u` for mvcc's state `σ`, `σ.pending = none`;
the generalization of `mvccImage_snapshot.law`, whose AU already fires at `Snapshot`'s commit), (ii) **the image
row of the batch lock's invariant** (`batchLockInv`, T10's new row): whenever the batch lock is free, the stored
index's mirror `mm.1 = i` comes with a committed prefix `A` reaching `i`, mvcc's state at the KV model of `A`
and the tracked buckets at `restModel … A`. The apply thread re-establishes the row at each `Unlock` (it holds
`srvRLogLb A` and the applied log; the row is what it already knows at quiescence, `stop_imageAt`, made true at
every unlock).

**Specs it touches** (shared = T4's / the lead's / another owner's; own = T10's):

| spec / definition | change | owner |
|---|---|---|
| C-I1 `dbCrashKeep` and its six axioms (`backend/CrashInterim.lean`) | the record drops `path` and the claim `bPath` (the crash law never used the name: it takes `Named V'.now i0`); `_new` stops consuming `bPath`, `_close` stops returning it. Needed: the snapshot install renames onto `db` while the old backend still commits (Go's `applySnapshot` closes the old backend only after `kv.Restore`), so the record cannot hold the name. A weakening of preconditions; **needs an `axiom`-skill re-review** | shared (C-I1's owner, the lead) |
| `cmtBody`/`cmtInv`, `newPostK`, `backend.New.spec`, `storage.OpenBackend.spec`, `OpenSnapshotBackend.spec` (their `γ` gains `KB`, `γk`, the post a `dbCrashKeep`-backed invariant) | new crash-aware body; the open's post gives the token | shared (backend's API, `etc/api/backend.txt`) |
| `batchTxBuffered.unsafeCommit`/`commit`/`Commit`, `backend.ForceCommit`, `backend.Close` (`bStopped`), `backend.Snapshot` proofs | apply (a)-(c) and the record laws | T10's (proofs inside the backend) |
| mvcc `mvccImage_commit.law` | new API law | shared (mvcc API) |
| `batchLockInv` (`etcdserver/InvApply.lean`) | the image row | T10's (server internals) |
| `applyEntryNormal`, `applyConfChange`, the deferred `SetConsistentIndex`, the compactor's unlocks, `applySnapshot` | keep the row at every unlock; the install's record swap | T10's |
| `raftNode.start`'s `SaveSnap` (T2's `rnDurInvK` records) | each saved snapshot index `j` with `ciFloorLb γc j ∨ snapSaved γd j` | T2's invariant (coordinate) |
| `srvCrashImageAt`, `wal.crashImage`, `bootstrapCrashContract`, `NewServer.specC` | restated (§2) | **shared: T4's** |
| `memberKeepR`, `MemberKN` (T7) | the `dbCrashKeep` row and the fields `γb i0 Dl Dn pd` leave `memberKeepR` (they move into `KeepB`) | T7's |
| `memberImage.law`, `memberDbNamed.law`, T7's `dbCrash` step | replaced by `memberBackend.law` (drafted) | T7's |

### 2. How it gives T7's laws; B2, B3; the restatement of T4

**`memberBackend.law cfg id KeepB`** (drafted; replaces `memberImage.law`, `memberDbNamed.law` and T7's own
`dbCrash` step, step 5 of session 5's plan): `KeepB L k` (the token of `bkKeepInvK` and of the backend's
`cmtInvK`), `crashed`, `memberDurOut` (for `σ`), the crash rest with nothing taken, the new generation's claim on
`db` and path/call shares ⊢ `∃ i0 i A D m, ⌜V'.now.entry J "db" = some (.file i0)⌝ ∗ crashRest … [i0] … ∗
memberDurOut ∗ memberImageRowsR k dd σ i A D m`. Proof: open both invariants with their tokens (record and
payload out); the durable name of `db` (below) gives the entry; `dbCrash` (C-I1, premise `BoltCrashWhole`) gives
`fileHoldsM i0 D'`, `D' ∈ {Dl, Dn, pd}`; the payload gives `bkImg … D'`; `fileHoldsM` with the new claim gives
`fileHolds (backendPathOf dd) D'`; the counter's authority and its bound with `σ` give `snapRowB2`. T7's proof then
loses its `hB1`, `hB1n` and the `dbCrash` call, and takes `hB1' : memberBackend.law cfg id KeepB`.

**The durable name of `db`** (what `memberDbNamed.law` asked): a `nameCrash`-style promise about the name `db` in
`member/snap` (`backend/FileDur.lean`: `CrashLeaves h J "db" P n` with `osCommitLb n`), kept in `bkKeepInvK`:
`P = (· = some (.file i0))` from the first boot's directory sync (`bootstrapNewWAL`'s; C-I1's notes) and after the
install's `syncDir` (`renamedDur`, which `OpenSnapshotBackend.spec` already gives); **inside the install window**
(the rename issued, its sync not returned) `P = (· = some (.file iOld) ∨ · = some (.file iNew))`, so the keep is a
disjunction over two records (the old backend's, still committing to an inode that may lose its name, and the new
one's, made by `_new` at its open). The rename is one directory entry change: in the crashed tree either `db`
names `iOld` and `<k>.snap.db` names the snapshot's file again, or `db` names `iNew`; the law picks the record by
the entry.

**B2 (the received-snapshot window).** Go's order: the transport saves `<k>.snap.db` durably (`SaveDBFrom`,
`snapSaved γd k`), raft's `Ready` carries the snapshot, the raft loop `SaveSnap`s `k` (synced), the apply thread
waits for it (`<-apply.notifyc`) and runs `OpenSnapshotBackend` (counter to `k + 1`, rename, `syncDir`). A crash
after the `SaveSnap` and before the rename's sync leaves `σ.b = k > i` (the old backend). Invariant (T2's records,
deposited at `SaveSnap`): every saved snapshot index `j` has `ciFloorLb γc j` (own snapshot: `ForceCommit` at
`j` returned before `SaveSnap`, so the fallback's index is `≥ j` after the resync) or `snapSaved γd j` (received).
So after a crash `σ.b ≤ i` or `snapSaved γd σ.b`, and: before the install's take, the file is still in T6's
invariant (`c ≤ σ.b`); after it, if the rename did not survive, the file is back under its name and T10's keep
(which received it from `snapHeld` through `OpenSnapshotBackend`) hands it to the image (`c = σ.b + 1`,
`fileAt … ∗ □ srvImageM … σ.b Ds`). That is `snapRowB2` (drafted).

**B3 (`bootLen ≤ i`).** Reachable values of `i` after a crash once the first `Save` is durable (else B4's first
case, the fork's discard): `0` (no commit since the boot: the meta keys never written, `UnsafeUpdateConsistentIndex`
never saves `0`) and every `k` inside the bootstrap batch (the backend's timer commit between two bootstrap
`AddMember`s, each its own `LockInsideApply` cycle). `restModel c0 boot (A)` is defined for any prefix (`restBootBk`
has empty member buckets, `memBoot` is in memory only), so the image at `i < bootLen` is meaningful: drop the row.
Two leftovers for T4/T3 (not T10's): at `i = 0`, `imageRestAt`'s meta clause must accept absent keys, and a file
whose buckets `NewServer` has not yet committed (a crash after the first `Save` but before the buckets'
commit, if reachable) is T3's backend leftover, not an image.

**New finding (membership row).** `applyConfChange` calls `beHooks.SetConfState` *before* the change's
`AddMember`/`RemoveMember` takes the batch lock with `LockInsideApply` (which moves the stored index): a timer
commit in between stores the new `confState` with the old index `k - 1` (`OnPreCommitUnsafe` writes a dirty
`confState`). `∀ cs, v3ConfStateIs D cs → confStateIs cs m` at `m = confAt (k - 1)` is then false. Not a Go bug
(the restart reapplies entry `k`; in `etcd_safe`'s static cluster only the bootstrap batch has conf changes),
so no `issues/` file; a spec defect (ledger 2026-11-25, "T10"). Weakened row: `confRowW` (the configuration at
`i` or at `i + 1`). A Go test would confirm the window.

**The restatement of T4's `srvCrashImageAt` T10 needs** (exact text: `srvCrashImageAtR`, `wal.crashImageR`,
`snapRowB2`, `confRowW` in the draft file):
1. `wal.crashImage cl S σ i` → `wal.crashImageR cl S σ` (drop `σ.b ≤ uint.nat i`);
2. drop `⌜γ.cl.bootLen ≤ uint.nat i⌝`;
3. `⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝` → `confRowW γ.cl i D m`;
4. the snapshot row `⌜γ.snapLoc id = some γd ∧ c ≤ uint.nat i + 1⌝` → `⌜γ.snapLoc id = some γd⌝ ∗ snapRowB2 γ dd σ i γd c`.
And correspondingly in `bootstrapCrashContract`: drop `σ.b ≤ uint.nat i` and `γ.cl.bootLen ≤ uint.nat i` from its
premise (keep `γ.cl.bootLen ≤ σ.commit`), add the `.snap.db` case (`recoverSnapshot` opens `<σ.b>.snap.db` when
the backend's index is below it: `beExist`/`ci` cases, T9's), accept absent meta keys at `i = 0`. D-T7-2 (the
snapshot directory's token) is independent and stays as proposed.

### 3. Draft statements

`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/crash/BackendImage.lean`, namespace `bkImage`: `confRowW`,
`bkImg`, `bkImgAny`, `bkPayload`, `kbAnnounce.law`, `kbLand.law`, `kbSync.law` (over an abstract `KB` and the
backend's `CV`), `wal.crashImageR`, `snapRowB2`, `srvCrashImageAtR`, `memberImageRowsR`, `memberBackend.law`.
Not drafted (internal to sealed modules, written with their proofs): `cmtBodyK`/`cmtInvK` (backend), the
`batchLockInv` row, `bkKeepInvK`, `mvccImage_commit.law`.

### 4. Estimate and risks

| piece | lines |
|---|---|
| C-I1 restatement (record without `path`) + derived resync lemma + re-review | 50-100 |
| backend: crash-aware `cmtInv` with `KB`, the opens' posts, `unsafeCommit`/`ForceCommit`/`Close`/`Snapshot` re-proved, the backend-level crash lemma | 800-1400 |
| mvcc `mvccImage_commit.law` and its proof inside mvcc | 300-600 |
| server: `batchLockInv`'s image row kept at every unlock (normal entries, conf changes, the deferred index moves, the compactor), `bkKeepInvK` (name, counter, current backend), the install window, `SaveSnap`'s floor/`snapSaved` deposit | 1000-1600 |
| `memberBackend_law_holds` and T7's adaptation | 200-400 |
| total | **2400-4100** |

**Riskiest step: the image row of `batchLockInv` at every unlock.** Today the image is proved only at quiescent
points (the graceful stop, `Snapshot` from the apply thread between entries). At an arbitrary unlock the apply
thread may be inside an entry: the conf-change window above (already forces a weakened spec), entries whose
index moves without the lock (`applyEntryNormal`'s deferred `SetConsistentIndex`, a rejected conf change's
`SetConsistentIndex`: harmless only if the entry wrote nothing), and the compactor's own batch cycles after the
index moved (covered by `mvccImage`'s unfinished-compaction bit, to be checked). Second risk: the install window
(two records, the name's disjunctive crash promise, the `.snap.db` file moving between T6's invariant and T10's
keep). Third: C-I1's restatement must survive review. Do first: a Go test of the conf-change window, then the
row's statement against `applyConfChange`'s proof.

### T10 status and handoff, session 2 (2026-11-25, branch `etcd-safe-t10`)

**Done (the order's step 1; built on fk-lean2, `BackendImage`, `NewServerCrash`, `etcdserver.CrashInterim`: 4521 jobs, 0 errors).** The two approved restatements (coordinator-E, #50 comment 2026-11-25T15:22:46Z,
items 2 and 8; ledger entries marked approved, a new C-I1 entry listing `_new` loses a premise, `_close` returns
less):
* C-I1 without the name: `backend/CrashInterim.lean` (`dbCrashKeep γ i0 Dl Dn pd`; `bPath` gone from `_new`'s
  premises and `_close`'s result; the review's docstring fixes, and `memberDbNamed.law`'s). The install window has
  one record (the fork syncs the directory before it opens the new file): §1's "disjunction over two records" is
  superseded; the `db` name's crash promise inside the window is `iOld ∨ iNew` with only the old record, the
  received file still `snapHeld`/`fileAt … Ds`.
* T4's `srvCrashImageAt` (`etcdserver/InvCrashImage.lean`): `wal.crashImageR`, `confRowW`, `snapRowB2` moved there
  from the draft (the draft `dist/crash/BackendImage.lean` keeps only T10's own definitions and laws);
  `bootLen ≤ i` dropped. `bootstrapCrashContract`: two cases, the backend kept (`σ.b ≤ i`, no `bootLen ≤ i`) and
  the `.snap.db` recovery (`i < σ.b = j`, the caller gives `<j>.snap.db` holding an image `Ds` at `j`, the post at
  `(j, Ls, Ds)`). `σ.b ≤ i` could not be dropped outright: with only the old backend file in the pre, Go opens the
  `.snap.db` when it exists and the post at the old `D` would be false. "Absent meta keys at `i = 0`" needed no
  change: `imageRestAt` already accepts them (`encMeta 0 = none`).
* Fixed what they broke: `srvCrashImageAt_disk` (`NewServerRAt.lean`) now returns the graceful image or the crash
  image with the reason (`¬ (i ≤ σ.commit ∧ σ.b ≤ i ∧ bootLen ≤ i ∧ conf strict)`); `NewServer.wp_proofC`'s one WIP
  `sorry` (T4's, unlinked) takes all the non-graceful cases; `bootstrapAtR_of_crash` takes the first case;
  `memberCrash.crashImage_of` builds the weakened rows from T7's strict ones. The C-I2 law's docstring says the new
  case needs its own `axiom`-skill review before the law becomes an axiom.

**The riskiest step, refined by reading the protocol (no Lean yet).** The image row belongs in the apply protocol's
invariant `consInv` (`InvApply.lean`), not in `batchLockInv`: the protocol's state `s = (k, p, eff, pending)`
already says what a commit stores (`commitOk s m`: `eff ≤ m ≤ p`, `commit_save_au`), and the steps that move it are
few (`hook_set_au`, `writes_done`, `skip_done`, `ci_advance_au`, `ci_swap_au`, the freeze). Proposed row, in
`flightInv`'s `false` branch (and kept through the `pending` one): `∃ A, srvRLogLb A ∗ ⌜uint.Z s.p = ai0 + |A|⌝ ∗
⌜∀ m, eff ≤ m ≤ p → the KV model and `restModel` of `A`'s prefix at `m` are `A`'s⌝` (the entries in `(eff, p]` wrote
nothing). Then at a commit `commit_save_au`'s `Ψ` gets the image index `m` with a prefix whose models are the batch's;
`mvccImage_commit.law` and the hooks' keys (`CV S`) give `S`'s image. Obligations: `skip_done` takes "entry `i` is
model-neutral" from its callers (`applyEntryNormal`'s no-write paths, a rejected conf change); `writes_done` takes the
new `A` (the apply thread's `kvApplied`); `confRowW` absorbs `SetConfState` before `LockInsideApply`. The row keeps
`consInv`'s openers (`consInv_open`/`_close`) unchanged if it is added inside `consInvAt`/`consFrozen` with its own
accessor lemmas. Next session: write the row and re-prove the five step lemmas in `InvApply.lean`, then their callers.

**Handoff order** (coordinator, relaying the etcd_safe lead, #50 15:29Z; ledger entries marked approved, not yet
applied). On this branch, before the riskiest step, as they touch the same statements; `NewServer.specC`'s proof is
the lead's `sorry` (T4): edit only its statement and move its callers.
1. **D-T7-2:** `srvCrashImageAt` holds `snapDirKeep` (handle and token), and `NewServer.specC` returns the token.
2. **B6 (a):** `memberRestartFacts` drops `idPfxInv`; `NewServer.specC` allocates a fresh one under the new
   incarnation's names; T7's `memberPfx.law` hypothesis goes.
3. **D-T7-1:** `snapDirKept`/`snapDirKeptF` restated at the law's own `R`; P7's `old_dir` gets `R0 = R` from
   `crashRest_roots`; T7's `snapDirKeptOf.law` hypothesis goes.
4. Then the riskiest step above (the image row in `consInv`), then the design's order.
Base: merge `etcd-safe-main-r4/2026-11-25` (the lead's r3 + d6t4b + t7) once the lead posts its head.


### T10 status and handoff, session 3 (2026-11-25, branch `etcd-safe-t10`)

Base: `etcd-safe-main-r4/2026-11-25` not posted yet (no such branch on origin); not merged.

**Done** (order items 1 and 3; ledger entries marked applied):
* **D-T7-2**: `srvCrashImageAt`'s snapshot row holds `snapDirKeep` (handle and token). New `srvSnapKeep γ id dd`
  (`InvCrashImage.lean`: `∃ γd γm, ⌜γ.snapLoc id = some γd⌝ ∗ snapDirKeep …` at the image's `img`/`Rm`);
  `NewServer.specC`'s post returns it beside raft's crash token, in both outcomes. `srvCrashImageAt_disk`'s graceful
  case returns it (the graceful image keeps the handle, `snapDirKeep_handle`), `NewServer.wp_proofC`'s graceful branch
  frames it (its WIP `sorry`, T4's, unchanged: the non-graceful case keeps the whole image). T7: `crashImage_of` and
  `memberGen_crash_law_holds` pass the new generation's `snapDirKeep` whole (the token is no longer dropped). The
  post's `γm` is existential: T8 ties it to `memberKeepR`'s `k.γm` when it builds the keep.
* **D-T7-1**: `snapCrash.snapDirKeptF` at the law's roots; `old_dir` at `R`; the step lemmas take the law's
  `osSharedInv R` and get `R0 = R` from `crashRest_roots` (moved from `MemberCrash.lean` into `SnapDirCrash.lean`).
  `memberCrash.snapDirKeptR` has `snapDirKeptF`'s body (converted by `iunfold` in the assembly); **T7's
  `snapDirKeptOf.law` (`hD1`) is gone.**

**Build** (fk-lean2, `MemberCrash`, `NewServerCrash`, `CrashInterim`: 4520 jobs, exit 0; tier check ok; no axiom
or `sorry` added: `NewServer.wp_proofC`'s one WIP `sorry` (T4's) unchanged and absorbs nothing new). T7's theorem's
hypotheses now: `hQ`, `hA1`, `hB4`, `hB1`, `hB1n`, `hB6` (D-T7-1's `hD1` gone; D-T7-2 needed none, its token is now
kept).

**Next session, in order** (crash work off the critical path since #50 16:48Z): B6 waits on D7/T8's decision; then
P5's certificate route (below, approved); then the `consInv` image row.

**Not done, stopped (hard rule):**
* **B6 (a)** does not go through as approved: `idPfxInv`'s names are a persistent element of the cluster's `gen` keyed
  by the prefix alone, and a new incarnation keeps `gen` and the prefix, so no fresh `idPfxInv` can be allocated at
  them; any fix restates idutil's shared definitions (ledger, B6 entry, options (a') and (b)). `memberRestartFacts` and
  `NewServer.specC` unchanged; **T7's `memberPfx.law` stays.** Needs D7/T8's decision.

**Handed off (budget):**
* **P5's item (a)** (lead, #50 16:06:56Z; ledger entry "the crash image's WAL row names its history"): (1) `walFilesC`
  names `Hs = walSrvHist d.H` (users: `WalRecsCrash`, `WalRecsH`, `InvRestart` (`srvFilesC`), `SrvCrash`,
  `StopShutdown`, `InvCrashImage`, `MemberCrash`; try in place: `walFilesC a id cid σ Hs sized` with
  `⌜walSrvHist d.H = Hs⌝`, `srvFilesC` keeps `∃ Hs` for the graceful slot and a named variant `srvFilesCH … Hs` for
  the crash image); (2) `srvCrashImageAt`'s files row `∃ Hs, srvFilesCH … Hs ∗ walHistCerts γ.cl sd Hs` (`sd`: the
  snapshot directory's durable indices, as `WalNamesK.sd`; T7 from `rnDurK_crash.law`, whose post must gain the
  certificates: not on `etcd-safe-p5`, so a hypothesis of `memberGen_crash_law_holds`); (3)
  `bootstrapCrashContract`'s two cases: the pre's image row's `walHistCerts` handed to the post unchanged, the post
  naming the opened WAL's history `Hs`; (4) `bootstrapRestartContract`, `srvDiskImageAt` certificate-free.
* **The image row in `consInv`** (order item 4; design in session 2's handoff; ledger entry "the backend's image row
  lives in the apply protocol's `consInv`", approved, internal).
* **C-I2 `.snap.db` review (sound, `notes/axiom-review/c-i2-snapdb.md`) followed up**: the case-2 argument added to
  `bootstrapCrashContract.law`'s docstring and the header's fork updated to the pin `e94f33b50`; the two caller
  obligations on `snapRowB2` recorded on it: (1) the file `<σ.b>.snap.db` in the `c ≤ σ.b` branch is kept by the
  directory's invariant (saved, its `Rm` refuted by the counter at `c ≤ j`; the fork's `purgeFile` no longer purges
  `.snap.db`, `a4d2bb172`), to be taken with `snapDir_take` at the restart; (2) its stored index is `j` by the image
  certificate's `imageRestAt`. No ledger entry needed (nothing could not be kept).


### T10 status and handoff, session 4 (2026-11-25, branch `etcd-safe-t10`)

**Merged `bbolt-crash/2026-11-25` @ `249a3f60fe`** (the bbolt-crash lead's C-I1 restatement, reviewed sound in
`notes/axiom-review/c-i1-monotone.md`, `c-i1-takeput.md`): bbolt's prefix-ordered `BoltCrashWhole`
(`Spec/go_etcd_io/bbolt/CrashPremise.lean`), `dbCrashKeep γ i0 Dl Dn` (no `pd`), `_take`/`_putSame`/`_putStep`
over `dbHalfV`, `dbCrash` with its mask premise; `Tx.Commit.spec` versioned. No textual conflict; followed up toward
the lead's statements: T7's `MemberKN.pd` removed (and `memberImage.law`'s third disjunct); the draft
`dist/crash/BackendImage.lean`: `bkPayload γ ρ Dl Dn`, `kbStep.law` at the commit point (the image of `S` given
there, with `CV S` framed into `Tx.Commit`'s update) replacing `kbAnnounce.law`/`kbLand.law`, `kbSync.law` without
`pd`. The "T10 design" section's announce step above is superseded by this.

**B6: options** (analysis only; the lead decides). Facts that fix the choice: (i) the cross-incarnation freshness
of ids is the issue record's (`GooseLang/Ext/IdIssue`): its crash keeps every entry as `id ↦ none`, and the restart
already gets `idIssueCrashStart hL hL'` in its crash rest (`etcdstart/NetExtsCrash.lean`), which turns an old
`idIssueFragAt hL id g` into `idIssuePastAt hL' id`; `idIssueFrag_past` refutes a new issue of it. So every option
needs one crash step converting `idPfxBody`'s `Ip` facts into past facts at `L'`. (ii) `Gp` (generators by heap
`Loc`) is used only by `NewGenerator` for `idClusterOk`'s clause 3 (distinct generators among a prefix's keys); a new
heap reuses `Loc`s, so clause 3 must be restricted to keys of one incarnation (`k.2 = k'.2`), which makes it
trivial (a key is `(p, inc)`), and `Gp` with its heap points-to can go, if `Ip` tags each id with its incarnation.
* **(a') per-incarnation names.** `gen` keyed by `IdKey` (or `p ↦ γpi`, a per-prefix map `inc ↦ (γip, γgp)` whose
  authority the member keeps: a new key needs an authority, and `gen`'s is the cluster's, allocated once); a fresh
  `idPfxInv` per incarnation allocated by `NewServer.specC` (B6(a) as approved), seeded at the crash with past facts
  for the earlier keys' ids, read out of the old invariants (persistent, open-and-close at `⊤`). Statements:
  `idPfxInv`'s argument becomes a key in `NewGenerator.spec`, `NewServer{,R,Crash}.spec`, `NewServerDist`
  (internal specs, no top-level change), `memberRestartFacts`, the `Alloc*` files. Cost ~600-900 lines (two-level
  names, five spec files and their callers, the seeding). Risk: the seed must cover every earlier key, kept by the
  keep across many crashes.
* **(b) crash-aware `idPfxInv` at the same names.** A cancellable invariant (its token in the member's keep); the
  crash law cancels it at `L`, keeps the authorities, converts `Ip`'s entries (`(inc, g)`: current or past) and
  re-allocates it at `L'` with the same `(γip, γgp)`. `idPfxInv gen p`'s form unchanged, so no spec statement
  changes; `idPfxBody`, `idKeyGenFacts`, `idClusterOk` clause 3, `NewGenerator`/`Next` (217 + 461 lines, the
  body-opening parts), the `Alloc*` files (the token) do. T7's `memberPfx.law` is proved by the crash law. Cost
  ~350-500 lines. Risk: low; the keep gains a token (T8).
* **(c) a generation-free `idPfxInv`** (new). The body holds no heap fact: `Ip : id ↦ (inc, g)` with
  `idIssueElemAt hL id (if inc = cur then some g else none)` at the record's current names `hL`, kept in a ghost
  register (`cur`, with an incarnation ↦ record-name map whose elements are persistent, so `Next` reads
  `cur = gooseIdIssueGS L` from its own key); `Gp` dropped by (ii). Then `idPfxInv` carries over by `.rfl` like the
  other restart facts (`memberRestartFacts_gen` with no exception), nothing is re-allocated, and the crash step is a
  ghost update of the one invariant (`idIssueCrashStart` turns each entry past, `cur` moves to `hL'`). Statements as
  (b) (none at the spec level), plus the register's allocation in `Alloc*`. Cost ~400-600 lines (the register is the
  new part). Risk: medium, in the register's protocol (who holds which half when `Next` and the crash step run).
* **Recommendation: (b)**: it changes no spec statement, uses the extension's crash rest as designed
  (`IdIssue/Crash.lean`'s header names `idPfxBody`), and its only new ownership is a cancel token in the keep.
  (c) is cleaner (no keep row, `memberRestartFacts_gen` without exception) but its register is a new protocol;
  take it only if T8 prefers no token. (a') costs the most and changes five specs. Under all three, clause 3's
  restriction and `Ip`'s incarnation tag are the same first step (`NewGenerator`, `Next`), doable before deciding.

**Build (unfinished at handoff):** fk-lean1, worktree `~/eg/wt/etcd-safe-t10` (moved from `etcd-safe-n7kv-nc2`), targets `MemberCrash`, `BackendImage`, `NewServerCrash`, `backend.CrashInterim` at `6887489844`, started 23:2xZ via `/shared/tmp/fklean1-check.sh`; log `/shared/tmp/t10-s4-build.log` (exit 1: one error, `BackendImage.lean:83` `Decidable (S = Dn)` in `kbStep.law`; fixed after the build with `open Classical in`, as C-I1 opens `Classical`, not rebuilt). Next session: rerun the same command with `FKLEAN_HOST=fk-lean1` (incremental) and fix what fails.

**Next session:** after the lead's B6 decision, that change; P5's certificate route and the `consInv` image row as in
session 3's handoff, the image row now at `kbStep.law`'s commit point (inside `Tx.Commit`'s update, C-I1's
`_take`/`_putStep`).

### T10 status and handoff, session 5 (2026-11-26, branch `etcd-safe-t10`)

**Step 1 (green):** session 4's targets (`MemberCrash`, `BackendImage`, `NewServerCrash`, `backend.CrashInterim`) at
`689a8b5e62` rebuilt incrementally on fk-lean1 (`FKLEAN_HOST=fk-lean1 /shared/tmp/fklean1-check.sh /shared/etcd-grove-t10
etcd-safe-t10 <targets>`): only `BackendImage` recompiled, exit 0 (`/shared/tmp/t10-s5-build1.log`).

**Step 2: B6's shared first step** (commit `7e8b4e3a3f`; ledger 2026-11-26), in `idutil` only (`Defs`, `NewGenerator`,
`Generator__Next`):
* `idPfxBody`'s ids' map is `Ip : id ↦ (inc, g)`; each entry holds `idIssueFragD id g`, `g ↪[γgp]□ inc` and its element;
  `idKeyGenFacts`' elements are `id ↪[γip]□ (k.2, g)`.
* `idClusterOk`'s clause 3, restricted to keys of one incarnation, is `k = (k.1, k.2)`: dropped (five clauses now; the
  `Hok.2…` projections in `Next` and `idIncarnation_alloc` shifted).
* `Gp` could **not** be dropped. The issue record is keyed by `Loc`, so `Next` still needs a way to tell, inside one heap,
  which incarnation a generator `g` belongs to (an id already issued by `g` must be its own key's). `Gp` is kept for that,
  but re-scoped as `Gp : Loc ↦ inc`, with heap fact `∃ v, prefix ↦□ v` and its name `γgp` per allocation of the
  invariant: `idPfxInv gen p := ∃ γip γgp, p ↪[gen]□ γip ∗ inv idPfxN (idPfxBody γip γgp)`. So `gen : w64 ↦ GName`,
  `idPfxTok` carries only `γip`, and `idPfxInv_alloc` allocates `γgp`. `idGen` holds the opened invariant with
  `g ↪[γgp]□ γi.inc` (registered by `NewGenerator`), replacing `idPfxInv γi.gen γi.pfx`. Its first four components are
  unchanged (`SrvRaftLog` reads them). No spec statement's text changes.
* For B6 (b), the re-allocation at the crash keeps `γip`'s authority and allocates a fresh `γgp` (empty `Gp`). The body
  also gains the past disjunct `idIssuePastD id` (to be added: an instance-free `idIssuePastAt` like `idIssueFragD`), and
  `Next` refutes it with `idIssueFragAt_past`.

**Build at handoff: running, result not seen.** fk-lean1, the 36 modules mentioning the changed names
(`etc/importers.py --uses …`, list in `/shared/tmp/t10s5/users.txt`) plus `BackendImage`, `NewServerCrash` and
`backend.CrashInterim`; log **`/shared/tmp/t10-s5-build2.log`** (ends `EXIT n`). `Defs`' cone is 2346 modules. Next session:
read the log. If it is unfinished, rerun the same command (incremental) with `FKLEAN_HOST=fk-lean1`:
`/shared/tmp/fklean1-check.sh /shared/etcd-grove-t10 etcd-safe-t10 $(cat /shared/tmp/t10s5/users.txt) <the three>`.
Fix what fails. The likely spots are `Next`'s new agreement steps (the `ig.2`/`ig.1` projections of literal pairs in
`bigSepM_lookup_acc`'s `Φ`, and `rcases ig'` under `hIp`) and `NewGenerator`'s `∃ v` frame.

**B6:** the lead (coordinator-E) had not answered on #50 by this session. Recommended option: (b).
### T10 status and handoff, session 6 (2026-11-26, branch `etcd-safe-t10`)

**Session 5's build** (`/shared/tmp/t10-s5-build2.log`) failed once, `Restart.lean:196` (`idKeyFact_pfxOk`
destructured `idClusterOk` into six parts; five since B6's first step). Fixed by name: `Defs.lean` has
`idClusterOk.issued/pfx/gen/domR/domF` and `idClusterOk.mk` (outside the instance-carrying `section ghost`, or
they pick up `[GooseExts] …`); `Restart.lean`, `Next`, `NewGenerator`, `Lemmas` and `Defs` itself use them. The
other positional reads left are IPM patterns over `idGen` (`SrvRaftLog`, `Lemmas`), whose trailing pattern
absorbs the rest. Build 1 (`/shared/tmp/t10-s6-build1.log`) got past `Restart` but failed in `Next` on the
section-variable problem (fixed since), and its target `backend.BackendImage` was misnamed: the module is
`Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.BackendImage`.

**B6 (b)** (etcd-grove-03 on #50, 00:33Z; the coordinator says the lead confirmed). Ledger 2026-11-26, "B6 (b)"
(it says why a `cinv` with a keep token cannot work: `Next` holds only the persistent `idGen`). Applied, **not
yet built green**:
* `GooseLang/Ext/IdIssue/Specs.lean`: `idIssueDeadAt hL` (the record's full authority), `idIssueCtx_dead`,
  `wp_IdIssue_live` (the update may give up with `idIssueDeadAt`), instance-free `idIssuePastD`/`idIssueDeadD`
  with `_eq` and `idIssueFragD_pastD`. `Crash.lean`: `idIssueCrashStart_dead`, `idIssue{Frag,Past}D_crash_pastD`.
* `idutil/Defs.lean`: `idPfxIdFact γgp id ig := (FragD id g ∗ g ↪[γgp]□ inc) ∨ PastD id`; `idPfxBody γip γgp :=
  GpPart ∗ (IpPart ∨ idIssueDeadD)`. `NewGenerator` uses only `GpPart`; `Next` uses `wp_IdIssue_live` (dead →
  give up; past entries refuted by `idIssueFragD_pastD`).
* `idutil/PfxCrash.lean` (new, defs tier): `idPfxInv_crash L L' gen p : idPfxInv(L) -∗ idIssueCrashStart(L,L')
  ={⊤}=∗ idPfxInv(L')`.
* `dist/crash/MemberGen.lean`: `memberGen_crash.law` gains `[HasExt idIssueExt]` and the hypothesis
  `idIssueCrashStart (gooseIdIssueGS L) (gooseIdIssueGS L')` (before `osInv L'`). `MemberCrash.lean`:
  `memberPfx.law` deleted, `hB6` dropped, the restart case reads the old `idPfxInv` out of `memberRestartFacts`
  and applies `idPfxInv_crash` (L, L' as the tuples `⟨fl, lc', …⟩`, `⟨fl', lc', …⟩`; `memberRestartFacts_gen`
  wants it at `atCtx L'`, defeq). Whoever applies `memberGen_crash.law` must pass the issue record's crash rest
  (`etcdstart/NetExtsCrash.lean`, `etcdNet_crashStart_split`).

**Build at handoff: build 3 running, result not seen** (fk-lean1, at `b663695717`: Specs/Defs/Next/NewGenerator/PfxCrash, **not** the
MemberGen/MemberCrash commit `80abc88fff`): log **`/shared/tmp/t10-s6-build3.log`** (ends `EXIT n`). Next
session: read it, then rerun with MemberGen/MemberCrash added (incremental, `FKLEAN_HOST=fk-lean1`):
`/shared/tmp/fklean1-check.sh /shared/etcd-grove-t10 etcd-safe-t10 $(cat /shared/tmp/t10s5/users.txt)
Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.BackendImage
Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerCrash Proof.go_etcd_io.etcd.server.v3.storage.backend.CrashInterim
Proof.go_etcd_io.etcd.pkg.v3.idutil.PfxCrash Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberCrash`.
Likely spots: `PfxCrash` (the `pure_forall` step building `Hall`, `ghost_map_lookup`'s instance under
`letI … idIssueAllG`, `inv_alloc`'s mask `⊤ \ ↑idPfxN` while the old invariant is open), `Next`'s dead branch
(`rw [idIssueDeadD_eq]` rewrites the IPM context) and the `rotate_left`s after `icases … (A | B)`, `MemberCrash`'s
`icases Hrf with ⟨⟨-, -, -, -, #Hp, -⟩, -⟩` (the fifth row of `memberRestartFacts` is `idPfxInv`).
No axiom, `sorry`, trusted text or top-level change.


### T10 status and handoff, session 7 (2026-11-26, branch `etcd-safe-t10`)

**B6 (b) built green.** Session 6's build 3 failed only in `GooseLang/Ext/IdIssue/Crash.lean` (lines 132, 146,
154: `rw [idIssue…D_eq]` with two `GooseLocalGS` in scope synthesized `L'` where the goal had `L`). Fixed by
naming the generation, `(L := L)`/`(L := L')`. Then `idutil/PfxCrash.lean`: iunfold takes its names
comma-separated; `go.Semantics` depends on the local context, so `idPfxInv_crash` takes one instance per
generation, `[semL : @go.Semantics _ L.goose_go_local_context go_gctx]` and `semL'` (no section `GoLocalContext`),
and `MemberCrash` passes `(semL := sem) (semL' := sem)` (both generations at `lc'` there); `(Mg !! id).isSome`
from `Option.isSome_iff_exists.2 ⟨ig, hI⟩`. `MemberCrash` reads `idPfxInv` with `memberRestartFacts`' flat pattern
`⟨-, -, -, -, #Hp, -⟩` (the fifth row). Build 5 (`/shared/tmp/t10-s7-build5.log`, fk-lean1, head `67af957a84`):
session 6's rerun targets (`/shared/tmp/t10s5/users.txt` plus `BackendImage`, `NewServerCrash`, `CrashInterim`,
`PfxCrash`, `MemberCrash`) all green. `etc/tier-check.py --check` ok. No axiom, `sorry`, trusted text or
top-level change. Nobody applies `memberGen_crash.law` yet; whoever does passes the issue record's crash rest
(`etcdstart/NetExtsCrash.lean`, `etcdNet_crashStart_split`).

**Next T10 items** (not started): P5's certificate route and the `consInv` image row (session 3's approvals).

### T10b status and handoff, session 1 (2026-11-26, branch `etcd-safe-t10b/2026-11-26`)

Assigned by coordinator-E (#50, 15:00Z): T10 item 2 (P5's certificate route) with the P5-RESTART `sorry`, T10
step 2 (the no-lock outcomes' model fact, mode `on`), T10 step 3 (the server's row, closing `NewServer.wp_proofC`'s
non-graceful case). Base `etcd-safe-crash-r6/2026-11-26` @ `8cdf5ff75f` with `etcd-safe-p5r/2026-11-26` @
`8c9642a9b2` merged (`ada6d74e2c`, clean). The brief's `plans/etcd-safe-crash-left.md` is in no branch and no
worktree on this host or fk-lean1; this session worked from this file's T10 sections and `notes/wal-p5-handoff.md`.

**Item 2 is blocked by the graceful restart (no Lean changed).** `rnRestartAllocK_law_holds` (the `sorry`) is
reached through `bootstrappedRaft.newRaftNode.wp_proof` from `NewServer.wp_proofRG`, the one proof behind both
restarts: `NewServer.wp_proofR` (graceful: `bootstrapRestartContract`, image `srvDiskImageAt`) and, through
`specRAt`, `NewServer.wp_proofC` (crash). `wp_proofRG` takes the WAL's history from `wal.restartOk`
(`wal.restartOk_startRK`, `NewServerR.lean:362`) and must hand `rnRestartAllocK` the certificates of every
snapshot record in it (`walHistCerts γ.cl sd Hs`, at `sd := fun _ => True` there, `bootstrappedRaft__newRaftNode.lean:223`).
The planned route (session 8's "Item 2", the lead's 2026-11-25T16:06:56Z conditions) gives them on the crash path
only: the crash image's files row and `bootstrapCrashContract`'s pass-through. On the graceful path nothing holds
them: `srvDiskImageAt` has only `wal.stopImage`'s `walSnapCert cl σ` (the records' own snapshot), the graceful
contract and slot stay certificate-free by the lead's condition, and the graceful stop's image is built from
`rnDurK_take.law`'s `walRecs h σ` and the closed WAL's `walFiles` (`StopShutdown.lean:680`), neither of which names
the history. So the route, done as planned, leaves the `sorry` in place (moved to the graceful case). Two ways on:
* **(A) the image route on both paths**: the graceful image carries the history's certificates too. Needs
  `rnDurK_take.law` to return the history with `walHistCerts` (the body has them, `InvWalCrash.lean:295`), the
  closed WAL's files naming their history (`raftNode.stop`'s `rnWalClosed`, the WAL's `Close` over the history),
  `StopShutdown`, and `srvDiskImageAt`'s body (a premise of `Spec/.../NewServerR.lean`, so a spec's meaning: the
  lead's call). Then `walFilesC`/`srvFilesC` name the history in both images, `wal.restartOk` names the opened
  history (the files' history: a claim of both contracts), and the certificates ride in the image, not the
  contracts. Large (raft loop stop, WAL close, server stop).
* **(B) P5's invariant needs no certificate of the restart's history** (recommended; P5's files only, no image,
  contract or trusted text change). `rnRestartAllocK.law` already takes `walSnapCert γn.cl σ`, the restart read's
  own certificate. At a restart nothing is pending (`HistReads σ Hs`), so every later read of `Hs ++ X` is based
  at `σ`'s base or at a snapshot record of `X`. The body's `walHistCerts γn.cl νk.sd Hs` becomes "the certificate
  of the restart read's base, and `walHistCerts` of the records after the allocation point `k`" (`k = 0` at a first
  start, where the two coincide); `walHistCerts_snapCert` gets that case; `rnDurK_crash.law`'s post drops
  `walHistCerts … Hc` (P5 session 6's addition for the image route; T7's `memberDur_crash` drops it today). Then
  the `sorry` is `walSnapCert` passed through, and `walFilesC`, the images, C-I2 and `wal.restartOk` stay as they
  are. Needs the pure lemma (reads of an extension of a restarted history are based at `σ`'s base or later), in
  `InvWalCrashPure.lean`.
Asked of the lead: (A) or (B). C-I2's text is unchanged on this branch (no before/after to record).

**Steps 2 and 3: not started** (not reachable this session). Step 2's applier part changes the `Pre` disjunct of
`cPost` (`apply/Contracts.lean:102`) into one with the step's no-effect fact, which `cPost` cannot state (it has no
step arguments): the component posts that produce `Pre` restate it, `cPost` reaches 16 `Spec/` files and 46 `Proof/`
files. The brief's trust rule makes that a stop-and-report before any `Spec/` text changes. Step 3 needs step 2's
fact at every `skip_doneR` site, and closing `NewServerCrash.lean:81` needs `wp_proofRG` for images that are not
graceful ones (the backend's index above the WAL's commit, `confRowW`'s second case, `snapRowB2`'s `.snap.db` case),
which the row alone does not give.

**Build**: fk-lean1, `~/eg/wt/etcd-safe-t10b` (seeded with `cp -a` from `etcd-safe-f7-runauth`, same Perennial pin
`a706aeb9a`); sync and build with `/shared/tmp/t10b-rb.sh [targets]` (`GATES=1` for `etc/gates.sh`; logs
`~/eg/logs/t10b-{build,gates}.log` there). The merge's full build and gates: see the STATUS entry of this session.

No axiom, `sorry`, trusted text, top-level premise or top-level statement changed.

**Handoff T10b-1** (stopped at the context rule; head = this commit, pushed):
* Item 2 (P5-RESTART): blocked, waiting on the lead's choice (A) or (B) above. C-I2 unchanged.
* Steps 2 and 3: not started (reasons above).
* The merge with p5r (`ada6d74e2c`) is **unbuilt**; no full build or gates ran.
* fk-lean1 seed copy **in progress at handoff**: `cd ~/eg/wt && cp -a etcd-safe-f7-runauth/.lake etcd-safe-t10b/`
  (source `~/eg/wt/etcd-safe-f7-runauth/.lake`, 63 GB, Perennial `a706aeb9a`; destination `~/eg/wt/etcd-safe-t10b/.lake`,
  a worktree of `~/eg/etcd-grove.git` checked out at `ada6d74e2c`; then `rm -rf .lake/lean-check`). Disk was 52 GB free
  at 17 GB copied: check `df -h ~` once it ends (about 6 GB left after it). If the copy is incomplete, `rm -rf` the
  destination's `.lake` and redo it.
* Sync and build: `/shared/tmp/t10b-rb.sh [targets]` (diff vs `ada6d74e2c`, deletes removed files; flock
  `~/eg/build.lock`, `MemoryMax=55G`, `--packages=.lake/package-overrides.json`); `GATES=1` runs `etc/gates.sh`
  (with `LAKE_PACKAGES`/`LAKE_OPTS` set). Logs `~/eg/logs/t10b-{build,gates}.log`. Delete read-only `.ilean`s on
  `permission denied`.
* Next: once the copy ends, the full build of the head, then gates in full; then item 2 by the lead's choice.

**T10b session 3** (2026-11-26): **(B) built; the P5-RESTART `sorry` is gone.**
* Fixes: `InvWalCrashPure.walFold_snapFrom`'s save case (`refine ih _ _ hA' ?_ h; exact hτ`: the fold's state after a
  save is a new record, `SnapFrom` holds by defeq); `InvWalCrashSteps`, both `walHistCertsK_snoc` calls at a snapshot
  record: `(by rw [walLastHS_snoc_snapP]; exact Nat.le_refl _)`.
* **`MemberCrash.lean:415`**: the one-token edit, approved by the lead through the coordinator: the trailing `-` pattern
  for `rnDurK_crash.law`'s dropped `walHistCerts … Hc` conjunct removed (`… #Hsd, #Hl⟩`). Nothing else in MemberCrash,
  `backend/CrashInterim.lean` or `NewServerCrash.lean` changed. No `Spec/`, `TrustedCode/` or axiom names
  `rnRestartAllocK.law` or `rnDurK_crash.law` (`git grep`).
* Full build green on fk-lean1 (29666 jobs). Gates (with `remote-check.sh`'s env: `PERENNIAL_CHECKOUT`, the caches under
  `~/eg/cache`; without it the Go and gen-init sections fail on the missing `/shared/tmp`): links, copy-part, **tcb (371
  axioms, 0 sorries: matches the baseline, nothing to update)**, all 69 collections match, goose, gen-init, tier, api,
  bounds 389, premisefix, k8s ok. `tcb-report --reuse --roots newRaftNode`: 2 roots, no `sorry`. The P5-RESTART
  `sorry` was in no baseline (none lists a `sorry`), so `--check --update` changes nothing.
* **Gates still failing, not from this change** (none names a file of it; they come with the merged full/crash lines):
  `mode` (20 unclassified lit-modes: `NewServerCrash.lean`, `NewServerRAt.lean`, `AuthViewDist`, `MemberLessor`,
  `MainLogger`, `MemberSplit`, `etcdstart/Start.lean`: entries for `etc/mode-allow.txt`), `featuregate` (the allow list
  names the etcd fork's old pseudo-version `20261124070122-df6af0c36a6b`, the programs now hit `20261125101634-251a430ce042`),
  `model-param` (117 rule-1 binders of the dist `wp_proof`s, `etcdInterceptorOk*`/`grpc*SvcAt`), `errdesc-check`
  (`KVGetDist.lean`, `WatchDist.lean` unreviewed). Owner: whoever lands the integration line.

**Handoff T10b-2** (session 2, 2026-11-26; stopped at the context rule; head = this commit, pushed). **(B) written, UNBUILT.**
Coordinator chose (B). No `Spec/`, `TrustedCode/`, image, contract or axiom text changed; no new `sorry` or axiom. What changed:
* `InvWalCrash.lean`: pure defs `SnapFrom σ0 X τ` (the read has `σ0`'s base and snapshot, or a snapshot record of `X` at its
  base) and `CertBaseK σ0 k Hs` (`k ≤ |Hs|`, `HistReads σ0 (Hs.take k)`, every prefix past `k` has last commit at least
  `Hs.take k`'s); `walHistCertsK cl sd Hs n := ∃ σ0 k, ⌜k ≤ n ∧ CertBaseK σ0 k Hs⌝ ∗ walSnapCert cl σ0 ∗ walSnapDur sd σ0 ∗
  walHistCerts cl sd (Hs.drop k)` (persistent). The body's `walHistCerts γn.cl νk.sd Hs` is now `walHistCertsK … Hs n`;
  `rnDurK_alloc.law` takes `walHistCertsK γn.cl sd Hs n`; `rnRestartAllocK.law` gains the premise `walSnapDur sd σ`
  (needed: the crash post gives `walSnapDur νk.sd σ`, and the law is ∀ `sd`); `rnDurK_crash.law`'s post drops
  `walHistCerts γn.cl νk.sd Hc` (the brief's choice).
* `InvWalCrashPure.lean`: **the lemma** `walRead_ext_snapFrom (hr : HistReads σ0 H0) (hc : c(H0) ≤ c(H0 ++ X))
  (h : walRead (H0 ++ X) = some τ) : SnapFrom σ0 X τ` (with `c(H) = uint.nat (walLastHS H).Commit'`), plus
  `walFold_snapFrom`, `snapFrom_mono`, `certBaseK_read`, `certBaseK_snoc`, `certBaseK_restart`.
* `InvWalCrashLaws.lean` (now imports `InvWalCrashPure`): `snapFrom_snapCert`, `walHistCertsK_snapCert`; the crash proof
  uses the latter (`n ≤ j`), no `Hhcj`. `walHistCerts_take`/`walHistCerts_snapCert` now unused (delete if still so).
* `InvWalCrashSteps.lean`: `walHistCertsK_snoc` (commit premise: save `rw [walLastHS_snoc_saveP, hlast]; exact Hcmono`,
  snapshots `walLastHS_snoc_snapP`), `walHistCertsK_mono` (enter's `max n (pos+1)`), `walHistCertsK_alloc`,
  `rnRestartWal_snapDurTriv`; fresh alloc and **`rnRestartAllocK_law_holds` without the `sorry`**.
* `bootstrappedRaft__newRaftNode.lean` (the law's one caller, `sd = fun _ => True`): `rnRestartWal_snapDurTriv` gives
  `walSnapDur` and is passed to `hRestartAlloc`.
* **Risk**: `MemberCrash.lean:415` (not ours to edit) destructs the crash post with a trailing `-` for the dropped
  conjunct (`… #Hl, -⟩`). If it no longer elaborates, either the owner drops the `-`, or put a placeholder conjunct back
  (ask the coordinator; do not edit MemberCrash here).
* **fk-lean1 at handoff**: seed copy `cp -a etcd-safe-f7-runauth/.lake etcd-safe-t10b/` still running (47 of 62 GB),
  with a watcher that, when it ends, deletes read-only `.ilean`s and `.lake/lean-check` in the destination. The remote
  worktree `~/eg/wt/etcd-safe-t10b` is still at `ada6d74e2c` (the head's Lean; head differs only in notes).
* **Next commands**: (1) once `pgrep -f "^cp -a etcd-safe-f7-runauth"` is empty: check `du -sh` of the destination
  (≈62 GB), delete `~/eg/wt/etcd-safe-f7-runauth` (merged, ours), `df -h ~`. (2) Head build BEFORE syncing (B): on
  fk-lean1 in the worktree, `flock ~/eg/build.lock systemd-run --user --scope -q -p MemoryMax=55G lake build
  --packages=.lake/package-overrides.json` (env as in `/shared/tmp/t10b-rb.sh`). (3) `/shared/tmp/t10b-rb.sh
  Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrashSteps Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
  Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberCrash`, fix; then full build and `GATES=1
  /shared/tmp/t10b-rb.sh`; `etc/tcb-report.py --check --update` (with `LAKE_OPTS`) should lose `rnRestartAllocK_law_holds`'s
  `sorry`; list it; update STATUS; push.

### T10 step 2 (`cPost` restatement), session 1 (2026-11-26, branch `etcd-safe-t10b/2026-11-26`)

**G1** (the lead's question: is T10's commit invariant generic in its payload, or a separate crash-mode backend
bundle?). Generic, one bundle. `kbStep.law`/`kbSync.law` (`dist/crash/BackendImage.lean`) are stated over an
abstract payload `KB : Data → Data → IProp GF` and the backend-supplied `CV`; T10's design ("T10 design", §1)
makes `KB` a parameter of the backend's names, as `W`/`Pk` are, with `cmtBody` gaining `dbCrashKeep ∗ KB` and
`cmtInvK` the crash token, and untracked backends (tests, `mvccfull`, defrag's temporary) taking `KB := True`
and the old body. No second backend bundle is planned: the record absorbs only the half of bbolt's `boltState`
that `cmtInv` already holds (`dbHalf γ.db Dc`, `InvBackend.lean:1763`); the batch lock's half (`ownDB`, what
the server's bundle reaches through `mvccBackend`/`bkWT`) is untouched. So the apply path's specs carry it at
the cost of the names gaining `KB`/`γk`: no `Spec/` file names `cmtInv` (8 `Proof/` files do, all inside the
backend), and the apply path's specs take the backend through `mvccBackend E.γ 1 B (E.Pk B)`, opaque in the
names. B4's `specGK`/`specCK` then need the server's backend opened with the server's payload (`bkPayload ∗
ciFloorAuth`), not a different bundle; the cost is where the server's `γ` is built (`OpenBackend.spec`'s post).

**Handoff T10s2-1** (session 1 stopped at the context rule; head = this commit, pushed). Plan: the draft
`/shared/tmp/coord-03/t10-step2-cpost-draft.md` §4 with the lead's conditions (#50, 15:27Z); ledger entry
"Applied, (2): `cPost` restated" (under 2026-11-26 "the skip paths' model fact").

*Done (stages 1-2), built on fk-lean1 (the seven modules, `lake build` targets, green):*
* ledger entry (conditions (a)-(c) recorded; `bootClusterRows.spec` "strengthens an unproved law", Go evidence);
* `apply/Contracts.lean`: `cPost b Pre Post φ`, `cPost_of_pre … φ h`, `cPost_mono`; `isCluster`/`isClusterRest`
  rows `cPost b Pre Post (restSetVersion b s r = r)`, `(restUpdateAttrs b ⟨id, attr.Name', cus⟩ r = r)`, `True`;
* `apply/Chain.lean`: `mPostV … Pre Post φ`; `kvPost`/`kvPostF … Pre Post (N := fun _ => True)` with `Pre` disjunct
  `Pre ∗ ⌜oc.logAfter log = log ∧ N oc⌝` (default stated in the docstring, condition (b)); `kvPostF_backend`
  (takes `N`); `cmpTriple`'s `Pre ∗ ⌜(if chainCompacts c then cmpRevAfter crev rev else crev) = crev⌝`;
  `applierSpec`'s cluster row `mPostV … (cr.eff v3 rs = rs)`;
* `apply/InvUber.lean`: `dispatchNoEff` (before `cmpAdmit`); `apply/GrantRest.lean`: `applyNoEff`,
  `applyNoEff_skipped`, `_rejected`, `_of_dispatch`;
* `apply/WriteLemmas.lean`: `mPostV_of … φ`; `apply/ApplyLemmas.lean`: `cPost_if … φ`;
* `auth/Steps.lean`: `adminOut_keep` (`err ≠ nil ∨ ∀ st o, R st o → o = .same` ⊢ `authOwn M hs` from `adminOut`),
  in place of the draft's `adminOut_errKeep` (it also covers `AuthEnable`/`AuthDisable`).

*Facts found* (in the ledger entry): `AuthEnable` has a pre-lock return with `err = nil` (`store.go:273-276`), so
its fact is `en = true`, not the draft's `err ≠ nil`; `AuthDisable` has one too (`store.go:308-310`), fact `en =
false` (condition (c): not `⌜False⌝`). For both, `(Post ∨ Pre)` must move inside `∃ en` (the `specT`'s
`∃ en, ⌜en = b0⌝ ∗ …`). `Authenticate` takes no batch lock at all and its post keeps `authOwn M hs` in both
disjuncts: leave its `(Post ∨ Pre)` unchanged (no fact needed). `UserChangePassword`, `UserGrantRole`,
`RoleRevokePermission` have no pre-lock return: `err ≠ nil` holds vacuously (their proofs never return `Pre`
with the lock taken: check, else the fact is the `.err` outcome's).

*Left, by stage (the tree above the defs does not build until stage 5 is done):*
3. **auth store**: `Spec/.../auth/authStore__{AuthEnable,AuthDisable,RoleAdd,RoleDelete,RoleGrantPermission,
   RoleRevokePermission,UserAdd (spec, specSure),UserChangePassword,UserDelete,UserGrantRole,UserRevokeRole}.lean`
   (`Post ∨ (Pre ∗ ⌜err ≠ GoInterface.nil⌝)`, enable/disable as above); `auth/LatestTie.lean`'s `specT` (303-441)
   and `specTB` (446-490) rows and the `spec_of_T`/`specT_of_TB` lemmas (522-730); the method proofs (the
   pre-lock sites end in `iapply csContract_noWrite $$ Hcs`: frame the pure fact there, e.g. `RoleAdd.lean:64`);
   `authStore__UserAdd_tieSure`, `InvAuth` (1 site); then `apply/AuthSteps.lean`/`AuthStepsX.lean` (`isAuthSteps`
   rows, 11 + 6, restated in place, condition "no parallel rows"), `AuthDerive`, `AuthApplyLatest`,
   `AuthApplyLatestRevoke`, `AuthLemmas`, `newAuthApplierV3`.
4. **applier methods and dispatch**: the backend proofs `applierV3backend__{Put,Txn,DeleteRange}` (`Pre` with the
   outcome's `logAfter = log`: `txn.Put`'s lease-not-found, `txn.Txn`'s read-only/`checkTxn` disjuncts),
   `__LeaseRevoke` (+ the three `LeaseRevoke` specs with explicit `N := fun o => revokeIds rq true o T = T ∧ ∀ t,
   revokeRest T rq true o (grantRest t rq true o rs) = rs`, from the lessor's `id ∉ L`), `__Compaction` (+ its
   spec; the `ErrCompacted` return, `rev ≤ crev`), `__Cluster{VersionSet,MemberAttrSet}`, `__DowngradeInfoSet`
   (`mPostV_of` with the row's fact), the `__Auth*`/`__Role*`/`__User*` applier methods (use `adminOut_keep`); the
   wrappers (`applierV3Corrupt__*`, `applierV3Capped__*`, `quotaApplierV3__*`, `authApplierV3__*`,
   `newApplierV3{Backend,Capped,Corrupt}`, `newQuotaApplierV3`: pass-through); `CompactArm`, `Results` (alarm chain);
   then `DispatchKVL`, `DispatchAdmin`, `uberApplier__dispatch` (+ its spec: `apply.cPost v3 Pre Post
   (apply.dispatchNoEff c rq v3 log crev T rs o)`).
5. **Apply levels and server**: `uberApplier__Apply` (+ spec: `apply.cPost v3 Pre Post (apply.applyNoEff rq v3 x
   x' T rs out)`), `ApplyRec`, `ApplyKVL`, `ApplyAdmin`, `ApplyAdminL` (mode `on`: `∧ st' = st`, `cPost` inside
   `∃ hs' st'`), `ApplyFnKVL`, `ApplyFnAdmin`, `ApplyFnAdminL`, `M2ApplyDraft` (if built); then
   `etcdserver/AdminEntryOn.lean`, `ModeSpecs.lean`, `EtcdServer__applyEntryNormal.lean` (the `(if v3 then
   iprop(Post ∨ Pre) else Pre)` wrappers become `cPost v3 Pre Post (…)`; destructure only). `ImgRow.lean`'s
   `srvImgModelOn` is step 3's.
   Then: full build, `etc/gates.sh` in full (base failures: `mode`, `featuregate`, `model-param`, `errdesc-check`),
   `etc/tcb-report.py --check` unchanged.

**Handoff T10s2-2** (session 2 stopped at the context rule; stage 3 = `3a851dec04`, pushed).

*Stage 3 done* (lean-checked on fk-lean1, `-a`, 0 errors each): the 11 `Spec/.../auth/authStore__*` admin specs
(`Post ∨ (Pre ∗ ⌜err ≠ GoInterface.nil⌝)`; `AuthEnable`/`AuthDisable`: `(Post ∨ (Pre ∗ ⌜en = true⌝))` /
`⌜en = false⌝` inside `∃ en`, docstrings say so); `LatestTie` specT/specTB rows and `spec_of_T`/`specT_of_TB`;
the method proofs (`InvAuth.csContract_noWriteF … (h : φ)` at the pre-lock sites, `(by nofun)` for `err ≠ nil`;
Enable/Disable's split moved after `iexists en`); `UserAdd_tieSure`; `isAuthSteps` (11 rows) and `isAuthStepsX`
(5 rows) restated in place; `AuthDerive`, `AuthApplyLatest{,Revoke,Put,Txn}`, `AuthLemmas`, `newAuthApplierV3` green.
`kvPostFL` (`AuthApplyLatest`) gained `N` (default `fun _ => True`) and `kvPostF`'s `Pre` disjunct.
**Open design point for stages 4-5**: the mode-`on` step specs (`AuthSteps`' `*.stepSpec`, `AuthStepsX`'
`stepSpecX`/`fuelSpecX`) still post `mPost` (`Post ∨ Pre`); their proofs drop the fact with
`apply.orPre_forget` (`Contracts.lean`, 16 sites, right after each `wp_apply HM`). For `ApplyAdmin(L)`'s
mode-`on` `st' = st`, these step specs must carry `Post ∨ (Pre ∗ ⌜φ⌝)` (φ the row's) up to `adminDone`, where
`auth.adminOut_keep` turns it into an unchanged authority; decide that form (a `φ` on the step specs' post, not
on `mPost`, which the axiom-side `authReqContract` path also uses) before stage 5.

*Stage 4*: a lean-check (`-a`) of every `applierV3backend__*`, `applierV3Corrupt__*`, `applierV3Capped__*`,
`quotaApplierV3__*`, `authApplierV3__*`, `newApplierV3*`, `newQuotaApplierV3`, `CompactArm` printed no file
with errors (its summary filter printed nothing at all: re-run it unfiltered before trusting that). None of
the stage-4 spec changes are made yet: `applierV3backend__Compaction` spec (`ErrCompacted`, `rev ≤ crev`), the
three `LeaseRevoke` specs' explicit `N`, `__Cluster{VersionSet,MemberAttrSet}`/`__DowngradeInfoSet` via
`mPostV_of` with the row's fact, `Results` (alarm chain), then `DispatchKVL`, `DispatchAdmin`,
`uberApplier__dispatch` (+ spec `apply.cPost v3 Pre Post (apply.dispatchNoEff c rq v3 log crev T rs o)`).
Note `kvPostFL` is used by `DispatchKVL` (lines 142-198) and `AuthApplyLatest{Put,Txn}`.

*Stage 5*: unchanged from T10s2-1's list, plus the step-spec point above. Then full build, gates in full,
`tcb --check`. `AuthSrv.lean` fails `setup-file` today (an import above the defs does not build yet).

**Handoff T10s2-3** (session 3 stopped at the context rule; head = this commit, pushed).

*The step-spec decision (coordinator, 2026-11-26), done*: the admin step specs carry the store's no-lock fact,
as the rows do. `apply/Chain.lean`: `mPostF E c a log Pre Post φ` (`kvOwn ∗ chainResAny ∗ (Post ∨ (Pre ∗ ⌜φ⌝))`)
and `mPostF_backend`, beside `mPost` (kept: `mPostW` in the `Spec/.../applierV3backend__*` files and the getters/
`Authenticate` use it; changing its arity would have touched those `Spec/` files, outside the plan's list).
`AuthSteps` (11 `stepSpec`s), `AuthFuel` (11 `fuelSpec`s), `AuthStepsX` (5 `stepSpecX`, 5 `fuelSpecX`; not
`Authenticate.specX`, which keeps the authority anyway): `mPostF … (err ≠ GoInterface.nil)`; `AuthEnable`/
`AuthDisable`: `∃ en, mPostF … (en = true)` / `(en = false) ∗ enabledVerdict ∗ adminOut…` (moved inside `∃ en`).
The 16 `orPre_forget` sites are gone and `orPre_forget` is deleted (`Contracts.lean`).
`AdminChain`: `AdminReq.result … err k` takes the no-lock fact `k` (`⌜k → err ≠ nil⌝`; `authEnable`: `⌜k → en =
true⌝` inside `∃ en`; `authenticate`: none); `adminTriples`' post is `applyTok ∗ applyErrIs err ∗ W ∗ ∃ k : Prop,
mPostF E c (.ok ai) log Pre Post k ∗ ar.result … err k`; the four layer wrappers and `applierAdmin_backendX` (explicit
continuations, `k := err ≠ nil` / `en = true`; `Authenticate`: `k := True`) follow. New `AdminReq.result_keep (hk :
k) : ar.result Own γa (.on γa) hs resp err k ⊢ Own γa hs` (what stage 5 uses for `st' = st`). Lean-checked
(`-a`, 0 errors): `AuthSteps`, `AuthStepsX`, `AuthFuel`, `AdminChain`.

*Stage 4, next*: `DispatchAdmin.lean` (spec line ~135 and `adminDone` line ~99; six `iunfold apply.mPost at Hpost`
sites, 537-880, become `mPostF` with `%k`): `adminDone Own γa M hs rq v3 ar k` (`ad.result … v.Err' k`), the
`adminSpec` post `∃ o (k : Prop), … cPost v3 Pre Post k ∗ … adminDone … k` (with `v3 = false`: `k := True`, the
authority as it was). Then the rest of stage 4 as in T10s2-2 (first re-run the method files' lean-check unfiltered),
`uberApplier__dispatch` (its `mPost` site, line 647), `newAuthApplierV3`/`newApplierV3{Capped,Corrupt}`/
`newQuotaApplierV3`/`authApplierV3__{UserGet,RoleGet}`/`quotaApplierV3__LeaseGrant` (they use `mPost`, unchanged:
check they still build). *Stage 5*: `ApplyAdmin`'s `adminOut … k`, `ApplyAdminL`'s `adminSpecL` (`∃ k`, `cPost v3
Pre Post k`), then `AdminEntryOn`: `cPost v3 Pre Post (st' = st)` inside `∃ hs' st'`, from `result_keep` in the
`Pre` branch (choose `hs' := hs`); the rest of T10s2-1's stage-5 list. Not yet run: full build, gates, `tcb --check`.

**Handoff T10s2-6** (session 6 stopped at the coordinator's context rule; head = this commit, pushed; no `sorry`, no
new axiom). **Full `lake build` on fk-lean1: EXIT 0** (flock, MemoryMax=55G).

*Done (green)*: `DispatchKVL` (range site: `Post ∨ (Pre ∗ ⌜oc.logAfter log = log ∧ True⌝)` by `chainStep_logAfter_of`,
which moved from `uberApplier__dispatch` to `DispatchLemmas`; revoke site: `revokeNoEff` at `restAfter_other`);
`quotaApplierV3__*`, `authApplierV3__*` (there is no `quotaApplierV3__LeaseRevoke` file); stage 5: `uberApplier__Apply`
(`cPost_mono` + `applyNoEff_of_dispatch` / `applyNoEff_rejected`), `ApplyKVL` (`applyNoEff`, grant identities by
`authKVKind`), `ApplyRec`/`ApplyFnKVL` (`cPost v3 Pre Post (applyNoEff …)` moved inside `∃ x' out`; skip: `applyNoEff_skipped`),
`ApplyAdmin`/`ApplyAdminL`/`ApplyFnAdmin`/`ApplyFnAdminL` (`adminOut … ar k out`, `∃ … (k : Prop)`, `cPost v3 Pre Post k`;
rejected/skipped `k := True`), `ApplyTieOn` (`adminOutX_on_noExtraE` also gives `err ≠ nil → outState st o = st`;
`adminOut_model` takes `k` and posts `k → st' = st`), `NoSpaceDeadAdminOn` (`k` threaded), `AdminEntryOn`
(`cPost v3 Pre Post (st' = st)` inside `∃ hs' st'`), `EtcdServer__applyEntryNormal` (the three `_win` wrappers restated;
call sites destructure the moved conjunct; local `cPost_true_orPre` forgets the fact where `tail_on` uses `Hout`: step 3
reads it there), etcdserver `Results` (`server_apply_admin_not_nospace_on` takes `k`).

*Not run*: `etc/gates.sh` in full (`GATES_FAILFAST=0`; base failures `mode`, `featuregate`, `model-param`,
`errdesc-check`), `etc/tcb-report.py --check` (expect unchanged). Then STATUS update.

**Handoff T10s2-5** (session 5 stopped at the context rule; head = this commit, pushed; WIP, no `sorry`, no axiom).
Last build: the stage-4 targets plus the `quotaApplierV3__*`/`authApplierV3__*`/`newAuth`/`newQuota` modules
(`/shared/tmp/t10b-s4targets.txt`, `/shared/tmp/t10b-g2.txt`) on fk-lean1, exit 1.

*Done (built green)*: `applierV3Corrupt__LeaseRevoke` (Pre site `⟨trivial, revokeIds_rejected, revokeRest_rejected⟩`),
`applierV3backend__Txn` (read-only site: `txnChs = []`), `newApplierV3Backend`, `newApplierV3Corrupt` (`simp
[chainCompacts]`), `AuthLemmas` (`auth_reject_kvPost`/`auth_pass_kvPost` take `N`, the reject one `hN`),
`authApplierV3__LeaseRevoke`, `AuthApplyLatest` (`auth_reject_kvPostFL` takes optional `N`, `hN := by trivial`),
`AuthApplyLatestRevoke` (`auth_pass_kvPostFL_nil` takes `N`), `uberApplier__dispatch` (`simp_all` gone: local
lemmas `restAfter_kind`, `chainStep_logAfter_of`, `dispatchNoEff_plain`, `dispatchNoEff_rest`; `noeff` = plain
kinds / rejected grant / compaction (`hcr`); cluster sites in `cpost_gen` through `dispatchNoEff_rest`; Range
site's fact by `chainStep_logAfter_of`; revoke site inlined), `CompactArm`, `newAuthApplierV3`,
`newQuotaApplierV3`. **`Chain.grantPost` changed** (needed by dispatch's grant site): its `mPostW … Pre Post`
is now `mPostW … iprop(Pre ∗ ⌜∃ e, o = .rejected e⌝) Post` (the Pre disjunct only at a rejection);
`applierV3{backend,Corrupt,Capped}__LeaseGrant`, `quotaApplierV3__LeaseGrant` adjusted, green.

*Failing (first error each)*:
- `DispatchKVL.lean:747`: `icases: cannot destruct Pre` (the grant row: the new `grantPost` Pre disjunct `Pre ∗
  ⌜∃ e, o = .rejected e⌝`; do as `uberApplier__dispatch`'s `noeff` grant alternative); `:954`: application type
  mismatch (not looked at; likely the same change).
- `uberApplier__Apply.lean:61`, `ApplyAdmin.lean:44` (also `:63`, `:122`): stage 5, not started.
- `Results.lean`: edited, not yet built: `chain_put`/`chain_deleteRange`/`chain_txn` now post `(Post ∨ (Pre ∗
  ⌜oc.logAfter log = log⌝))` (converted from the `kvPostF` fact's `.1`), `chain_revoke` `(Post ∨ (Pre ∗
  ⌜oc.logAfter log = log ∧ revokeNoEff rq T rs oc⌝))`. Check it once `DispatchKVL` builds.
- Not built (behind the failures): `quotaApplierV3__LeaseRevoke` and the rest of `Link`'s closure.

*Then*: stage 5 (`ApplyAdmin`/`ApplyAdminL`, `AdminEntryOn` with `result_keep`, `uberApplier__Apply`, the server),
full build, gates in full, `tcb --check`.

**Handoff T10s2-4** (session 4 stopped at the context rule; head = this commit, pushed; WIP: the files marked
failing do not build yet, no `sorry`, no axiom). Last build: the stage-4 targets (`/shared/tmp/t10b-s4targets.txt`,
`lake build` on fk-lean1).

*Done (built green)*: `DispatchAdmin` (`adminDone … k`, `adminSpec` post `∃ (o) (k : Prop), … cPost v3 Pre Post k`,
the six admin sites `%k` from `adminTriples`' `mPostF`; v3 = false: `k := True`); `Spec/.../uberApplier__dispatch`
(post `cPost v3 Pre Post (dispatchNoEff c rq v3 log crev T rs o)`); `Spec/.../applierV3backend__Compaction`
(`Post ∨ (Pre ∗ ⌜cmpRevAfter crev rev = crev⌝)`, cmpTriple's form) and its proof; `Chain.lean`: new
`revokeNoEff rq T rs o := revokeIds rq true o T = T ∧ revokeRest T rq true o rs = rs` (simpler than T10s2-1's
`∀ t, … grantRest …`: for a revoke `grantRest` is the identity), the applierSpec revoke row's `kvPost … (revokeNoEff
rq T rs)`; the three `Spec/.../{applierV3backend,applierV3Corrupt,authApplierV3}__LeaseRevoke` with that `N`;
`applierV3backend__LeaseRevoke` (local `kvPost_backend` takes `N`); `Spec/.../applierV3backend__{ClusterVersionSet,
ClusterMemberAttrSet,DowngradeInfoSet}` (`mPostV … (restSetVersion v3 v rs = rs)` / `(restUpdateAttrs v3 mm rs = rs)`
/ `True`) and their proofs (unchanged); `applierV3backend__Put`, `applierV3Capped__{Put,Txn}`,
`applierV3Corrupt__{Put,Txn,DeleteRange}` (the `Pre` sites `iright; iframe HPre; ipureintro; (first | exact ⟨rfl,
trivial⟩ | …)`); `DispatchKVL` (`kvSpecL` post `cPost v3 Pre Post (o.logAfter log = log ∧ revokeIds rq v3 o T = T ∧
revokeRest T rq v3 o (restAfter rq v3 rs) = rs)`; applierKVL's revoke row `… (revokeNoEff rq T rs)`; `fin_kvL` and the
revoke site derive it with `revokeIds/Rest_nonRevoke`, `restAfter_other`); `Spec/.../uberApplier__Apply` restated
(`cPost v3 Pre Post (applyNoEff rq v3 x x' T rs out)`, stage 5's spec).

*Failing (first error each)*:
- `applierV3Corrupt__LeaseRevoke.lean:47`: unsolved goals (the Pre site's pure fact: now `revokeNoEff` of the
  rejected outcome: `revokeIds_rejected`, `revokeRest_rejected`; the `first | … | simp_all […]` did not close it).
- `applierV3backend__Txn.lean:218`: unsolved goals (second `Pre` site, the read-only path: `logAfter = log` of its
  outcome; `:179` site passes).
- `newApplierV3Backend.lean:304`: unsolved goals (its revoke row now needs `revokeNoEff`; not yet looked at).
- `newApplierV3Corrupt.lean:299`: unsolved goals (the `mPreRest_reject` site: rejected outcome's fact, as Corrupt
  LeaseRevoke).
- `authApplierV3__LeaseRevoke.lean:61`, `:105`: `iapply` cannot apply `kvPost …` (the inner/outer `kvPost` now with
  `N := revokeNoEff rq T rs`: pass `N` explicitly / the auth rejection's `Pre` site gets the rejected fact).
- `AuthApplyLatestRevoke.lean:151`: `iapply` cannot apply `kvPostFL …` (same: its spec now ends `(apply.revokeNoEff rq
  T rs)`).
- `uberApplier__dispatch.lean`: the new local macros `noeff` (`simp_all [dispatchNoEff, dispatchCrev, revokeIds,
  grantIds, revokeRest, grantRest, restAfter, ClusterReq.eff, Outcome.logAfter, revokeNoEff]`), `cpost_fin`,
  `cpost_gen φ` (header, ~line 125-160): `noeff`'s `simp_all` fails ("Tactic `simp` failed with a nested error") at
  357, 389, 419, 512, 533, 561, 582, 619, 786, 877; 698: `icases: cannot destruct Pre` (the grant site's `HPP` is not
  `Post ∨ (Pre ∗ ⌜_⌝)`: check the grant row's post). Replace `noeff`'s `simp_all` by a targeted proof: `dispatchNoEff`
  is `⟨logAfter, dispatchCrev_nonCmp, grantIds_nonGrant + revokeIds_nonRevoke, fun t => grantRest_nonGrant +
  revokeRest_nonRevoke + restAfter_other⟩` for most kinds (as `grant_same` does), the method's fact for
  compaction/revoke/grant/cluster.
- `uberApplier__Apply.lean:61` (stage 5), `ApplyAdmin.lean:44` (stage 5): not started.
- Not reached (downstream of the failures): `Results` (alarm chain, its revoke post `(Post ∨ Pre)` at line 436 will
  need `(Pre ∗ ⌜… revokeNoEff …⌝)`), `newAuthApplierV3`, `newQuotaApplierV3`, `CompactArm`, `quotaApplierV3__*`,
  `authApplierV3__*` other than LeaseRevoke.

*Then*: steps 3-5 of the plan (`ApplyAdmin`/`ApplyAdminL`, `AdminEntryOn` with `result_keep`, the rest of stage 5),
full build, gates in full, `tcb --check`.

### T10 step 3, session 1 (2026-11-26, branch `etcd-safe-t10s3/2026-11-26`; design)

Base `etcd-safe-t10b/2026-11-26` @ `9f2a8ff9ea` (step 2 done). Build: fk-lean2, `~/eg/wt/etcd-safe-p5`
(repurposed, Perennial overrides at `a706aeb9a`), sync and build with `/shared/tmp/t10s3-rb.sh [targets]`
(`CHECK=1`: `etc/lean-check.py`; `GATES=1`: gates; logs `~/eg/logs/t10s3-{build,gates}.log` there).

**What step 3 is.** Two parts, of very different size. (A) The server's row: `consInv γ` at the server's
`srvImgRow` (session 9's plan, item 3): `isServer`/`isServerM` pass it, the call sites switch to the `R`
lemmas, the skip sites read step 2's fact. (B) Closing `NewServer.wp_proofC`'s `sorry`: the restart proof
(`wp_proofRG`) over the non-graceful images (`σ.commit < i`, `i < σ.b` with the `.snap.db`, `i < bootLen`,
`confRowW`'s second case). (A) does not give (B): (B) is T4's open list ("Not done (next, in order)" items
2-4 of the option-(a) entry, and round 4's steps: the replay state over the durable state and its deposits,
`applyAll`'s keep case, `rnRestartOk` without `|a0| ≤ commit0`, `rnStopImage`/`wal.stopImage` without the commit
bound), plus T10's three image cases. Order: (A) first (each group builds green), then (B) by T4's list.

**The row the server uses.** Mode off: `srvImgRow γr.raft (srvImgModel γr)` (`ImgRow.lean`). Mode `on`: the
same row over `srvImgModelOn` (to define beside it: the models at `kvModelOn`), passed where the mode is known
(`isServerM`, `AppliedOn`, `AuthCompRows`), not in `isServerCI` alone. As a bundle: `srvImgRowT γ M : TRow GF`.

**Bundle: yes** (session 10's alternative). `structure TRow GF where IR; tl : ∀ a b, Timeless (IR a b)`
(`InvApply.lean`), `consInv γ (Rw : TRow GF := TRow.triv)`, the generic sections over `{Rw : TRow GF}` with
the global instance `TRow.timeless`: no instance argument, so `Rw` unifies from `inv applyN (consInv γ Rw)`.
Named `Rw`, not `R`: nine of the files already bind an `R`. Mechanical, untrusted, no statement of a
`Spec/` file. The 22 `(IR := fun _ _ => True)` sites become `(Rw := TRow.triv)`; they can drop the
argument where it then unifies. Written, not checked: `/shared/tmp/t10s3-trow.patch` (handoff below).

**A finding for (A): the row at the restart's allocation.** `consInv_allocR` takes `□ IR 0 m0.1` (the state
`⟨k = 0, p = m0.1, eff = 0⟩`). At the server's row that says the models are constant over `[0, m0.1]`: true at
the first boot (`m0.1 = ai0`, `srvImgRow_nil`), false at a restart with a non-empty applied prefix. What the
protocol needs at `k = 0` is only the row at the stored index (`commit_save_auR`'s `k = 0` case reads it at
`mm.1`; Go's `UnsafeSave` stores nothing new while `ci = 0`). Fix (choose when doing the allocation's callers):
allocate at `eff = m0.1` (`⟨0, m0.1, m0.1, false⟩`; `commitOk` then pins the stored index, as Go does), which
changes the boot packets' `applyThread γ ⟨0, m0.1, 0, false⟩`; or read the row at `(if k = 0 then p else eff, p)`.

**Order of files (A).** 1. `InvApply` (`TRow`) and the 21 users (the patch). 2. `ImgRow`: `srvImgRowT`,
`srvImgModelOn`. 3. `InvApplier`/`AppliedOn`/`AuthCompRows` (`isServer`, `isServerM`) at the row; the call
sites: `writes_done` → `writes_doneR` (`srvImgRow_at` at `A ++ ms.take (j+1)` in `EtcdServer__apply`, `A ++ [m]`
in `applyEntryNormal`), `skip_done` → `skip_doneR` (`srvImgRow_skip`; the fact from `cPost`'s `Pre` disjunct:
replace `applyEntryNormal`'s local `cPost_true_orPre` in `tail_on` by a use of the fact; `applyConfChange`'s wand's
`ccValidOn = false`), `ci_swap_au` → `ci_swap_auR` (`SnapApplyOpen`), `consInv_alloc` → `consInv_allocR`
(`bootstrapBackend`), the boot packets carry the row. 4. Then (B).

**Handoff T10s3-1** (session 1 stopped at the coordinator's context rule; notes only, no Lean changed on the
branch; no `sorry`, no axiom).
* *Host*: fk-lean2 (`ssh -i /shared/aws ubuntu@ec2-54-152-19-40.compute-1.amazonaws.com`), tree
  `~/eg/wt/etcd-safe-p5` (a worktree of `~/eg/etcd-grove.git`, now detached at `9f2a8ff9ea`; the branch is also
  pushed to that bare repo), `.lake/package-overrides.json` pointing at `~/eg/perennial-a706aeb9a` (the t10b pin,
  `lake-manifest.json`'s rev). Disk after the build: 63G free.
* *Script*: `/shared/tmp/t10s3-rb.sh [targets]` syncs this worktree's changes against `9f2a8ff9ea` (tar over ssh)
  and runs `lake build` there under `flock ~/eg/build.lock` and `MemoryMax=55G`, `LEAN_NUM_THREADS=10`
  (`CHECK=1`: `etc/lean-check.py` on the args; `GATES=1`: `etc/gates.sh`; log `~/eg/logs/t10s3-build.log`). When the
  base moves, change its `BASE=`.
* *Build state*: `NewServerCrash` and the server's `Link` at `9f2a8ff9ea` built green on that tree (10083 jobs,
  EXIT 0), so the next checks are incremental.
* *Next*: apply `/shared/tmp/t10s3-trow.patch` (`git apply`; the `TRow` bundle in `InvApply.lean`, `Rw` in its 21
  users, written by perl/python edits and **not yet checked**), then `CHECK=1 t10s3-rb.sh` on `InvApply.lean`,
  `InvServer.lean`, then build the 22 files' modules plus the server's `Link`; then the design's order, item 2.

**T10 step 3, session 2 (2026-11-26): steps 1-2 done, step 3 stopped (a `Spec/` change).**
* *Step 1, `TRow`*: the patch applied with two fixes in `InvApply.lean`: `TRow.triv` is an `abbrev`
  (as a `def`, `TRow.triv.IR a b` did not reduce to `True` for `IntoWand` at the trivial corollaries
  `writes_done`, `skip_done`, `ci_swap_au`, `consInv_alloc`), and `consInv_timeless` keeps its
  `Timeless (□ Rw.IR a b)` helper. The 22 files plus the server's `Link` and `NewServerCrash` built green
  on fk-lean2 (10094 jobs). Commit `ca9fbbfa4d`.
* *Step 2*: `srvImgRowT γ M : TRow GF` (and `srvImgRowT_IR`) in `ImgRow.lean`, which now imports `InvApply`;
  `srvImgModelOn γr A` (the mode-`on` KV model, `crevOf`, `kvLeasesOn` and `restModel` at `pre ++ A`, and
  the auth state after `A`, what `dbImageOn` is of) and `srvImgRowM on γr` (the row by mode) in
  `KVModelM.lean`, **not** `ImgRow`: `kvModelOn`'s module `KVAuthModel` imports `InvApplier`, which
  `isServer`'s row needs `ImgRow` under (an import cycle otherwise). Lean-checked; commit `19b44496c8`.
* *Step 3, STOP: the row cannot be allocated without a `Spec/` change.* `consInv` is allocated in
  `bootstrapBackend` (`consInv_alloc`, `bootstrapBackend.lean:214`), and `bootstrapBackend.spec`
  (`Spec/.../etcdserver/bootstrapBackend.lean:68`) returns `bootBackendRows cfg bk γA cil d` at the default
  `Rw := TRow.triv`, as `bootstrap.spec` returns `bootOk … b` at it. The invariant's row is fixed when it
  is allocated, and the server's row `srvImgRowT γr.raft M` names the `ServerRaftNames` (`pre`, `ai0`, the
  log's names), which do not exist at `bootstrapBackend` (it takes no names; `bootstrap.spec` takes only
  `γ : SrvRaft`). So `isServer`/`isServerM` cannot hold `consInv γ (srvImgRowT …)` until the boot specs
  carry a row. Ways on, for the lead: (i) `bootstrapBackend.spec`/`bootstrap.spec` take a row `Rw` with a
  premise `□ Rw.IR 0 0` (and the restart's specs the row at `(0, m0.1)`), the raft names allocated before
  `bootstrap` in `NewServer`'s proof; or (ii) the row over a ghost name allocated at `bootstrapBackend`
  and bound to the raft names later (`IR e p := ⌜(e, p) = (0, 0)⌝ ∨ ∃ γr, bound γb γr ∗ srvImgRow γr …`),
  the name in `bootBackendRows`'s post; both change a `Spec/` statement.
* *`consInv_allocR`'s restart problem*: not chosen (its callers are behind the same stop). For the record,
  the fix with fewer statement changes is reading the row at `(if k = 0 then p else eff, p)` inside
  `consInv` (`InvApply` only: `consInv`, `consInv_open`/`_close`, `skip_doneR`, `commit_save_auR`), where
  allocating at `eff = m0.1` changes `applyThread γ ⟨0, m0.1, 0, false⟩` in the boot packets
  (`bootBackendRows`, `bootOk`, `InvRestart`) and so `bootstrapBackend.spec`'s meaning.

**Handoff T10s3-2.** Branch `etcd-safe-t10s3/2026-11-26` @ `19b44496c8` (pushed). Done: steps 1, 2.
Left: step 3 (`isServer`/`isServerM` at the row) and step 4 (the call sites, `cPost_true_orPre`'s
replacement), waiting on the lead's choice of (i)/(ii) above; then (B). The script's `BASE=9f2a8ff9ea`
still holds (the remote tree is that commit plus this branch's files).
No axiom, `sorry`, `Spec/` or trusted text changed.

### T10 status and handoff, session 10 (2026-11-26, branch `etcd-safe-t10`)

**The ledger entry "the skip paths' model fact" is decided** (coordinator: take the proposed change; recorded under its
"Decision", with an "Applied" line).

**Step 1 (row-agnostic users generic over the row): build 3 green** (exit 0, 11040 jobs, `/shared/tmp/t10-s10-build3.log`; `etc/tier-check.py --check` ok; targets
`/shared/tmp/t10s10-targets2.txt`: the 100 modules naming a changed name, `etc/importers.py --uses`). `isServerCI s γ ci
(IR := trivial)`; section `variable {IR} [hIR : ∀ a b, Timeless (IR a b)]` in `InvServer` (`ci_get_au`, `wp_ci_*`),
`CindexBackend` (hook section), `BuildLemmas`, `SnapSendBranch` (`commitReq_freeze`), `SnapApplyOpen` (`snap_create`;
new `wp_ci_swapR` taking `□ IR s'.eff s'.p`, `wp_ci_swap` its trivial-row corollary), `Results` (backend section);
`InvApply.commit_save_au` generic (it only forgets the row); the boot packets `bootBackendRows`, `bootOk`, `bootOkR`
take `(IR := trivial)` last. **Caveat found**: the instance argument `hIR` cannot be synthesized while `IR` is an
unassigned metavariable, and `iapply`/`wp_apply(_core)` with goal specs (`$$ [..] [..]`) turn it into a first goal
(`istart: ∀ a b, Timeless (?m a b) is not an emp valid`). So the call sites name the row: `(IR := IR)` in the generic
sections, `(IR := fun _ _ => iprop(True))` at the 22 trivial callers (`wp_ci_get`, `wp_ci_advance`, `wp_ci_unsafeGet`,
`wp_ci_hookSet`, `snap_create`, `hooksOk_server_fut`, `commitReq_freeze`). Step 3 changes those to the server's row.
*Alternative to weigh before step 3* (avoids naming the row at every call): bundle the row with its timelessness,
`structure TRow GF where IR : w64 → w64 → IProp GF; tl : ∀ a b, Timeless (IR a b)`, `consInv γ (R : TRow GF :=
TRow.triv)`, lemmas over `{R}`: then `R` unifies from `inv applyN (consInv γ R)` and no instance goal is left (a
mechanical change of `InvApply`, `IR` to `R.IR`).

**Step 2 (the no-lock outcomes' model fact): started.**
- `applyConfChange` (done, build 3 green): its no-lock path is the failed validation, and the skip happens inside the
  caller's wand `Pre -∗ WP SetConsistentIndex {Adv}` (where `EtcdServer.apply` runs `skip_done`, before `Adv`
  exists), so the wand takes `⌜membership.ccValidOn rs.bk m = false⌝` (spec and proof; the caller's two wands
  `iintro … %_Hcv`). From it `ccRest true m rs = rs` (as `fail_tail`'s `hcr`), so the entry's `restModel` step is
  the identity; the conf-change entry has no KV effect (`EtcdServer__apply.lean` line 76).
- The applier (`apply.Apply.specRec`, ~40 files): its no-lock outcome is `cPost`'s `Pre` disjunct
  (`apply/Contracts.lean:102`, `if v3 then Post ∨ Pre else Pre`), produced in `uberApplier__Apply` (`.rejected`,
  `.skipped`), `uberApplier__dispatch`, `Dispatch{KVL,Admin}`, `ApplyFn*`, `Apply{KVL,Admin,AdminL}`, the lease
  methods (`LeaseGrant`/`Revoke`/`Checkpoint`, `Compaction`) and the auth store's (`authReqContract`, `Post ∨ Pre`),
  and below them in lease/mvcc (`csContractA`, `lease/MvccShapes.lean:89`). Design: the `Pre` disjunct gains a pure
  "no effect" fact on the step, `o.logAfter log = log` and `dispatchCrev … = crev` (KV, `applyStep`'s
  `.dispatched` case; `.skipped`/`.rejected` already have `x' = x`), the lease table and rest state unchanged
  (`revokeIds…/grantIds…`, `revokeRest/grantRest/restAfter`); the server then gets `srvImgModel (A ++ [m]) =
  srvImgModel A` from its existing ties (`kvModel_snoc_*`, `hmod`, `restModel_append`). Note `restAfter` does not
  depend on the outcome (`ClusterVersionSet`/`MemberAttrSet` change `RestM` whenever dispatched): those paths must
  take the lock, or they are a finding. **Audit of every `Pre` path** (a read-only subagent, 2026-11-26): **no finding**, no v3 path
  returns `Pre` with a model changed. The paths: `.skipped` (no waiter, `noSideEffect`) and `.rejected` (admin check;
  auth/corrupt/no-space) have `x' = x` and the `*A` functions the identity; `DowngradeVersionTest` (pre-v3 kind,
  `restAfter_other`); Range and read-only txn (`commitLog log [] = log` by `backendStep`'s `txnReadonly` conjunct,
  `applierV3backend__Txn.lean:234`); put with its lease missing and `checkTxn` errors (`.rejected .backend`,
  `applierV3backend__Put.lean:186`, `Txn.lean:179`); `LeaseGrant` errors (`.rejected`, `LeaseGrant.lean:70`);
  `LeaseRevoke` of a lease not live (`LeaseRevoke.lean:219`: `revokeLog` the identity by the lessor contract's `Hnd`,
  the table filter by `Hnf`); `Compaction`'s `ErrCompacted` (`Compaction.lean:207`: `cmpRevAfter crev rev = crev`
  from `rev ≤ crev` in `cmpAnswerIs`); the auth store's early returns and checkpoint/alarm paths are not admitted by
  `rqOk`. Where the fact lives: only the read-only-txn one is inside `applyStep`; `Hnd`, `Hnf` and `rev ≤ crev` stay in
  component posts or are consumed inside the proofs, so step 2 exports them up to `cPost`'s `Pre`. **Spec looseness
  (not a Go bug, to tighten with it)**: the cluster contract `isCluster`/`isClusterRest` (`apply/Contracts.lean:593-614`,
  `clusterApplyRest`, unproved rows of `bootClusterRows.spec`) gives `cPost b Pre Post ∗ RO (restSetVersion b s r)`,
  allowing `Pre` with `RO` changed at `b = true`; Go always writes under the lock there (`cluster.go:473,613`), so the
  rows should tie `Pre` to `b = false`. Also: `lessor.Revoke` with `le.rd == nil` returns without the lock and the
  lease live (`lessor.go:339`); the contract's `rdHeld` premise excludes it and the server sets `rd`.
- Mode `on`: not started (the row's `M` at `kvModelOn`, passed where the mode is known: `isServerM`).

**Step 3**: not started.

No axiom, `sorry`, trusted text, top-level premise or top-level statement changed.

### T10 status and handoff, session 9 (2026-11-26, branch `etcd-safe-t10`)

**Build 4 (session 8's)**: green, exit 0 (`/shared/tmp/t10-s8-build4.log`: the 23 users of the protocol and
`etcdserver.Results`, 9976 jobs).

**Item 1 (a), the server's row: defined, not instantiated.** `etcdserver/ImgRow.lean` (defs tier, imports `InvRest`):
`srvImgModel γr A` (the mode-off image's models: `kvModel`, `crevOf`, `kvLeases (pre ++ A)`, `restModel c0 boot (pre ++
A)`, what `bkImg`/`imageRestAt` are of), `srvImgRow γ M e p := ∃ A, srvRLogLb γ A ∗ ⌜p = ai0 + |A| ∧ ∀ m ∈ [e, p],
M (A.take (m - ai0)) = M A⌝` (timeless, persistent), and the step lemmas: `srvImgRow_at` (from `srvRLogLb A` with
`k = ai0 + |A|`, the row at `(k, k)`: `writes_doneR` and `ci_swap_auR` need nothing else, the row at one index has no
model clause to prove), `srvImgRow_nil` (`p = ai0`, from `srvRLogLb []`: `consInv_allocR` at the boot, where
`m0.1 = ai0`), `srvImgRow_skip` (from `srvRLogLb (A ++ [x])`, `i = p + 1 = ai0 + |A| + 1` and `M (A ++ [x]) = M A`;
the row's prefix is `A` by `srvRLogLb_prefix` and the length). Built green on fk-lean1 (`/shared/tmp/t10-s9-build1.log`).
Checked with `/shared/tmp/t10s9-chk.sh FILE…` (copies the files to fk-lean1's worktree and runs `etc/lean-check.py`
there; the remote worktree then differs from the branch until the next `fklean1-check.sh` resets it).

**What blocks the switch (ledger 2026-11-26, "the skip paths' model fact"; decide first).** `skip_doneR` at the
server's row needs `M (A ++ [m]) = M A`. The no-data entry has it; the applier's and `applyConfChange`'s outcomes
without the batch lock (`applyEntryNormal` ~1002, ~1277; `EtcdServer.apply` ~788, ~1874) do not carry it. And the
mode `on` (`wp_proofOn`) needs the row over the mode's model (`kvModelOn`), so `M` is mode-dependent: pass the row
where the mode is known (`isServerM on`/`srvFieldsAtM on`, `AppliedOn.lean`, `AuthCompRows.lean`), not in
`isServerCI` alone.

**Plan for the instantiation (next session)**, so that each step builds green:
1. Generalize the row-agnostic users over `IR` (section `variable {IR} [∀ a b, Timeless (IR a b)]`, as `InvApply`):
   `isServerCI s γ ci` gains `(IR := fun _ _ => True)` (`InvServer`; `ci_get_au`, `wp_ci_*` take `consInv γ IR`),
   `CindexBackend` (566-843), `BuildLemmas` (103, 140), `SnapSendBranch` 121, `SnapApplyOpen` 70/183, `Results`
   1102-1156, the boot packets' `"#Hcons"` (`BootParts` 433, `InvBoot` 416, `InvRestart` 595). No caller changes.
2. Settle the ledger entry (the no-lock outcomes' model fact; `srvImgModelOn` for the mode `on`).
3. `isServer`/`isServerM` (`InvApplier` 749, `AppliedOn` 265, `AuthCompRows` 110) pass `srvImgRow γr.raft (M on γr)`;
   the 12 call sites switch: `writes_done` → `writes_doneR` with `srvImgRow_at` (the entry's committed prefix:
   `A ++ ms.take (j+1)` in `apply`, `A ++ [m]` in `applyEntryNormal`), `skip_done` → `skip_doneR` with
   `srvImgRow_skip`, `ci_swap_au` → `ci_swap_auR` (`SnapApplyOpen` 193) with `srvImgRow_at` at the snapshot's prefix,
   `consInv_alloc` → `consInv_allocR` (`bootstrapBackend` 214) with `srvImgRow_nil`; the boot packets carry the row.
4. Item 1 (c), the retired case of `commit_save_auR`, and (d) as in session 8's list.

Item 2 (P5's certificate route): not started, as session 8 says.

No axiom, `sorry`, trusted text, top-level premise or top-level statement changed.

### T10 status and handoff, session 8 (2026-11-26, branch `etcd-safe-t10`)

**Item 1, the `consInv` image row: first step done** (`InvApply.lean` only; ledger 2026-11-25 "the backend's image row
lives in the apply protocol's `consInv`", now partly applied). The protocol is generic over the row:
`consInv γ (IR : w64 → w64 → IProp GF := fun _ _ => True)` holds `□ IR s.eff s.p` beside `consRest` (timeless rows:
`consInv_timeless` takes `∀ a b, Timeless (IR a b)`). `consInv_open` returns the row, `consInv_close` takes it at `s'`'s
`(eff, p)` (explicit `e p` and `s'.eff = e ∧ s'.p = p`). New: `writes_doneR` (takes `□ IR k k`), `skip_doneR` (takes
`□ IR eff p -∗ □ IR eff i`), `ci_swap_auR` (takes `□ IR s'.eff s'.p`), `consInv_allocR` (takes `□ IR 0 m0.1`),
**`commit_save_auR`**: the commit's `Ψ` gets `□ IR s.eff s.p ∨ ⌜s.k = 0 ∧ s.eff = s.p⌝` with `commitOk s m` (the
right disjunct is the retired-backend case, where `s` is made of the stored index). This is what `kbStep.law`'s
commit point consumes: inside `Tx.Commit`'s update the backend's `UnsafeSave` runs `commit_save_auR`, so the row at
the stored index `m ∈ [eff, p]` is in hand at `_take`/`_putStep`. The old names (`writes_done`, `skip_done`,
`ci_swap_au`, `consInv_alloc`, `commit_save_au`) are corollaries at the trivial row, so no caller changed. `InvApply`
built green on fk-lean1 (build 3, `/shared/tmp/t10-s8-build3.log`). **Build 4 green** (the 23 modules naming the protocol plus `etcdserver.Results`, exit 0, log `/shared/tmp/t10-s8-build4.log`, list `/shared/tmp/t10s8/b1.txt`). `etc/tier-check.py --check` ok.

**Item 1, left** (in order): (a) the server's row `srvImgRow ρ γ e p := ∃ A, srvRLogLb A ∗ ⌜uint.Z p = ai0 + |A| ∧ ∀ m,
e ≤ m ≤ p → the KV model and restModel of A's prefix at m are A's⌝` (a defs module beside `InvServer`, timeless),
and `inv applyN (consInv γ.ap)` → `consInv γ.ap (srvImgRow …)` in the server (`InvServer`, `CindexBackend`,
`SnapApplyOpen`, `bootstrapBackend`, `EtcdServer__apply`, `applyEntryNormal`: the 23 modules of the list); (b) their
callers switch to the `R` lemmas: `writes_doneR` from the apply thread's `kvApplied` (the new prefix), `skip_doneR`
from the no-write paths (an entry that writes nothing keeps the models), `ci_swap_auR` from the snapshot's image,
`consInv_allocR` at the boot; (c) the retired case of `commit_save_auR`: the retired backend's KB must not need an
image (its file lost the name `db` at the install), or a persistent retired fact replaces the pure disjunct; (d) the
backend's crash-aware `cmtInv` with `KB` and `kbStep.law`'s proof at the commit point from (a)'s row plus mvcc's
`mvccImage_commit.law` (proposed; design §1).

**Item 2, P5's certificate route: not started** (budget). Lead's conditions (#50 2026-11-25T16:06:56Z): `walFilesC`
(`storage/WalRecsCrash.lean:67`, `@[no_expose]`, 7 users) names `Hs = walSrvHist d.H` in place; the crash image's
`srvFilesC` row (`InvRestart.lean:128`, `InvCrashImage.lean`) holds `walHistCerts γ.cl sd Hs` (`InvWalCrash.lean:178`);
`bootstrapCrashContract.law` (`etcdserver/CrashInterim.lean:137`) returns exactly the pre's certificates as a visible
frame (no fresh claim); `bootstrapRestartContract` and the graceful slot stay certificate-free. **What P5 must
provide:** `rnDurK_crash.law` (`InvWalCrash.lean`, P5's) extended to return `walHistCerts γ.cl sd Hs` for the
crashed WAL's history `Hs` (with `sd` the snapshot directory's durable indices, as `WalNamesK.sd`); until then T7's
`memberGen_crash_law_holds` takes it as a hypothesis.

No axiom, `sorry`, trusted text, top-level premise or top-level statement changed.
