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

**Port to the verified bbolt: yes, needed, not done.** The proof verifies `upamanyus/bbolt` @
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
