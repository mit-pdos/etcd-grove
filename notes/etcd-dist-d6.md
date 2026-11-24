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
* **Q2**: `W1` becomes a premise of every member machine's crash (finding 4); it is pending review.
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
