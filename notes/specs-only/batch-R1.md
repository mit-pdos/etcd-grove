# Batch R1: raft's node API (report)

Author agent, 2026-11-09. Everything builds: `etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3`
(66 modules); snippets: `cd examples && go vet ./specreq/raftnode/` clean, gofmt clean.

## Files

- `Spec/go_etcd_io/raft/v3/Model.lean`: the protocol-level pure model, transparent (the
  enumerations; `LogEntry`, `opsOf`, `termAt`; `HardState`, `ConfState`, `Membership`, `Snapshot`;
  `ConfChangeV1/V2/I`, `ConfDecision`; `Msg`; `StorState` with `MemoryStorage`'s operations;
  `Durable`, `StorageHolds`; `Batch`, `Durable.next`, `Driver`, `BatchOk`, `ConfView`, `BootLog`).
  Two opaque pure functions owned by other batches: `Membership.applyChange`/`Membership.Valid`
  (R4) and `decodeConfChange` (3h).
- `Spec/go_etcd_io/raft/v3/Api.lean`: the resources (opaque) and laws (`.spec` obligations), with
  the header saying what each means and how raft's proof would realize it.
- 64 spec files: `StartNode`, `RestartNode`, `setupNode`, `newNode`, `confChangeToMsg`,
  `node__{Stop,Tick,Campaign,ForgetLeader,Propose,ProposeConfChange,Step,Ready,Advance,
  ApplyConfChange,Status,ReportUnreachable,ReportSnapshot,TransferLeadership,ReadIndex,
  stepWithWaitOption,step,stepWait,run}`, `NewRawNode`, `RawNode__{Bootstrap,Tick,
  ReportUnreachable,ReportSnapshot,TransferLeader,Campaign,ForgetLeader,Propose,ProposeConfChange,
  ApplyConfChange,Step,ReadIndex,Ready,HasReady,Advance,BasicStatus,Status}`, `MustSync`,
  `IsEmptyHardState`, `isHardStateEqual`, `IsEmptySnap`, `IsLocalMsg`, `IsResponseMsg`,
  `IsLocalMsgTarget`, `SoftState__equal`, `needStorageApplyMsg`, `needStorageApplyRespMsg`,
  `NewMemoryStorage`, `MemoryStorage__{InitialState,SetHardState,Append,ApplySnapshot,
  CreateSnapshot,Compact,Entries,Term,LastIndex,FirstIndex,Snapshot}`.
- Snippets `examples/specreq/raftnode/`: `propose.go` (errors; retry with persistent credits),
  `readindex.go` (linearizable read), `readyloop.go` (etcd's Ready loop: leader send-before-write,
  snapshot install, storage writes, contiguous committed entries, conf changes before `Advance`;
  `MustSync`; disruptions), `confchange.go` (v1, v2 joint, apply or refuse two ways),
  `storage.go` (bootstrap from a WAL image; snapshot and compaction), `restart.go` (fresh start,
  durable restart, joiner, stop/restart), `transport.go` (rafthttp delivery and reports, etcd's
  merged `MsgSnap`).
- Requirement notes: `notes/specs-only/req/go_etcd_io_raft_v3.md` (R2, R3),
  `go_etcd_io_raft_v3_raftpb.md` (3h), `go_etcd_io_raft_v3_confchange.md` (R4).

## Exported vocabulary (namespace `Perennial.EtcdGrove.Raft`)

Ghost names: `Cluster` (opaque), `Cluster.ns` (raft's invariants' namespace, the client's choice),
`Cluster.dup` (persistent or one-shot proposal credits, the client's choice).

Cluster-wide:
- `committedLb γ l` (pers): the committed log extends `l`. Laws: nil, mono, agree.
- `committedOps γ ops` (excl, client-owned): the committed operations; moved only by proposal
  updates. Laws: `committedOps_lb`, `committedOps_get_lb`; `committedLb_confDecodes`.
- `confAt γ k m` (pers): configuration after `k` entries. `confDecisions γ D` (excl, client),
  `confDecided γ k d` (pers). Laws: `confAt_agree`, `confAt_normal`, `confAt_decided`,
  `confAt_skipped`, `confDecide`, `confDecided_agree`, `confDecisions_lookup`; `confSkipped` (a
  transparent helper). Membership laws (R4's): `simple_valid`, `applyChange_valid`,
  `applyChange_v1`.
- `snapsMade γ S` (excl, client), `snapValid γ s` (pers). Laws: `snap_make`, `snapValid_made`,
  `snapValid_committed`.
- `readCtxs γ U` (excl, client), `readCtx γ c Q` (pers), `readState γ c i` (pers). Laws:
  `readCtx_register`, `readState_fire`, `readState_registered`.
- `msgSent γ m` (pers), `msgCredit γ m` (excl; copyable when `γ.dup`). Laws: `msgCredit_intro`,
  `msgCredit_dup`, `msgSent_snap`, `msgSent_replaceSnap`.
- `raftState γ id D` (excl, client: the durable state), `nodeVacant γ id` (excl),
  `freshIds γ U` (excl), `bootLog γ boot` (pers). Laws: `cluster_alloc`, `freshIds_take`.

Per node (`n` a `*node` or a `*RawNode`):
- `isNode n γ id` (pers), `nodeRunning n q` (fractional), `nodeStopped n` (pers),
  `nodeDriver n γ st` (excl: the Ready loop's token), `nodeConf n γ v` (excl: the configuration
  view), `deliveredLb n γ l`, `appliedLb n i`, `storSnapLb n j`, `nodeStorage n γ S` (pers),
  `readyStor n s k es` (excl: the batch's storage writes left), `isReadyChan n ch` (pers),
  `rawNode rn γ id` (excl). Laws: `nodeConf_confAt`, `deliveredLb_committed`, `deliveredLb_mono`,
  `nodeDriver_delivered`, `appliedLb_mono`, `storSnapLb_mono`, `zero_lbs`, `rawNode_drop`,
  `nodeRunning_fractional`; the storage updates `readyStor_install`, `readyStor_append`,
  `stor_compact`, `stor_createSnapshot`, `stor_setHardState`; `readyChan_recv` (the `Ready`
  receive as Perennial's channel `recvAu`, for `select`).
- Transparent helpers: `readyGot` (what a `Ready` gives), `readyEnter`, `readyCheck`, `readyOwn`,
  `readyMsgsOwn`, `readyDq`, `hsPtr`, `hsOpt`, `snapOpt`, `nodeErr`, `propErr`, `errIs`,
  `memStorIface`, `nodeIface`, `ConfigOk`.
- Storage: `memStor ms σ` (excl), `isStorage st S cf` (transparent: the `Storage` interface's
  contract, a method bundle like `sync.isLocker`; `memStor_isStorage`), `loggerOk lg` (pers).
- Errors: `errs_init` (raft's error variables, distinct, non-nil), `errIs_agree`.
- Provisional raftpb ownership (3h's, to be replaced at integration): `entriesRO`, `msgPts`,
  `hardStatePts`, `snapshotPts`, `confStatePts`, `confChangePts`; raft structs: `softStateOpt`,
  `readStatesRO`, `peersPts`, `statusOwn`. Internal: `nodeLoop`, `nodeFresh`, `stepOk`.
- Generic laws: `persistent`, `timeless`, `exclusive`.

## Main changes from the old specs

- **Over opaque predicates and values.** Messages are `Msg` values with `msgSent`/`msgCredit`
  (was `stepIn`'s bundle over Go pointers, `QMsg`, `MsgSt`); no `N` namespace parameter (it is
  `γ.ns`); no storage keys (`GName K`), no `nodeStartedFresh`, `snapLocalMsg`/`nodeSnapLocal`,
  `readyFits`/receipt bounds, `committedAtTerm`, `nodeCommitLb`.
- **Storage restated.** Any `Storage` implementation, through its contract `isStorage st S cf`
  over the contents model `StorState` (was `isStorageP` with range ownership `memLog`/`memEnd`/
  `memCompacted`, and `restartStorage`'s method triples). Raft holds `S σ` once attached; the client
  writes through updates raft hands out (`readyStor` from the `Ready`, `stor_compact` with
  `appliedLb` and `storSnapLb`, `stor_createSnapshot`, `stor_setHardState`). The `MemoryStorage`
  methods are logically atomic over `memStor`, the same spec detached or attached (was `memStorAt`'s
  modes). `InitialState` is non-atomic (it reads unlocked).
- **One start spec for all durable states**: `RestartNode` (and `NewRawNode`) from any storage
  holding the durable state (`StorageHolds`), after snapshots too; the bootstrap-length premise
  dropped (a joiner restarts at the empty configuration at index 0).
- **Bootstrap log**: with one, the configuration at index 0 is empty, the bootstrap `AddNode`s are
  decided at allocation, and a node's view after `StartNode` is past them; `ApplyConfChange`
  accepts an entry below the view when its change is a no-op (replaces the old special
  `Membership.simple` at 0 and the restart's skip rule).
- **Configuration premises** are `ConfigOk` (`validate`, the size-limit panic); `CheckQuorum`,
  `PreVote`, `StepDownOnRemoval`, `DisableProposalForwarding` (was required off), size limits are
  free. `ReadOnlyOption`, `AsyncStorageWrites`, `DisableConfChangeValidation` stay scope
  restrictions (no user sets them).
- `RawNode` specs share the node's vocabulary (`rawNode rn` for the thread-unsafe token, the rest
  keyed by `rn`; was `ownRawNode`/`RNState`/`RNMode`).

## Left out

- `status.go`'s `getProgressCopy`, `getBasicStatus`, `getStatus`; `rawnode.go`'s
  `readyWithoutAccept`, `acceptReady`, `applyUnstableEntries`, `needStorageAppendMsg`,
  `needStorageAppendRespMsg`, `newStorageAppendMsg`, `newStorageAppendRespMsg`,
  `newStorageApplyMsg`, `newStorageApplyRespMsg`: internal, stated over the raft struct, which is
  R2's vocabulary (requested in `req/go_etcd_io_raft_v3.md`).
- `util.go`'s `isMsgInArray`, `voteRespMsgType`, `entsSize`, `limitSize`, `payloadSize(s)`,
  `extend`, `assertConfStatesEquivalent`, `Describe*`, `types.go`'s `pbEntryID`: the log's and the
  core's helpers (R3; util.go is in both batches' rows).
- `MemoryStorage.lastIndex`/`firstIndex` (lock-held internal helpers), `RawNode.TickQuiesced`
  (deprecated, unused, no old spec), `RawNode.WithProgress` (no user), `Status.MarshalJSON`/`String`.
- `AsyncStorageWrites` (no user enables it: etcd and every example leave it off), `ReadOnlyLeaseBased`.

## Open questions for the user

1. **Scope restrictions in `ConfigOk`**: `ReadOnlySafe` only (a lease-based read needs clock
   assumptions), no `AsyncStorageWrites`, conf-change validation on. No user sets them. Keep as
   filed scope restrictions?
2. **A storage is attached once**: `Stop` does not give `S σ` back (the storage stays in raft's
   invariant). Every user restarts on a new storage built from its durable state. Should `Stop`
   return the storage contents instead (costs gating every storage update by `nodeRunning`)?
3. **`StartNode` on a non-empty storage** (Go logs a warning and runs it as a restart) is excluded by
   the premise `S StorState.empty`; etcd calls it only without a WAL.
4. (Answered by the round-1 review: the term-free `msgSent_replaceSnap` was unsound; fixed, below.)
5. **The `Ready` updates stay gated by `nodeRunning`**, read states included, as in the approved
   candidate 11.

6. **(Round 1) A restart's configuration ahead of the WAL's commit** (completeness F1). etcd
   restarts raft at the backend's membership, at its consistent index `c`, which can be above the
   WAL's `HardState.Commit` (a commit-only hard state is not fsynced; the apply thread gets entries
   before the WAL save: `bootstrap.go:632-636` says so). Adopted: `RestartNode`/`NewRawNode` take
   the configuration at any committed point `a ≥ max σ.off Applied` (`confAt γ a m`, no bound by the
   stored commit); the entries in `(applied, a]` are below the view (etcd does not re-apply them).
   This puts on raft's proof (R2) that a tracker at a committed configuration ahead of the node's
   commit is safe. **Alternative** if R2 cannot carry it: keep `a ≤ σ.hs.commit` as a filed scope
   restriction, under which etcd's restart after such a crash is not covered (and etcd would need to
   sync the commit with the backend, or record the WAL commit's configuration).
7. **(Round 1) A snapshot whose configuration is ahead of its index** (completeness F3). etcd's
   snapshots taken during the WAL replay record the configuration at `c` with the log at
   `appliedi < c` (`nonissues/etcd-replay-snapshot-confstate-ahead.md`). Adopted: `snap_make`
   takes the configuration at any committed point `a ≥` the snapshot's index; a node installing it
   gets its view at `a` (`node.Advance`), re-applying nothing below. Same R2 obligation as 6.
   **Alternative**: snapshots only at their own configuration, with 2d excluding snapshots during
   the replay (a premise filed as a scope restriction), or etcd fixed to track the replayed
   changes.
8. **(Round 1) A crash's vacancy** (completeness S6): `nodeVacant` comes back only from `Stop`; a
   process crash must re-create it through the adequacy/crash rule. Is that the adequacy theorem's
   (I assume so), or should raft export a crash law?

## Round 1 repairs (2026-11-09)

Reviews: `reviews/R1-provability-1.md`, `reviews/R1-completeness-1.md`. Rebuilt:
`etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3` OK (131 modules, R2/R3's files included);
`go vet ./specreq/raftnode/` and gofmt clean; `etc/issues-status.py --check` clean.

Provability, first tier:
- F1 `msgSent_replaceSnap`: now requires the new snapshot within the sender's delivered log
  (`isNode n γ m.src ∗ deliveredLb n γ l ∗ ⌜s'.index ≤ |l|⌝`); `ReqSendSnapshot`'s Assumes says so.
- F2 the storage laws' masks: `⊤` (raft opens its own invariant), for the five write laws and the
  new read law.
- F3 the stored snapshot: `RestartNode`/`NewRawNode` take `σ.snap.isEmpty ∨ snapValid γ σ.snap`
  (with the generalized `snapValid`, open question 7, etcd's restored snapshot meets it).
- F4 `BootLog` fixes the bytes: `e = ⟨1, EntryConfChange, bootEntryData p.1 p.2⟩` with
  `bootEntryData` opaque (3h's wire model, requested in `req/go_etcd_io_raft_v3_raftpb.md`) and
  the law `bootEntryData_decode`; contexts non-empty (etcd's are JSON).
- F5 contexts: every `node.*` spec takes W0's `Context.ctxOk ctx` (any context: rafthttp's
  `TODO()`), and `nodeErr n ctx err`/`propErr n ctx err`'s context arm is
  `Context.ctxDone ctx ∗ isCtxErr err`.
- F6 `node.Stop.spec`: one spec over `running : Bool` (`nodeRunning n 1` or `nodeStopped n`),
  vacancy back only when it was running.
- F7 the storage contract: `Entries` without the `ErrUnavailable` arm (`ErrCompacted` exactly at or
  below the compaction point); `Term` with `j ≤ last` provided by raft and no `ErrUnavailable` arm;
  `MemoryStorage.Term.spec` requires `i < off + 2^63` (Go's signed conversion);
  `MemoryStorage.Append.spec` and `readyStor_append` require `k + |es| < 2^64` (Go's index
  arithmetic), in the update's precondition.

Provability, second tier: S1 `memStor`'s realization restated (a fractional share of the
unlocked footprint), presence requested from 3h; S2 = completeness F4; S3 = completeness F1; S4
`confAt_valid` (and `confAt_committed`); S5 `cluster_alloc` excludes local-target ids; S6/S7 the
snippets' Assumes (stop order, the view at the applied index, the `nodeRunning` share, non-joint
refusal, `applied > 0`, owned snapshots) and `ReqDeliver` steps a copy (`proto.Clone`).

Completeness, first tier:
- F1 (open question 6) and F3 (open question 7, `nonissues/etcd-replay-snapshot-confstate-ahead.md`)
  as above: `a` unbounded by the stored commit, snapshot configurations at a committed point at or
  after the index (`snap_make`, `snapValid_committed`, `node.Advance`/`RawNode.Advance`'s snapshot
  case `∃ a m, nodeConf ⟨a, m⟩ ∗ ⌜s.index ≤ a ∧ s.conf.Is m⌝`).
- F2 `committedLb_emptyV2`: an empty `EntryConfChangeV2` is committed only at a joint
  configuration; snippet `ReqEntryTypes`.
- F4 `stor_read`: an update reading the attached storage, guaranteeing `off ≤ snap.index`, the
  snapshot at least a known lower bound, `appliedLb n off`, the snapshot empty or valid, and giving
  `storSnapLb` back; snippet `ReqReadAttached`. (kvfile's `InitialState` on an attached storage
  stays excluded: it is the known race.)
- F5 `statusOwn_progress`: the `Progress` map's `ownMap`; snippet `ReqStatusProgress`.
- F6 `ReqStopRestart`'s double `Stop`: now provable (provability F6's spec).

Completeness, second tier: S2 `MemoryStorage.Entries.spec` takes `lo ≤ hi` and gives the whole
range at `maxSize = 2^64 - 1` (kvfile's `Encode`); S3 `hsPtr` takes any fraction (`MustSync`,
`IsEmptyHardState`, `isHardStateEqual` give it back); S4 `--force-new-cluster` named out of scope in
`RestartNode`'s Margin. Not done: S1 (a two-goroutine Ready/apply snippet), S7 (a "led term `t`"
fact in `Status`), S9 (a decoded-`Id` check): no first-tier need; S8 (rafthttp at most once) is
2f's.

## Round 2 repairs (2026-11-09)

Review: `reviews/R1-round2.md`; R2's requests in `req/go_etcd_io_raft_v3.md` ("from R2"). Rebuilt:
`etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3` OK (192 modules, R2/R3's included);
`go vet ./specreq/raftnode/` and gofmt clean; `etc/issues-status.py --check` clean.

- **N1, the view after a snapshot**: `node.Advance`/`RawNode.Advance`'s snapshot arm now gives
  the client a one-shot `∀ a m, confAt γ a m -∗ ⌜s.index ≤ a ∧ s.conf.Is m⌝ -∗ |={⊤}=> nodeConf
  n γ ⟨a, m⟩`: the client names the point (it knows it from its record of the snapshot; etcd takes
  its consistent index, an example the snapshot's own index). `ReqReadyLoop` assumes every snapshot
  is made at its own index's configuration and names that index. R2's `ackPost` should give the
  same wand (req item 8).
- **N2, `msgSent_replaceSnap`**: adds `s'.term ≤ m.term` (`issues/etcd-merged-snapshot-stale-term.md`,
  the fork's guard). `ReqSendSnapshot` checks it (skips a snapshot above the message's term) and
  says so in its Assumes; req item 10 updated (and the fact 2d needs: applied entries' terms at most
  the node's term).
- **N3, `ctx.Done()`**: requested from W0 in `req/context.md` ("from R1": `Context.Done.spec`,
  `Context.doneRecv.spec`), cited by name in `node.stepWithWaitOption.spec`'s sketch, on which every
  `node.*` spec with a context rests.
- **req items 2 and 8**: item 2 no longer bounds `a` by the stored commit; item 8 carries the
  round-2 reviewer's quorum-overlap argument as the safety case R2 must make.
- **R2's finding (`RawNode.Ready.spec` false)**: adopted R2's phase predicates (`ApiCore.lean`).
  Every `RawNode` spec now keeps `rawNodeAt rn γ id k adv`; `NewRawNode` gives `... 0 false`;
  `RawNode.Ready` takes `... k false` and gives `... (k+1) true` with `readyGot`; `RawNode.Advance`
  gives `... k false`; `RawNode.HasReady`, given a `readyKept rn k rd`, gives `readyFresh ... rd` on
  `false` (R2's request for `node.run`). The `RawNode` spec files import `ApiCore`. `node.Ready` is
  unchanged (`run` waits on `advancec`). `rawNode` stays as R1's name for "some phase"
  (R2's `rawNode_at`).
- **Second tier**: `appliedLb`'s meaning restated (applied, or an installed snapshot's index not yet
  `Advance`d: R3); `memStor`'s realization owns `callStats` (R2); `ReqRestartDurable`'s Assumes names
  the stored snapshot's validity (R4); `proto.Clone` of a `*Message` requested from 3h (R1); the
  `ReqReadyLoop` assumption (R5). Third tier: `statusOwn_progress`'s docstring (Inflights cloned,
  `nil` map when not leader), the nonissue's merged-snapshot wording. `BootLog`'s non-empty contexts
  stay a marked scope restriction.

- **For R3's reviews** (`R3-provability-1.md` F5/F6, `R3-completeness-1.md` F5): `isStorage`'s and
  `MemoryStorage.Entries`' success case gives `sl.len = sl.cap` (raft's log extends the slice);
  `stor_read` drops its unused `appliedLb n σ.off` conjunct and has `logStor_read`'s restated shape
  (a `storSnapLb`/`logSnapLb` lower bound in, `j ≤ σ.snap.index` guaranteed, the new bound at
  commit), so it is derivable from R3's; `Api.lean`'s header realizes `nodeStorage` as R3's
  `logStorage` (the log's invariant holds `S σ`), `storSnapLb` as `logSnapLb`, `readyStor` as
  `logPending`. `IsLocalMsg`/`IsResponseMsg` take `0 ≤ t` (`isMsgInArray` indexes an array by
  `int(msgt)`: a negative type panics; checked in util.go), with a new law `msgSent_type` (a sent
  message's type is one of raftpb's) for `Step`'s callers. `RawNode.ApplyConfChange`'s phase binder
  renamed (it shadowed the entry index).

Open question added: **9. R2's term bound** (R2's req item 5): the execution's step bound below
`2^64 - 1` must enter at `cluster_alloc.spec` (its owner); R1's statement has no such premise
today. Left to the user with R2's report.

## Notes for reviewers

- The protocol model's `Membership.applyChange` and `decodeConfChange` are opaque here (R4's and
  3h's); R1's laws about them are obligations of those batches.
- `Spec/PkgInit/os.lean` did not build at the start (generator issue, fixed by the coordinator during
  the batch).
