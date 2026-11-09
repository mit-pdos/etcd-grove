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
4. **`msgSent_replaceSnap`** (etcd's merged snapshot message) drops the old law's premise that the
   new snapshot's index was known committed at the message's term: I believe the follower's restore
   of any committed snapshot is safe at any term (argued in the law's comment); the provability
   review should check it against R2's invariants.
5. **The `Ready` updates stay gated by `nodeRunning`**, read states included, as in the approved
   candidate 11.

## Notes for reviewers

- The protocol model's `Membership.applyChange` and `decodeConfChange` are opaque here (R4's and
  3h's); R1's laws about them are obligations of those batches.
- `Spec/PkgInit/os.lean` did not build at the start (generator issue, fixed by the coordinator during
  the batch).
