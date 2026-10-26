# Review of raft's public specs (2026-10-26)

A read-only review of the specs of raft's exported Go API at `lean` `fdd48848c5`: the `RawNode`
methods and `NewRawNode`, `node.go`'s `Node` (`StartNode`, `RestartNode`, the `node.*` methods),
the `Storage` contract and `MemoryStorage`, the exported helpers, the exported functions of
`quorum`/`tracker`/`confchange`/`raftpb` with their trust-boundary axioms, and the meaning of the
protocol predicates the client-facing specs are written in (`isCommitted`, the proposal deposits,
`readStateOk`, `isMessage`, the ghost-state allocation). Each finding was checked against the
definitions; "suspected" marks the ones that were not.

## Verdict

No raft spec was found wrong or vacuous. The raft collection (`etc/tcb-collections/raft.txt`)
rests on 13 axioms (nine `proto.*`, `DescribeConfChange`, `fmt.Errorf`,
`raftpb.ConfChangeType.String`, `context.ErrAny`) and no `sorry`. These hold:

- **γ:** the client cannot pick it. It is allocated fresh behind `raftCommitInv`
  (`ownRaftGhost_alloc_core` and its instances, `Protocol/Facts.lean`; `raft_dyn_alloc`,
  `Protocol/ResultsDyn.lean`).
- **Agreement:** any two `isCommitted` agree (`isCommitted_agree`, `Protocol/Ghost.lean:667`), so
  the delivered logs of all nodes are prefix-comparable.
- **Proposals:** only deposited data commits, and each deposit fires at most once (`propTk`,
  `fire_one`).
- **Reads:** `readStateOk` gives linearizable reads (`read_deposit`/`read_collect`,
  `Protocol/ReadIndex.lean`), under `ReadOnlySafe` and with no clock assumption.
- **Usability:** `kv_porcupine_safe` shows the specs can be used end to end, in the static mode
  with snapshots.

The serious findings are about a premise of the server's closed theorems that rests on raft's
`node` model, and about how narrow a client the specs support.

## Findings

### High

1. **`rnStopOkStarted` is false in the model, so the server's closed theorems that take it are
   vacuous.**
   - **The premise:** `rnStopOkStarted` (`etcdserver/NodeBridge.lean:111`) is
     `□ ∀ γ, rnIsNode γ -∗ {{ True }} n.Stop() {{ True }}`. It is one of the named Iris premises
     (`premises`) of `putget_safe`, which takes it through `Hprem : ∀ hG, ⊢ putget.premises …`
     (`examples/putget/Results.lean:72`). The examples watchkv, authkv, common (and through it
     putget3), cachekv, k8setcd3 and linkvtxn take it too.
   - **Why it cannot hold:** `rnIsNode γ` is `isNode` (`InvNode.lean:951-953`), whose `stop`
     channel is `isHandshake γ.stop nv.stop' (fun _ => False) True`. The handshake invariant
     (Perennial `Golang/Theory/Chan/Idioms/Handshake.lean:29`) requires `P v` in every state with
     a send in flight (`SndPending`/`SndCommit`). `Stop`'s first step offers a send on `n.stop`,
     and `run`'s loop is always ready to receive it. A world holding `isNode` can therefore never
     take that step and close the invariant, so the triple is false wherever a node exists, and
     `⊢ rnStopOkStarted` is false.
   - **Consequence:** `Hprem` cannot be met, so `putget_safe` and the other closed theorems that
     take it hold vacuously. `kv_porcupine_safe` does not take it.
   - **Earlier fix:** D19r (A) (`notes/decisions.md:10053`) restated `∀ n, rnStopOk n` as this
     premise because the old one was false in the model. The new premise has the same defect,
     through `isNode`'s `False` payloads.
   - **Options** (a decision for the user, since they change a trusted statement):
     - (a2) prove `node.Stop` from raft's model. That needs `stop`/`done` payloads that allow a
       shutdown, and the node specs then cover a stopped node (finding 2).
     - (a3) make `onStop` unreachable in the runs covered and drop the clause, as D19m did for
       `run`'s shutdown.
     - A third option is a premise not stated over `isNode`.

### Medium

2. **The `node` model never stops.** `isNode` gives `done`, `stop` and `status` the payload `False`,
   so `Stop`, `Status` and `Campaign` have no spec (`Status` is unusable, not just unspecified).
   `node.Advance.spec` and `node.ApplyConfChange.spec` promise resources (`nodeDriver`, `reqWit`,
   an owned `csPts`) that Go does not provide after `Stop` (`Advance` returns at once,
   `ApplyConfChange` returns `nil`). Specifying `Stop` will change those postconditions.
3. **No theorem shows that a bare `MemoryStorage` meets the current `Storage` contract.**
   - **What was deleted:** `memStorage_isStorage` and the `memOwnStorage_*` conversions were
     deleted as unused (`9bfc967717`), and they were of the contract before the certificate
     argument (`SC`, `sdat` in `HSnapshot`).
   - **Who depends on it:** etcd's server takes `isStorage (memStorIface …)` and `ownStorage …
     memStorEmpty` as premises (`NodeStart.lean:268-269`, `InvBoot.lean:314`,
     `bootstrappedRaft__newRaftNode.lean:98`), and nothing discharges them.
   - **Stale prose:** `MemstorageInstance.lean:37-48`, `NodeStart.lean:26,266` and
     `KVStorageInstance.lean:25,33` still cite the deleted theorems.
   - **Fix:** probably routine. `kvStorage_isStorage` proves the current contract from the same
     `MemoryStorage.wp_*`.
4. **The server's `InitialState` closure (suspected) cannot be derived from
   `MemoryStorage.InitialState.spec`.**
   - **Why:** it is `□` and carries only `memSnapTok` (`NodeStart.lean:271-280`). The proved spec
     also needs `memStorMeta`, which is not persistent.
   - **Consequence:** this is a verification gap for etcd's `MemoryStorage`, not the modelling
     choice the header calls it.
5. **`RawNode.Step` takes no `MsgProp`.**
   - **The gap:** `NetMsgOk`'s `netStepTypes` (`InvRawnode.lean:570`) excludes it. Yet `Ready`
     hands out forwarded proposals, and `NewRawNode` requires forwarding on. So a multi-node
     `RawNode` client must drop forwarded proposals, and only proposals made at the leader
     commit.
   - **Where it is covered:** `node.Step` has its own path (`fwdP`).
   - **Same gap for:** a follower's stamped `MsgTransferLeader`, and `MsgHup` (`Campaign`'s, for
     `node`).
6. **Nine `RawNode` specs are used by no proof.** `node.run` calls `raft.wp_Step`/
   `raft.wp_applyConfChange` directly. `Ready`, `Step`, `Propose`, `ProposeConfChange`,
   `ReadIndex`, `Campaign`, `ApplyConfChange`, `BasicStatus` and the report/transfer specs are
   reached by no closed theorem, so no proof has shown that they chain. Finding 5 is the kind of
   gap that leaves open.
7. **No restart.**
   - **The constructors:** `NewRawNode`, `StartNode` and `RestartNode` all require an empty
     storage (no entries, `HsEmpty`, `Applied = 0`, floor 0). `RestartNode` is a fresh start of a
     node whose `ConfState` names it. It covers neither a restart from a WAL nor a join with an
     empty `ConfState`.
   - **Out of scope by design:** crashes, durability, `MustSync` and persist-before-send
     (STATUS, "Out of scope for now").
   - **Closing the node:** the step that closes a fresh node's `rawNodeFresh` into `ownRawNode`
     over a non-empty conf state is inside `RestartNode.wp_proof` only. No exported lemma does
     it.
8. **Reconfiguration and snapshots.**
   - **Static mode:** a voter change detaches the node (`ownRawNodeC`, no γ, no further spec takes
     it), so the static mode means no reconfiguration.
   - **Dynamic mode:** it takes no `MsgSnap` (`DynNoSnap`), excludes auto-leave joint
     configurations, and needs `ApplyConfChange` before `Advance` (A1,
     `issues/raft-advance-before-applyconfchange.md`). No closed theorem runs the dynamic mode.
   - **Cluster modes:** the no-snapshot and no-transfer modes, which the server's examples use,
     mean the log is never compacted and leadership is never transferred. A `MsgPreVote` is taken
     only in a cluster started from a bootstrap log (`γ.reBoot ≠ []`).
9. **`Inflights` is not a FIFO in the model.**
   - **The model:** it keeps counts only (`Defs.lean:375-512`). `InflightsFreed` allows a
     `FreeLE` that frees nothing.
   - **The header:** it wrongly says `bytes -= ...` "can wrap". In the Go `bytes` is the
     window's sum.
   - **Other existential results:** `TallyVotes`' counts and `QuorumActive`'s active set.
10. **Specified for success only:** `confchange.Restore`, and `ConfState.Equivalent` (only the
    `nil` result).

### Low

11. **The `proto.Marshal` round-trip axioms claim more than protobuf-go.**
    - **The mismatch:** `ownCCV1`/`ownCCV2` allow arbitrary unknown-field bytes (`pbMsg … uf`,
      `InvPb.lean:178`, unconstrained), yet `MarshalConfChange(V2).spec` concludes
      `ccDecodeV1 bs = some m`. protobuf-go appends unknown fields verbatim, and bytes carrying a
      known field number would change the decode.
    - **Why it is harmless now:** such bytes arise only from `Unmarshal` (unknown numbers only) or
      not at all.
    - **Fix:** state the axioms over `uf` that is valid wire format with no known field numbers.
12. **Premises stronger than needed.**
    - `Propose` requires `data ≠ []`.
    - Every `MaxInflight` must be `< 2^62`, while `Config.validate` only checks `> 0`.
    - `ConfigValid` is stricter than `validate`.
    - `JointConfig.CommittedIndex`/`VoteResult` take full ownership of maps they only read.
    - `HEntries` requires `cap = len`.
    - A `MsgReadIndex` must be delivered at most once (its read credit), although duplication
      would be harmless in raft.
13. **Weak postconditions.**
    - `Ready` says nothing about `SoftState`/`MustSync`.
    - `Step`'s `err` is unconstrained.
    - `IsLocalMsg`/`IsResponseMsg` say only that they return.
    - `Slice`/`VoterNodes`/`ConfState` give a permutation, not sortedness.
14. **Prose that has drifted from the statements:**
    - **RawNode specs:**
      - `RawNode__Ready.lean` header: "nothing is said of `HardState`", "`Snapshot` empty".
      - `RawNode__Campaign`/`Tick`: `rs.term + 1 < 2^64`; the premise is now `≤ tc`.
      - `RawNode__ApplyConfChange.lean`: the scope paragraph; "not a premise" against A1; the
        `StepDownOnRemoval` remark.
      - `RawNode__Advance.lean`: "the rest … unchanged".
      - `RawNode__Propose.lean`: `propEntry data_sl`; the `Htk` comment.
    - **node specs:**
      - `StartNode.lean:39`: "static mode only".
      - `node__run.lean:5`: forked only by `RestartNode`.
      - `InvNodeCtx.lean:23`: "the Stop premise".
      - `isPropData`/`propDataInv` in the node specs' headers.
    - **Allocation and storage:**
      - `ownRaftGhost_alloc` is cited but does not exist (NewRawNode.lean:16,87, newRaft.lean:59,
        Ghost.lean:295,303).
      - The `ResultsDyn.lean` header lists theorems deleted on 2026-10-21.
      - The `NewMemoryStorage`, `MemoryStorage__Snapshot` and `InvMemstorage` headers predate
        R8a/D17d.
      - `InvStorage.lean:50` says "Four are specified" where there are five.
    - **Subpackages:**
      - `MajorityConfig__Slice.lean`: "only a permutation".
      - `MakeProgressTracker.lean`/`MajorityConfig__VoteResult.lean`: a non-empty voter set.
15. **Exported functions with no spec:**
    - **RawNode:** `Status`, `WithProgress`, `TickQuiesced`.
    - **Node:** `Campaign`, `Status`, `Stop`.
    - **Logging helpers:** the `String`/`Describe*` methods.
    - **raftpb:** `ConfChangesFromString`/`ToString`.

## Issues in the Go code

- Filed: [`issues/raft-compact-past-snapshot.md`](../issues/raft-compact-past-snapshot.md).
  `Compact`'s documentation asks only for `≤ applied`. Compacting past the storage's snapshot makes
  the leader panic when a follower lags (reproduced). etcd is not affected.
- Not filed:
  - `MemoryStorage` keeps the caller's `data`, `HardState` and entry pointers, without a
    documented no-modify rule. This is Go convention, and the specs take them read-only.
  - `isMsgInArray` panics on a negative `MessageType`, which is an invalid enum value and not
    reachable from the wire.
