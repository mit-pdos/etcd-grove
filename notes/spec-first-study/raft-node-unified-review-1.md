# Review of raft's node API contract, for a client that takes snapshots and reconfigures (round 1)

Reviewer: a fresh reviewer (`spec-repair --review-only` rubric), 2026-10-28.

Commit under review: `kv-snap-reconf` at `08b9b323b0`, the `HEAD` of the worktree
`.claude/worktrees/raft-spec-review`. The only commit after `c495edc0e1` (kvreconf's Go) is `08b9b323b0`.
It touches only `issues/raft-conf-lag-model/fork-v3.7-applied-snap-config.patch` and `notes/STATUS.md`, so no
finding below is stale. (Written in the reviewer's own worktree, which the isolation allowed; the brief's
path is `notes/spec-first-study/raft-node-unified-review-1.md` in `raft-spec-review`.)

Targets:
- `interface/Proof/go_etcd_io/raft/v3/{InvNode,NodeApiVocab,ApiVocab,InvNodeCtx}.txt`;
- `interface/Spec/go_etcd_io/raft/v3/{StartNode,RestartNode,node__*}.txt`;
- where the node specs rely on them: `MemoryStorage__*.txt`, `InvStorage`, `InvMemstorage`,
  `MemstorageInstance`, `MemstorageAU`.

Go: raft v3.7 as translated (`c8217eb9`, branch `raft37-goose-lean-a1`). I read the code in the copy with
the appliedSnap fix (`/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-a2`) and assumed the fix.

Callers:
- `examples/kvreconf/*.go`: no proof yet; read in full, the intended client.
- `examples/kv`: the Go code and `Proof/github_com/mit_pdos/etcd_grove/examples/kv/`.
- etcd's server: `Proof/go_etcd_io/etcd/server/v3/etcdserver/` (`NodeBridge`, `InvBoot`, `SnapTake`, ...).

Unfolds were found mechanically: a script lists every `unfold`/`iunfold`/`delta`/`simp only [..]` of a name
defined under `Proof/go_etcd_io/raft` or `Spec/go_etcd_io/raft`. Positional `icases` are not counted.

Rubric: the agent file's, which equals `notes/spec-first-plan.md`, Phase 1b (no difference found). Rules
applied from `LESSONS.md`:
- "no caller predicate as a library predicate's parameter" (`snapOk`, `decode`);
- "no special-case predicate or spec family beside the general one" (static/dynamic);
- "every premise has a source the client sees";
- the compactor pilot's failure patterns: every mode variant, caller unfolds, a premise stricter than Go.

---

## Summary

The contract is proved and its core is good. No node spec or law has a `sorry`; raft's collection rests on 13
axioms, all protobuf, `fmt` and `context` trust-boundary specs (`etc/tcb-collections/raft.txt`). The core:
- the client's committed log in two views: `ownCommittedOps` (exclusive) and `isCommittedLogLb` (persistent);
- proposals as atomic updates with `COMM True`, in the caller's namespace;
- read contexts;
- one persistent `isNode`, with the `Ready` loop's token (`nodeDriver`) separate from the configuration view
  (`nodeConfig`).

**But no client can use it with snapshots and reconfiguration together.** The contract comes in two
families, each excluding half of what kvreconf does:
- **Static** (`isStaticCluster`, `StartNode.spec`, `RestartNode.spec`, `Advance.spec`,
  `ApplyConfChange.spec`): it takes snapshots but never changes the voters (`CCShrink`).
- **Dynamic** (`isDynamicCluster`, the `*.dynamicSpec`s): it reconfigures, but it is raft's no-snapshot mode.
  `readySnap_dynamic` concludes `False`, `sentMsg_dynamic_notSnapshot` holds, and storage cap 1 means no
  compaction. It also has no `RestartNode`, no rejection of a committed change and no auto-leave.

Neither family can start a newcomer on an empty `ConfState`. Cross-cutting premises also exclude kvreconf's
network and storage:
- no message duplication (`msgCredits` is exclusive);
- no message-shape law with leader transfer on;
- `CreateSnapshot` only at or below raft's acknowledged floor;
- a single global storage model with no wrapper law.

And `Campaign`, `ForgetLeader`, `Status` and `Stop` have no usable spec.

I found **no Tier-1 "false of the code"** finding. The Tier-1 findings are all **sufficiency** (for kvreconf,
and some for kv and the server) or **unneeded or too-strict premises**.

---

## Findings, ranked (most serious first)

### F1. No cluster takes both snapshots and reconfiguration (Tier 1: sufficient for every caller)

**Evidence**

- `InvNode.lean:628` (`isDynamicCluster`) is "raft's no-snapshot mode ... never compacted past index `1`,
  `storCap`".
- `InvNode.lean:652` (`readySnap_dynamic`): `isDynamicCluster ∗ readySnap … (some l) ⊢ False`.
- `InvNode.lean:644` (`sentMsg_dynamic_notSnapshot`).
- `StartNode.dynamicSpec` takes `storCap (interface.ok si) 1` (`Spec/.../StartNode.lean:115`) instead of
  `storageCertLink`. `MemoryStorage.Compact.spec` needs `ci ≤ γs.cap` (`MemoryStorage__Compact.lean:66`), so
  nothing is compacted.
- No law certifies a dynamic-cluster snapshot. The only one is `snapshotCert_static`, with `ConfState`
  `⟨vs, [], [], []⟩` and `al = false`.
- Static `node.ApplyConfChange.spec` needs `CCShrink (listToSet vs) …`: the voters stay `vs` and the learners
  only shrink.

**Go accepts both together.** With the a2 fix the configuration switches at `appliedSnap` (`raft.go:766-790`
of `raft-a2`).

**Callers affected**

- **kvreconf**: entirely excluded.
- **The server**: dynamic, with storage cap 1 (`InvBoot.lean:276`). Compaction is held at 1 through the
  receipt bound (`EtcdServer__snapshotIfNeededAndCompactRaftLog.lean:47`), so etcd's snapshot and compaction
  path is out of scope.
- **kv**: static. Its Go stops snapshotting after a conf change (`reconf`, `examples/kv/kv.go:250-254`), a
  workaround the spec forces.

**Restatement**

- One cluster predicate, `isCluster γ N`, with the initial membership in the boot token.
- Snapshot certificates come from the configuration view:
  `nodeConfig n γ N v ∗ deliveredLogLb n γ N l ∗ ⌜i ≤ l.length ∧ NoConfChangeIn' l v.applied i⌝ ∗ snapData … ⊢
  □ ∀ t, snapshotCert γ N ⟨⟨t, i⟩, listsOf v.membership, v.membership.autoLeave, d⟩`.
- `node.Advance` of a snapshot `Ready` moves `nodeConfig` to the snapshot's configuration, which the
  appliedSnap fix makes true.
- Storage caps are dropped.

This is D1's announced next step (`notes/STATUS.md`, "Kept for now (D1)").

### F2. The static family beside the dynamic one, and caller predicates as parameters (Tier 1 for kvreconf; the user's rules)

**Evidence**

- `isStaticCluster γ N vs snapOk` (`InvNode.lean:225`) and `isDynamicCluster γ N c0 decode`
  (`InvNode.lean:628`).
- Two triples per spec file for `StartNode`, `node.Advance` and `node.ApplyConfChange` (`spec`/`dynamicSpec`).
  This also breaks CLAUDE.md's "one Hoare triple" per spec file.
- `snapOk` is fixed at allocation, and `decode` is an arbitrary caller function (`dynamicCluster_alloc`,
  `InvNode.lean:672`).

**Why it matters**

- Both are against LESSONS 2026-10-27, which already names `snapOk` and this bifurcation.
- kvreconf's data `encodeState(kv, applied)` is a function of the *applied* log: it skips rejected changes
  and duplicates. A fixed relation of the committed log cannot say that.
- `decode` exists only so that replicas agree, but the bytes are raft's (`MarshalsConfChange`).

**Restatement**

- A TaDa snapshot set, `ownSnapSet γ S`: `CreateSnapshot` takes it and gives it back extended, and a `Ready`
  snapshot gives `⌜(i, d) ∈ S⌝`.
- Replace `decode` by `MarshalsConfChange (some o) e.data`.

### F3. Newcomers: no `RestartNode` on an empty configuration, and no node token minted in a running cluster (Tier 1: sufficient)

**Evidence**

- `RestartNode.spec` needs `csm.Voters' = vs` and `cv.ID' ∈ vs` (`Spec/.../RestartNode.lean:51,53`).
- It takes `nodeRestartBoot`, which only `cluster_alloc_static` gives (`InvNode.lean:321`). That allocation
  has no bootstrap log and a different `γ` from `cluster_alloc`'s.
- `InvNode.lean:692-699` records why `RestartNode.dynamicSpec` and `dynamicCluster_alloc_empty` were dropped:
  dynamic mode takes no `MsgSnap`.
- kvreconf's `startNew` calls `raft.RestartNode` on a fresh `MemoryStorage` with an empty `ConfState`.
- Go accepts this: `Restore` of an empty `ConfState`, and the node is not promotable. See also
  `issues/raft-conf-lag-model/joiner_empty_confstate_test.go`.

**Restatement**

- `isCluster γ N ∗ ownFreshId γ id ⊢ |==> nodeJoin γ N id`, with `ownFreshId` for the non-boot ids given at
  allocation.
- `RestartNode` over `nodeJoin` with `csm` empty, giving `isNode`, `nodeDriver` (init) and
  `nodeConfig {applied := 0, membership := ∅}`.

### F4. A committed conf change cannot be rejected by not applying it (Tier 1: sufficient; excludes a documented use)

**Evidence**

- `node.Advance.dynamicSpec` needs `NoConfChangeIn st.delivered v.applied st.delivered.length`
  (`node__Advance.lean:56`).
- `ApplyConfChange.dynamicSpec` needs `NoConfChangeIn l v.applied k` (`node__ApplyConfChange.lean:56`).
- So a skipped change blocks both `Advance` and later applies for good.
- `Node.ApplyConfChange`'s documentation (`node.go:179-183`) allows exactly that: "except when the app decides
  to reject ... in which case it must not be called". kvreconf rejects this way (`applyConf`/`validConf`).
- The static `Advance.spec` has no such premise.

**Restatement**

`nodeConfig n γ N v ∗ deliveredLogLb n γ N l ∗ ⌜v.applied ≤ k ∧ l[k]? = some e ∧ e.isConfChange ∧
NoConfChangeIn l v.applied k ∧ MarshalsConfChange (some o) e.data ∧ Membership.applyChange o v.membership =
none⌝ ⊢ |==> nodeConfig n γ N {v with applied := k+1}`.

### F5. Auto-leave excluded, and the abstract log cannot hold raft's own leave entry (Tier 1: sufficient)

**Evidence**

- `ApplyConfChange.dynamicSpec` needs `m'.autoLeave = false` (`node__ApplyConfChange.lean:58`).
- Under auto-leave, raft's leader proposes `confChangeToMsg(nil)` (`raft.go:742-763`): an
  `EntryConfChangeV2` with `nil` data (`raftpb/confchange.go:40-45`).
- `LogEntry.isFiller` is `data = [] ∧ type = 0` (`NodeApiVocab.lean:51`; `Filler`,
  `Protocol/Ghost.lean:1015`).
- So that entry is neither a filler nor a client request. `ownCommittedOps`'s meaning (`InvNode.lean:62-65`)
  fails for it.
- kvreconf uses the `Auto` and `JointImplicit` transitions.

**Restatement**

- Let raft append an empty `ConfChangeV2` while the membership has `autoLeave`. This cannot be told from the
  entry alone, since a client's `ConfChangeV2{}` has the same bytes. So either `opsOf` keeps every non-normal
  entry, or `ownCommittedOps`'s laws allow that append.
- Then drop `autoLeave = false`, and add joint `applyChange` laws (F9).

### F6. Duplicated forwarded proposals and read requests excluded (Tier 1: sufficient)

**Evidence**

- `stepIn_intro` (`InvNode.lean:499`) consumes `msgCredits`, which is exclusive: the tickets of a `MsgProp`,
  the read credit of a `MsgReadIndex` (`InvNode.lean:463-466`).
- Only `msgCredits_none` and `msgCredits_snapshot` mint new ones.
- kvreconf duplicates any message, one time in 32 (`deliver`).
- Go commits a duplicated proposal twice, and kvreconf's `applyOp` deduplicates.
- The cause is the model: one AU per entry, so at most one committed copy.

**Restatement**

- A persistent `Propose` update, fired once per committed copy.
- A duplication law for read requests.

### F7. With leader transfer on, no message-shape law, and `MsgTransferLeader` cannot be stepped (Tier 1: sufficient)

**Evidence**

- `stepIn_intro` needs `NetMsgOk` and `≠ MsgTransferLeader` for non-`MsgProp` messages.
- `NetMsgOk` comes from `sentMsg` only through `sentMsg_transferOff` (`InvNode.lean:639`), which needs
  `leaderTransferOff`.
- kv works around this in **Go**: the `deliverable` filter (`examples/kv/cluster.go:30-69`, "What raft
  promises of a Ready's messages does not say that it sends nothing else"), and the `timeouts` bound on
  `MsgTimeoutNow` (`cluster.go:71-74`), each of which needs a `tickCredit`.
- kvreconf has neither:
  - it asks random replicas for transfers, so followers forward `MsgTransferLeader`;
  - it duplicates `MsgTimeoutNow`.

**Restatement**

- `sentMsg ⊢ ⌜SentMsgOkX st⌝`, with `MsgTimeoutNow` and `MsgTransferLeader` added.
- `stepIn_intro` admits `MsgTransferLeader`.
- The `MsgTimeoutNow` tick credit travels with the message (`msgCredits`), or is justified.

### F8. No usable spec for `Campaign`, `ForgetLeader`, `Status`, `Stop` (Tier 1: sufficient)

**Evidence**

- No `node__Campaign`, `node__Status` or `node__Stop` exists.
- `node.ForgetLeader.spec` is over the old `isNodeChan` and is not importable (`etc/api/raft.txt`).
- The server assumes `Stop` returns (`rnStopOk`, `NodeBridge.lean` header).
- kvreconf calls all four.
- After `Stop`, `ApplyConfChange` returns `nil` (`node.go:562-572`), but its post promises a `ConfState`.

**Restatement**

- Add the four specs over `isNode`.
- Make the `ApplyConfChange` post `csp = null ∨ …` once a `Stop` exists.

### F9. `Membership.applyChange` is sealed, with laws only for simple v1 changes (Tier 1 for kvreconf; Tier 2 abstraction)

**Evidence**

- `InvNode.lean:586-587`: "nothing is said of joint configurations".
- The laws are only `applyChange_{addVoter,removeVoter,removeAbsent,nodeZero}`.
- kvreconf must prove, for each change, whether `applyChange o v.membership` is `some m'` or `none`. It must
  also prove that its `validConf` (confchange `Restore` + `Simple`/`EnterJoint`/`LeaveJoint`) decides the
  same.

**Restatement**

- A law tying `applyChange` to the confchange `Changer`'s result on `Restore`'s configuration, or the
  definition exposed over `Membership`.
- Joint `confStateIs` laws.

### F10. `CreateSnapshot` only at or below the acknowledged floor (Tier 1: premise stricter than Go; sufficient)

**Evidence**

- `MemoryStorage__CreateSnapshot.lean:85` needs `i ≤ x`, where `x` is from `memFloorTok`, the floor
  `Advance` published.
- Go needs only `offset ≤ i ≤ lastIndex` (`storage.go:251-253`).
- kvreconf snapshots between applied entries, before `Advance`. The entry is already appended, but above
  the floor.
- The floor stands in for "the storage holds `i`", and it feeds the storage contract's `Snapshot` clause
  `sv.Index ≤ σ.fl`.

**Restatement**

- An "appended up to `i`" witness, from the current `Ready`'s `appendReceipt`.
- The `Snapshot` clause bounded by the committed and delivered index instead of the floor.

### F11. A single global `StorageModel`; a storage wrapper needs a re-proof (Tier 2: burden, coupling; Tier 1 for kvreconf until a law exists)

**Evidence**

- `memStorageModel` is keyed by `st = memStorIface ms`.
- kvreconf passes `*kvreconf.Storage`, whose `Snapshot` may return `ErrSnapshotTemporarilyUnavailable`.
- kv wrote its own instance (`KVStorageInstance.lean`), unfolding `isStorage` and `isStorageWith`, and
  re-proved every clause.

**Restatement**

- A raft law for an embedding wrapper with a `Snapshot` that may return that error.
- Better, a per-storage model value.

### F12. kv: `RemoveMember` is unprovable for a voter (Tier 1: sufficient, for kv)

**Evidence**

- kv's `RemoveMember` is documented to remove a voter (`examples/kv/kv.go:445-453`).
- Its proof needs `RmShrink id` (`Proof/.../kv/Defs.lean:264-270`), "unsatisfiable for a voter".

**Restatement:** none needed separately. F1 and F2 dissolve it.

### F13. Leaks and missing laws (Tier 2: abstraction, size, caller burden)

**`readyRest` and `readySnap`**

- They are exposed definitions, and every client destructures them.
- They show `SnapLoan` (`ptr`, `fl`, `dlv`); the bound `Lx < receiptBound GF + γ.bootLen` (with the sealed
  `bootLen`); and `readyOut`, `snapReceipt` and `advReceipt` over `StorState` fields.
- Unfolds:
  - kv: `readyRest`, `readySnap`, `readyOut`, `advReceipt` ×3, `snapReceipt` ×2, `appendRight`,
    `appendReceipt`;
  - server: `readyRest` ×2, `readySnap` ×2, `advReceipt` ×2.
- Laws to add: `readyRest_split`, `readySnap_none`, `readySnap_some`.

**Other leaks**

- `CCShrink` in the static `ApplyConfChange.spec` is `CCApply`'s internal (`ccApplyM`, `cfgState`).
- `StartNode.spec`'s `R` frame is threaded through the `InitialState` callback.
- `Compact`'s `ci ≤ γs.cap`, and `memKey γs.ak`, `memSnapTokG`, `memSnapN` in the `CreateSnapshot` and
  `Compact` statements, name ghost fields.

**The server's unfolds of raft definitions**

- `memTokShared` ×4, `memCsArg` ×4, `certCovers`, `memStorCreated`, `memFloorTok`, `memCertAuth`;
- `nodeCtx` ×5, `nodeErr` ×5, `ctxErr` ×3, `errStopped` ×3, `stepErr` ×2, `propErr`, `errProposalDropped`,
  `doneNilCtx` ×3, `bgCd` ×2.
- Each is a missing law. For example: `nodeErr_cases : nodeErr cd err ⊢ ⌜err = nil⌝ ∨ errStopped err ∨
  ctxErr cd err`.

**`ApiVocab` exports internals**

- On the importable list, `ApiVocab` exports `RNState`, `RNMode` (`CCDec`, `CCState`), `bootInit`, `rnInit`,
  `ccPropArg`, `isRaftMsg` and `readyIdx`, all over `RaftNames`.

### F14. Uncited scope premises (metric; Tier 2)

**Configuration premises.** `StartNode`'s and `RestartNode`'s 10 configuration premises are labelled
"`NewRawNode`'s premises (unchanged)". Only `MaxCommittedSizePerReady ≠ 0 ∨ MaxSizePerMsg ≠ 0` has a source
(`issues/nonissues/raft-zero-max-size-per-msg.md`). The uncited ones:
- `DisableProposalForwarding = false`;
- `ReadOnlyOption = 0`;
- `DisableConfChangeValidation = false`;
- `AsyncStorageWrites = false`;
- `Applied = 0`;
- `MaxInflightMsgs < 2^62`.

kvreconf meets them all.

**The empty-storage premises** exclude any restart with state.

**The receipt bound.** `cluster_alloc`'s premise `receiptBound + boot.length ≤ 2^61` is the term budget, a
proof concession. It is uncited too.

---

## Per target

### `InvNode`

- **Keep:**
  - the log views and their laws (`get_lb`, `lb_prefix`, `agree`, `mono`, `nil`);
  - the read contexts (`readCtx_commit`, `readStateOk_ctx`, `readStateOk_used`);
  - `isNode` persistent, with `nodeDriver` separate from `nodeConfig`;
  - `deliveredLogLb`;
  - the caller's namespace;
  - `storageCert_*`.
- **Findings:** F1-F7, F9, F13.
- **Laws missing:**
  - every law of `nodeConfig`: there is no persistent "membership at index" and no agreement between two
    nodes' views;
  - `msgCredits` duplication;
  - message shapes with transfer on.
- **Trust:** 13 axioms (protobuf `Marshal`, `Unmarshal` and `Clone` of `ConfChange`, `ConfState`, `Entry`
  and `Snapshot`; `fmt.Errorf`; `context.ErrAny`; `DescribeConfChange`; `ConfChangeType.String`). Tester
  coverage not checked.
- **Testable** (decidable): `ConfigValid`, `NetMsgOk`, `SentMsgOk`, `BootLog`, `NoConfChangeIn`. The
  cluster predicates are opaque.

### `NodeApiVocab` / `ApiVocab`

- **Keep:** `LogEntry` with the index as position; `opsOf`; `Membership` as sets; `confStateIs`.
- **Findings:** F5 (`isFiller`); `ApiVocab` leaks `RaftNames` internals (F13).

### `InvNodeCtx`

- **Keep:** `nodeCtx`, `nodeErr` and `propErr`, and the background-context laws.
- **Findings:** missing elimination laws (F13).

### `StartNode.{spec,dynamicSpec}`

- **Findings:** F1, F2, F14 (27 pure premises, 15 binders; the `R` frame).
- `cv.ID' ∈ ps` is stricter than Go, which starts a non-member, but no caller needs that.

### `RestartNode.spec`

- **Findings:** F3, F14 (22 premises, 10 binders).

### `node.Advance.{spec,dynamicSpec}`

- **Findings:** F1, F2, F4.
- The dynamic spec does not move `nodeConfig` on a snapshot `Ready`.
- **Strength margin:** no floor witness after a snapshot `Ready`. That costs nothing: compacting at or below
  the snapshot is a no-op.

### `node.ApplyConfChange.{spec,dynamicSpec}`

- **Keep:** the dynamic one's shape: stated over `Membership`, `nodeConfig` in and out, `confStateIs`.
- **Findings:** F2, F4, F5, F8 (`nil` after `Stop`), F9, F13.
- The two `applyChange … = some m'` premises (for the decoded and for the passed change) collapse into one
  once `decode` is replaced by `MarshalsConfChange`.

### `node.{Propose,ProposeConfChange,ReadIndex,Ready,Step,Tick,ReportSnapshot,ReportUnreachable,TransferLeadership}`

- **Keep:**
  - the AUs with `COMM True`;
  - `Propose`'s error post, exactly `stepWithWaitOption`'s results (`node.go:514-551`);
  - `ReadIndex` over `isReadCtx` and a read credit;
  - `Report*` taking `isNode` only.
- **Findings:** F6 and F7 (for `Step`); `TransferLeadership`'s `leaderTransferOn` makes F7 bite.
- `Propose([])` commits a filler and never fires its AU. That is consistent, but undocumented.

### `MemoryStorage.*`, `InvMemstorage`, `MemstorageAU`, `InvStorage`

- **Keep:** `Compact`'s `ci ≤ ss.index` (cited: `issues/raft-compact-past-snapshot.md`); the registry
  certificates.
- **Findings:** F10, F11, F13 (`cap`, `γs.ak`); F1 (cap 1).
- `MemstorageAU`'s second triples are the STATUS D4 follow-up.

---

## Ranking of the targets (most in need of revision first)

1. **The dynamic family** (`isDynamicCluster`, `dynamicCluster_alloc`, `nodeDynamicBoot`, `nodeConfig`, the
   `dynamicSpec`s): F1, F3, F4, F5, F9.
2. **The static family** (`isStaticCluster`/`snapOk`, `cluster_alloc_static`, `nodeRestartBoot`,
   `RestartNode.spec`, the `CCShrink` `ApplyConfChange.spec`): F1, F2, F3, F12. It should merge into the
   unified family.
3. **`node.Step`'s vocabulary** (`stepIn_intro`, `sentMsg`, `msgCredits`, `tickCredit`,
   `leaderTransferOn/Off`): F6, F7.
4. **The missing `Campaign`, `ForgetLeader`, `Status` and `Stop` specs**: F8.
5. **The storage boundary** (`CreateSnapshot`, `Compact`, `StorageModel`, the certificates): F10, F11.
6. **`readyRest`/`readySnap`, `ApiVocab`, `InvNodeCtx`**: F13.
7. **`Propose`, `ProposeConfChange`, `ReadIndex`, `Ready`, `Tick`, `Report*`, `TransferLeadership`**: sound
   and usable.

---

## What kvreconf would need that is missing or excluded

| # | kvreconf's use | missing or excluding item | finding |
|---|---|---|---|
| 1 | snapshots and conf changes in one cluster | dynamic = no-snapshot (`readySnap_dynamic ⊢ False`, `sentMsg_dynamic_notSnapshot`, `storCap 1`); static = fixed voters | F1 |
| 2 | `CreateSnapshot(r.index, r.cs, data)` in a reconfigured cluster | only `snapshotCert_static` (voters `vs`, no learners, not joint) | F1 |
| 3 | its own snapshot data, decoded on install (it panics if not) | `snapOk` fixed and static only; no TaDa snapshot set | F2 |
| 4 | after an install, decide later changes on the snapshot's `ConfState` | `Advance` leaves `nodeConfig`; no membership-at-index law | F1 |
| 5 | `RestartNode` on an empty storage and an empty `ConfState`, in a `StartNode` cluster | `Voters' = vs`, `ID ∈ vs`, `nodeRestartBoot` only from `cluster_alloc_static`; no joiner token | F3 |
| 6 | reject a committed change by not calling `ApplyConfChange` | `NoConfChangeIn` in `Advance.dynamicSpec` and `ApplyConfChange.dynamicSpec` | F4 |
| 7 | `Auto`/`JointImplicit` joint changes; raft's own leave entry | `m'.autoLeave = false`; `isFiller` | F5 |
| 8 | `validConf` = raft's acceptance, joint included | `applyChange` sealed, v1 laws only | F9 |
| 9 | compaction up to min(snapshot, applied) | `ci ≤ γs.cap` = 1 | F1 |
| 10 | snapshots between applied entries, before `Advance` | `CreateSnapshot`'s `i ≤` floor | F10 |
| 11 | `*Storage` wrapper with `ErrSnapshotTemporarilyUnavailable` | no wrapper law; global `StorageModel` | F11 |
| 12 | duplicated `MsgProp`/`MsgReadIndex` | `msgCredits` exclusive | F6 |
| 13 | transfers asked of any replica; no Go filter; duplicated `MsgTimeoutNow` | no shape law with transfer on; `MsgTransferLeader` excluded from `stepIn_intro`; tick credit per `MsgTimeoutNow` | F7 |
| 14 | `Campaign`, `ForgetLeader`, `Status().Lead`, `Stop` | no spec / `isNodeChan` spec, not importable | F8 |
| 15 | `ApplyConfChange` after `Stop` | post promises a `ConfState`; Go returns `nil` | F8 |
| 16 | `PreVote` at `RestartNode` nodes | `MsgPreVote` needs `bootedCluster` (moot with F3) | F3 |

Usable as they are:
- `Propose`, retried with a fresh AU per call;
- `ReadIndex`, with fresh contexts per replica and sequence number;
- `Ready`/`readyRecv`, `Tick`, `ReportSnapshot`, `ReportUnreachable`;
- `TransferLeadership`, given F7;
- `Advance`, without snapshots;
- `ApplyConfChange` of simple and explicit-joint changes.

kvreconf meets the configuration premises (F14).

## Go and documentation defects

- **`doc.go:94-99` versus `node.go:179-183`.** `doc.go` says `ApplyConfChange` "must be called one way or
  the other"; `node.go` says it "must not be called" for a rejected change. This is noted only inside
  `issues/upstream/raft-advance-before-applyconfchange/meta.md:202-204` ("left alone"), and there is **no
  `issues/` file of its own**. One should be written; this review did not write it.
- **Nothing new otherwise.** kvreconf's exposures are all recorded:
  - `raft-snapshot-during-apply-stale-confchange` (with the a2 fix);
  - `raft-remove-last-voter-panic` (avoided by `validConf`);
  - `raft-snapshot-without-recipient-livelock` (liveness);
  - `nonissues/raft-memorystorage-createsnapshot-bounds`.

## Uncertain points

1. **F10:** whether raft's own proof uses the `Snapshot` clause's `sv.Index ≤ σ.fl` beyond "the storage
   holds `i`". To settle: trace `#HSnapshot`'s bound through the `maybeSendSnapshot` and `newRaft` proofs.
2. **The specs are proved of a1 (`c8217eb9`), not a2.** I expect the static specs to stay true, since the
   voters never change. To settle: retranslate with `etc/goose.py --src raft=.lake/raft-fork` and build.
3. **F6:** whether a duplicated `MsgReadIndex` is harmless in raft's `readOnly` bookkeeping, which is keyed
   by context. To settle: a Go test duplicating a forwarded `MsgReadIndex`.
4. **F9:** whether the `Spec/go_etcd_io/raft/v3/confchange/*` triples are stated over the internal
   `CCState`. To settle: read `Changer__Simple.lean`.
5. **The unfold counts** are lower bounds: from a regex scan, with no positional `icases` and no `rw`.
6. **`etc/tcb-report.py --roots` was not run** (it needs a build). The axioms are from the committed
   baseline.
