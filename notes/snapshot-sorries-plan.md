# The SNAPSHOT-SORRY track (2026-10-31, branch `snap-sorries`)

The user's "go ahead with the snapshot sorries" (2026-10-31), after the merge of `auth-a4`. The
list is `notes/raft-unified-plan.md`, "Repair: snapshot sorries" (#1-#3, #6-#11; `grep -rn
SNAPSHOT-SORRY Proof Spec`). This file records what each needs beyond what that table says, as
found, and the order of the work. The user was away during the first part: statement changes to
trusted or exported results are recorded here as proposals, not made.

## Findings

### #9 `EtcdServer.snapshot`: what `CreateSnapshot` takes that `snapshot.spec` does not give

`MemoryStorage.CreateSnapshot.spec` (the repair's) takes `memLog γs ai □ [e]`, `J.SV (memSnapMade ai
e.Term' c nil)` (`snapshotValid cl`), `J.DL ai` (`storDL`), `memSnapLb γs 0`, and the conf state
**owned or read-only, non-`nil`** (`ownCSM cs dq c`). `snapshotValid` comes from
`snapshotCert_make` + `snapshotCert_valid` (as kv's `kv_snap_make`), which take:

1. **The conf state at the applied index.** `confStateIs c m` with `confAt cl ai m`. The membership
   is the boot configuration at every index (`srv_confAt_simple`: the rule keeps `simple cfg`), so
   what is missing is only **`ep.confState` reports `simple cfg`** once an entry is applied.
   `snapshot.spec` has `epConfState ep cs` (`epCsOk`: `nil` or some read-only conf state), nothing
   about its content. In Go (`server.go:808`), `ep.confState` starts as the storage snapshot's
   (empty at a fresh start) and `applyConfChange` sets it to raft's answer (`server.go:2052`) **only
   when the change validates**; a failed validation leaves it (`:2035-2045`). So the invariant
   needs: the first conf entry validates (the boot entries: an `AddNode` per peer on a fresh
   backend, `ValidateConfigurationChange` passes), and raft's answer reports `simple cfg`
   (`raftApplyCC`'s `confStateIs cs m'`, `nodeConfig ⟨k+1, m'⟩`, `nodeConfig_confAt`,
   `srv_confAt_simple`, `confAt_agree`).
   Shape: an apply-thread invariant `epCfgOk` (`ai = 0`, or the conf state reports `simple cfg`),
   threaded through `apply`/`applyEntries`/`applyAll`/`applyConfChange` (post), `applySnapshot`
   (a snapshot's conf state is valid, `snapshotValid`), and `run`'s loop invariant (`InvRun`).
2. **The term of the frozen entry.** `CreateSnapshot` names the snapshot's term `e.Term'`, the
   storage entry's (`ms.ents[i-offset].Term`, `storage.go:257`); `snapshotCert_make` needs it to be
   the last term of a committed prefix of length `ai`. `srvSnapStor` gives a committed `A` with
   `lastTermIs A at'`, `srvFrozenAt γs ai` only `∃ e, memLog γs ai □ [e]`: nothing ties `e` to
   `A`. The raft loop knows the frozen entries are the `Ready`'s committed ones
   (`RaftLoopFreeze.lean`, `srv_batch_tail`), and `srvFrozenAt` drops it. Options: strengthen
   `srvFrozenAt` to name the committed entry (it would take the cluster's names), or a raft-API law
   relating the storage's entries at committed indices to the committed log.
3. **`SnapListsOk`**: `Membership.Valid.snapListsOk` (raft) from `confAt_valid`/`confAt_restorable`,
   `GMap.size cfg < 2^61` (the boot log has fewer than `2^61` entries, `srvBootLogOk`; `cfg`'s
   relation to it to be found), and `uint.Z ai < 2^61` (`memLog`'s own bound: `k + 1 ≤ 2^61`).
4. **`0 < ai`** (`snapshotCert_valid`): from `snapshotIfNeeded…`'s guards (`appliedi - snapi >
   count` or `appliedi > diskSnapshotIndex`), so a premise of `snapshot.spec`.
5. **`storage.releaseOk`** (the `toDisk` branch's `Release`): an opaque environment premise
   (`InvOpen.lean`), so ultimately a premise of the exported results that run the apply thread
   (`server_run`, `server_Start`, ...) and of the examples' closed theorems: **a trusted statement
   change, for the user** (cf. `snapOpensOk`, `applySnapshot`'s, "not yet a premise of any closed
   theorem").

### #11 and `applyAll`

`snapshotIfNeededAndCompactRaftLog.specFull` adds to `spec`: `isServerM`, `srvSnapDisk`,
`appliedAtLeast γr ai`, the KV commit contract with `RC`, `srvSnapStor`, `srvWTPool`/`srvWTTaken`
with `ai ≤ w`, `srvSnapFrozen`, `nodeAppliedLb ai`, `ai ≤ ciEff`, `releaseOk`; `applyAll` must hold
them at its call (stage P: `releaseOk` from nowhere, `run`'s `ciJ` gives `ci ≤ ai`). In Go the
consistent index is at least the applied index after every entry (`applyEntryNormal`'s deferred
`SetConsistentIndex` when `ConsistentIndex() < e.Index`, the conf change's on a failed
validation), so `ai ≤ ciEff` is an invariant to add to the apply thread's (`loopOk` has `p = max
ciEff ai`).

### #7/#8 under auth on: `applySnapshot.specSnap` is auth-off only

`EtcdServer.applySnapshot.specSnap` (proved on lean) has the premise `E.authMode = .off`: its
restore rebuilds the applier's off row. With auth on (authkv's server) a snapshot batch's
`applySnapshot` also restores the auth store (`server.go:1126`, `s.authStore.Recover(newbe)`),
which the on row's `srvApplyKVOn` must be re-established over. So #7's snapshot branch and #8's
job have an off proof once the two-receive notify exists, and an on proof only after a new
`applySnapshot` spec in the mode `on` (the auth store's `Recover` over the restored backend's
auth buckets: `authInv` of the image). Not started.

### #3, #7, #8: the notify protocol takes two receives for a snapshot batch

`NotifyC.lean`'s protocol has one receive and at most two sends. A snapshot batch is received twice
on the apply side (`applySnapshot`'s `<-toApply.notifyc`, `server.go:1056`, and `applyAll`'s
`<-apply.notifyc`, `:995`; line numbers of the pinned fork), and the raft loop sends twice: after
`SaveSnap`/`ApplySnapshot` (`raft.go:284`) and, for a follower, after `processMessages` (`:307`;
a leader sends once, in the `else` branch). (2026-10-31, done with #3) The two-receive notify is
`NotifyC2.lean` (`isNotify2 γ ch S1 S2`, sends `notifySnd` 0 → 1 → 2, receives `notifyRcvN γ k`);
`rnApSnap` holds `isNotify2 … True True ∗ notifyRcvN γ 0`, for #7's `applySnapshot` call and #8's
job.

### Proposal (for the user): `rnBusyS` carries the snapshot's facts

`rnBusyS` (`InvRaftNode.lean`, the driver's state while a snapshot `Ready` is out) is part of the
node contract `isRaftNodeIfc`, which `node_contract_ifc` exports. #1/#6 added the pure conjunct
`srvLE A' = strip l.dlv ∧ srvLE d <+: strip l.dlv ∧ l.dlv.length = idx ∧ 0 < idx < 2^61` (what
`Advance`'s snapshot clause needs and `rn_ready_recv` has from `readySnap`). It is a definition
inside an exported contract: done on the branch, to be approved before the merge.

### Go detail for the `epCsCfg` invariant

`ep.confState` is set at `server.go:809` (the storage snapshot's at start) and by
`applyConfChange` only when the change validates (`:2035-2052`); a failed validation leaves it.
(`applySnapshot` sets it to the snapshot's, `:1174`.)

## Progress (branch `snap-sorries`)

- 2026-10-31: #1 (`rn_ready_recv`'s `some l` case), #2 (`rnApplyTok_recv`'s snapshot case), #6
  (the snapshot `Advance` clause) proved; #9 proved (`SnapCert.lean`: `srv_snap_make`, the
  registry's certificate, and `wp_srv_createSnapshot`), #10 gone (`SnapTakeProof.lean` deleted).
  `snapshot.spec` and `snapshotIfNeededAndCompactRaftLog.specFull` (and `specFullOff`/`On`) take
  `0 < ai` (specFull: from its trigger), `GMap.size cfg < 2^61`, `epCsCfg γr cs`, `srvFrozenTerm γs
  ai at'`.
- 2026-10-31: #3 proved (`raftNode.start`'s snapshot `Ready`; `notes/decisions.md`, "The raft
  loop's snapshot `Ready`"): the two-receive notify (`NotifyC2.lean`: `isNotify2`, `notifyRcvN`),
  `srvFrozenTerms` allowing compacted indices below the last, `rnReadySnap`'s committed entries,
  fits, last term and `snapshotValid`, `updateCommittedIndex.spec` over the snapshot's model,
  `raftNode.start.spec`'s `memStorInv`/`memSnapLb γs 0`. `rnApSnap` now hands the apply side
  `isNotify2 … ∗ notifyRcvN γ 0`: #7/#8 receive twice with it.
- Left: #7, #8 (the two receives, `wp_notify2_receive1`/`2`; with auth on, a mode-`on`
  `applySnapshot`). (#11 done: "#11 progress" below.)

## #11: what `applyAll` must hand `specFull` (design, 2026-10-31)

At `applyAll`'s call of `snapshotIfNeededAndCompactRaftLog` (after `applyEntries`, the
`notifyc` receive and the `raftAdvancedC` receive), at the new applied index `ai'` and term `at'`:

| `specFull` needs | `applyAll` has / the source to add |
|---|---|
| `isServerM E.authOn`, `isServerApplyAll`, `srvWTPool`, `srvWTTaken` with `ai' ≤ w'` | has (`isServer` is `isServerM false`; `HW`, `HWA'`, `hlen'`) |
| `appliedAtLeast γr ai'` | has (`srvAppliedOwn_lb`) |
| `nodeAppliedLb nid ai'` | has: `raftAdvancedC`'s receipt (today dropped, `iintro ⟨-, -⟩`) |
| `uint.Z ai' ≤ uint.Z (ciEff st')` | **S1** a pre `ai ≤ ciEff st` and the post `ai' ≤ ciEff st'`; `applyEntries`' "ci unchanged" disjunct strengthened to the empty batch (every `Or.inl` in its proof is one), `apply`'s `max`; `run`'s loop carries it (Go: `applyEntryNormal`'s `SetConsistentIndex` when below the entry's index) |
| `srvSnapFrozen γs ai'` | **S2** a pre `srvSnapFrozen γs ai` and the post at `ai'`: the receipt's `srvFrozenRange (ai+1) (ai'+1)` with it (a lemma) |
| `srvFrozenTerm γs ai' at'` | **S3** `srvFrozenRange` naming the batch's entries (`memLog γs j □ [m.toM]` for the entry `m` at `j`), so the entry at `ai'` has the applied term (`termAfter`); the raft loop's freeze (`RaftLoopFreeze`, `srv_batch_tail`) knows them |
| `srvSnapStor mst γs γr nid ai' at'` | **S4** `memStorInv` (the raft node's, persistent), `srvRaftLogInv` (the server's), the committed prefix of length `ai'` ending at `at'` (`batchCommittedIdx`/`kvApplied`'s log), `storDL nid ai'` (the delivered log past `ai'`: with the batch's receipt) |
| `epCsCfg γr cs'` | **S5** an apply-thread invariant through `apply`/`applyConfChange` (raft's answer `confStateIs cs m'` at `simple cfg`, D3) and at the start (`server.go:809`) |
| `srvSnapDisk s γr`, `srvKVAddr ↦□ kv`, `srvKVCommitOk kv RC RC'`, `RC` | **S6** from `run`/the start (the merged snapshot's sender has the KV commit contract, `SnapSendBranch`) |
| `storage.releaseOk`, `GMap.size cfg < 2^61` | **S7** premises; `releaseOk` up to the exported results (a proposal, above) |

Order: S1 (pure, self-contained), S2, S3, then S4-S6 with `run`'s loop invariant, S7 last.

### #11 progress (2026-10-31)

- **S1 done** for `applyAll` and `run`: `applyEntries`' "ci unchanged" disjunct is the empty batch's;
  `applyAll`'s post `ai ≤ ciEff st → ai' ≤ ciEff st'`; `run`'s loop invariant (`applyRes`,
  `applyResOn`) carries `ai ≤ ciEff`, at the start from `isServerRun`'s fresh start (`ai₀ = 0`).
  Left: `applyAll` taking it as a premise once it calls `specFull`.
- **S2**: `srvSnapFrozen_extend` (`SDSnapLemmas.lean`); not yet threaded (`applyAll` must take
  `srvSnapFrozen γs ai` and `run`'s loop carry it).
- **S2/S3, revised**: the raft loop's token (`rnLoopTokP`) carries the frozen terms of its whole
  log (`srvFrozenTerms γs (pre.length+1) L`, empty at `NodeStart`), so `raftAdvancedC`'s payload
  and `applyAll`'s spec carry those of the applied log `A ++ batch` from index `1` (a fresh start:
  `applyAll` takes `ai = |A|`, `lastTermIs A at0`); `srv_frozen_of_terms` gives `srvSnapFrozen γs
  ai'` and `srvFrozenTerm γs ai' at'` from it at any applied index (an empty batch too), with no
  state threaded between batches. `srvFrozenTerm` has an `ai = 0` disjunct.
- (superseded by the revision above) **S3 done** for the receipt: `srvFrozenTerms` (`InvRaftNode.lean`) next to `srvFrozenRange` in
  `raftAdvancedC`'s payload, from `raftNode.start`'s freeze (`rn_freeze_receipt` returns the
  frozen `memLog`, `srvFrozenTerms_of_memLog`) through `rnApN`, `run` and `applyAll`'s spec.
  Left: `srvFrozenTerm γs ai' at'` from it and `termAfter` in `applyAll` (and, for an empty batch,
  from the previous batch's: `run`'s loop carries it).
- **S4, the delivered log, done**: `raftAdvancedC`'s close carries `storDL nid |pre ++ A ++ batch|`
  (`rn_storDL`, from `isNode` and the ready receive's `deliveredLogLb`), through `rnApN`, `run`
  and `applyAll`'s spec. Left for S4: `memStorInv` (the boot's) and the committed prefix
  (`run_job_body`'s `srvRLogLb`) to `applyAll`; `srvRaftLogInv` is `isServer`'s (`srvKVInvs`).
- **S6, the KV's commit, done at `snapshot`**: `snapshot.spec` took `srvKVCommitOk kv RC RC'` and
  `RC`, which no caller could give: `Commit()` needs the store writer's tokens (`writerFrag`,
  `writerOwn`), which are inside `srvApplyKVCore`, which the spec also takes. Now `snapshot` (and
  `specFull`, `specFullOff/On`) take the KV's static facts (`∃ kv, srvKVAddr s ↦□ kv ∗ txn.isKV kv
  E.s E.γ`, `NewServer`'s `srvBuilt` `Hkv`) and the write budget (`srvWTPool`); the proof takes a
  receipt at a Go step (`wp_apply_core` on `ID.String`, so `zap.String`'s `FuncResolve` is left
  for it), the writer's tokens and a write token from the row (`srvApplyKVCore_commit`) and calls
  `store.Commit`'s proved spec (`srvKVCommitOk_of_kv`, a new callee in the server's link). Left
  for S6: the KV's facts and `srvSnapDisk` from the start through `run` to `applyAll`.
- **The WAL's open token and `diskOk`** (`notes/decisions.md`, "The WAL's readiness and one disk
  premise", settled): `snapshot`'s `SaveSnap` is `isRNWal`'s, at the apply thread's half
  (`rnWalTok (srvRAddr s) q`, pre and post of `snapshot`, `specFull`, `specFullOff/On`), with
  `walSaveOk`; the token is built at `NewServer` and rides `isServerRun` (`Hwth`), with
  `⌜storage.diskOk⌝` (`Hdisk`). `snapshot` and `specFull` take two new obligations of `SaveSnap`'s:
  the snapshot's term non-zero (`specFull`: `0 < ai → at' ≠ 0`) and a voter (`0 < GMap.size cfg`).
  Left for the switch: `Hwth` from `isServerRun` through `run`'s job chain to `applyAll` (beside
  the `nodeRunning` half, `HQR`), and back to `raftNode.stop` in `run`'s defer (its spec takes it);
  `at' ≠ 0` (the applied entry's term: raft's terms are positive past index 0) and `0 < size cfg`
  (the boot voters, `γ.vs = ps ≠ []`) at `applyAll`; `walSaveOk`, `releaseOk` from `Hdisk`. The
  raft loop's `SaveSnap` (#3) has its half (`rnWalTok`, the loop invariant).
- **SaveSnap at the pointer level** (2026-10-31, the user's decisions): the two obligations above are
  gone. `isRNWal`'s `SaveSnap` takes the metadata with its conf state, index and term pointers set
  (`smPtsV`, `InvPbSnapSet.lean`; what `walpb.ValidateSnapshotForWrite` checks, a nil conf state
  included, slightly stronger than Go's "nil only at index 0"), `CreateSnapshot` returns such a
  snapshot (`ownSnapV`; its clone by a fifth conjunct of the `proto.CloneSnapshot` axiom, approved),
  so `snapshot`'s `at' ≠ 0` and `0 < size cfg` premises are dropped. `srvMemOk`'s voter bound is
  `< 2^61` (from `NewServer`'s `ps.length ≤ 2^20`), which gives `specFull`'s.
- **S5, `ep.confState` the voters'** (done 2026-10-31, before `specFull`'s switch): Go updates `ep.confState` only on a validated change
  (raft's answer, `confStateIs cs m'`; `m'` is the voters' by `nodeConfig_confAt` and
  `srv_confAt_simple`); a failed one leaves it. A fresh start's is the empty storage snapshot's, so
  it is the voters' once the first boot entry validated, on the fresh backend: the approved law
  `membership.membersOfBk_empty` (empty buckets decode to no members; reviewed: survives,
  `notes/axiom-review/members-empty.md`) gives `ccValidOn restBootBk m` for the boot AddNode. Steps:
  `srvRaftLogInv` carries the boot entries committed (`srvRLogLb γ (bootEntries boot)`), so a
  non-empty applied log starts with the boot's first entry; `applyConfChange`'s post says
  `ep.confState` is the voters' after a validated change, unchanged otherwise; `apply`'s loop,
  `applyEntries` and `applyAll` keep `⌜L = []⌝ ∨ epCsCfg γr cs` for the applied log `L`; `run`'s
  `applyRes` carries it. As built: `epCsVoters γs cs` (`InvApplier`; `epCsCfg γr` is it at `γr.raft`) and
  `epCsAt γs L cs := ⌜L = []⌝ ∨ epCsVoters γs cs`; `srv_first_entry` (the loop's first entry is the
  boot AddNode), `ccValidOn_boot`; `applyConfChange`'s post `epCsVoters γs csl ∨ ⌜ccValidOn rs.bk m =
  false ∧ csl = cs⌝`; `apply`/`applyEntries`/`applyAll` take `epCsAt ρ.raft A cs` and give it at
  `A ++ ms`; `applyRes`/`applyResOn` carry `epCsAt C.ρ.raft A cs`.
- **#11 done** (2026-10-31): `applyAll` (`spec`, `specOn`) calls the snapshot spec (the former
  `specFull`, now `snapshotIfNeededAndCompactRaftLog.spec`, with `specOff`/`specOn`; the no-snapshot
  spec, its `wp_proof` with SNAPSHOT-SORRY #11, and their corollaries deleted). `applyAll` takes
  `storage.diskOk`, `ai ≤ ciEff st` (`applyRes`'s), `srvSnapDisk s γr`, the KV's static facts at
  `E` (returned at `E'`), `memStorInv` of the node's storage and the WAL's half `rnWalTok … q`
  (returned); the voter bound comes from its own `srvApRes` (`srvApRes_cfg_size`), the committed
  prefix, `srvSnapStor` and the frozen terms from the `raftAdvancedC` receipt
  (`srv_frozen_of_terms`). The snapshot spec's `epCsCfg γr cs` premise is weakened to
  `⌜uint.Z ai = 0⌝ ∨ epCsCfg γr cs` (nothing applied: `applyAll`'s `epCsAt` at an empty log; its
  proof refutes `ai = 0` from the snapshot's trigger). The sources, in `run`: `rnSnapOnce`'s
  continuation hands `memStorInv` (`InvBoot`'s `rnSnapOnce_of_tok` has it); `srvSnapDisk_of_RO`
  (`InvRun`) builds `srvSnapDisk` from `isServerRun`'s `srvSnapBoot` and the node; `isServerRun`
  and `isServerRunOn` gain `"#Hkvf"` (the KV's facts, `start`'s `srvReadBuilt`) and
  `isServerRunOn` `"Hsnapb"` (as `isServerRun`'s); `applyRes`/`applyResOn` carry the KV's facts at
  the batch's backend and `Hwth`; `run_job_body(On)` take `diskOk`, `srvSnapDisk`, `memStorInv`.
