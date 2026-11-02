# Review of the unified node-API candidate 11, round 11

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

## What was reviewed

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-7.md`, titled "candidate 11", one text.
  It is a design, and nothing of it is implemented, so no finding can be stale against `HEAD` (`bbc7ce9e61`).
- **Today's API**: the committed state. The files I cite are identical at `eb59bb8d1b` and at `HEAD` (checked with
  `git diff --stat`):
  - `interface/Proof/go_etcd_io/raft/v3/{InvNode,ApiVocab,InvMemstorage}.txt`;
  - `interface/Spec/go_etcd_io/raft/v3/{MemoryStorage__CreateSnapshot,MemoryStorage__ApplySnapshot,MemoryStorage__Compact,node__Advance,node__Propose}.txt`;
  - `Proof/go_etcd_io/raft/v3/{InvStorage,InvNode}.lean`, `Protocol/Ghost.lean`;
  - `Spec/go_etcd_io/raft/v3/MemoryStorage__SetHardState.lean`, `etc/api/raft.txt`.
- **The plan**: `notes/raft-unified-plan.md`, unchanged since `bbc7ce9e61` (no working-tree diff).
- **Go**:
  - raft a2 (`.lake/raft-fork`, `565c2bd`): `storage.go`, `node.go`, `confchange/restore.go`;
  - kvreconf: `examples/kvreconf/{kv,cluster,reconf}.go`;
  - kv: `examples/kv/kv.go`;
  - etcd's server: `server.go`, `raft.go` under `~/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261027220749-a20f6760ff43/etcdserver/`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md` (the worktree has no `spec/` skill).
- **Not run**: lake build, lean-check, Go tests.

Each finding is marked **[spec]** or **[obligation]**, and says whether §0 or the plan carries it.

## Summary

Candidate 11 fixes J1's core (`Ok`/`clamp` over `Valid`, `WellFormed`, the size check), J2's core (one continuation
per branch), J3 (`nodeLive`), J4's home and law, and J5. J8 and most of J9 are claimed in the header but the text
is unchanged.

The whole text was then reread, and it has three false or unprovable statements. Each needs only a premise or a
deletion:

- **K1.** `storHoldsLb` cannot be proved persistent with today's `ApplySnapshot` spec, which the candidate keeps.
- **K2.** `snapshotCert_make` lost its `i < 2^61` premise when G6 made `readyFits` bootstrap-only. Without that
  premise it is unprovable for a cluster with no bootstrap log (kv).
- **K3.** `applyChange_valid`, kept by name in §1, is false of Go's `applyChange` (J1's residual).

**Tier 1 (3)**: K1, K2, K3. **Tier 2 (2)**: K4, K5. **Tier 3 (6)**: K6-K11.

**Go defects**: none new.

**Freeze?** Not yet, but close. Once K1-K3 are fixed, only Tier 2-3 items remain, and those are records and
wording. K1 is the only one that needs a decision (two options below). After it, the candidate is ready to
implement.

---

## Review 10's findings: fixed?

| review 10 | candidate 11 | status |
|---|---|---|
| J1(a) `Ok`/`clamp` over `isSome` | `Ok`/`clamp` over "`some m'` and `m'.Valid`"; `clamp_eq` takes `m.Valid` | **Fixed**. But §1 still keeps `applyChange_valid` unrestated, and that law is false (K3) |
| J1(b) kvreconf's size | §5: `validConf` rejects at `len(prs) ≥ 2^62`; size law `ownCfgPairM ⊢ size = m.ids.size` | **Fixed** (design). The Go change must keep the `prs` the `Changer` returns: today `validConf` discards it, `_, _, err =` (`kv.go:232-237`) |
| J1(c) `WellFormed` too weak for `Restore` | `WellFormed := empty ∨ Valid` | **Fixed**. Checked against `restore.go:79-104`: voters come first in `in`, a `Valid` joint config has non-empty outgoing and incoming halves, and the empty `ConfState` gives no ops. `Membership.empty` is not defined in §1 (K11) |
| J2 branch-tied outcomes | `COMM (⌜si<i⌝ -∗ Qok) ∧ (⌜i≤si⌝ -∗ Qold)`, and `err` tied to them in the post | **Fixed** in substance. Review 10's "smaller gaps" (the token's state, the mask, `memKey`) were not taken (K4) |
| J3 server's `nil` `ConfState` | `nodeLive` (fractional); `Stop` takes it whole | **Fixed** (spec). The server's route for the token is not recorded, and the prose overclaims (K5) |
| J4 `storHoldsLb` home, receipt, persistence | a `StorageModel` field; law over `appendReceipt`, giving `st'.delivered`; docstring "an invariant of U8" | Home and law **fixed**. Persistence is **not**: the invariant it relies on cannot be proved under today's `ApplySnapshot` (K1). The plan's U8 does not mention it |
| J5 `SetHardState` importable | stated | **Fixed** (design). `memStorMeta` comes from `NewMemoryStorage`'s post (`Spec/.../NewMemoryStorage.lean:49`) |
| J6 `MsgSnap` bound without a bootstrap log | "by the certificate's `SnapListsOk`" | **Moves the problem**: the certificate's maker must now prove the bound (K2) |
| J7 clients' hand-off | header says U10 | **Not in the plan**: U10 is unchanged (K6) |
| J8 assembly law as a record update | header says fixed | **Not fixed**: the text is review 10's wording, word for word (K7) |
| J9 nits | header says fixed | **Mostly not fixed** (K8) |

---

## Findings, ranked

### Tier 1

#### K1. [spec; the plan's U8 does not carry it] `storHoldsLb`'s persistence is unprovable while `ApplySnapshot` keeps today's spec

**Principles**: *Sound* (each law must be provable); *every premise has a source*.

**Evidence**:
- §4 keeps today's storage specs "with one change to `CreateSnapshot`'s bound", so `ApplySnapshot`'s spec is
  unchanged. Its only lower bound on the index is `σ.fl ≤ index` (`MemoryStorage__ApplySnapshot.txt`).
  `storageCert_register` lets a client register any certified snapshot (`InvNode.txt:152-154`).
- Go's `ApplySnapshot` replaces the log by one dummy entry at the snapshot's index (`storage.go:234-235`). After
  that, `lastIndex = index`.
- `appendReceipt_holds` gives `storHoldsLb st st'.delivered` before `Advance`. At that point `st'.delivered`
  includes the Ready's committed entries, so it can be longer than the floor. Raft raises the floor only at
  `Advance` (`node__Advance.txt`: `storFloor x ∗ ⌜|delivered| ≤ x⌝`; `InvStorage.lean:186-195`, 518-521).
- So `MemoryStorage`'s proof of `storHoldsLb` would have to keep `lastIndex ≥ |l|` across an `ApplySnapshot` whose
  precondition allows `fl ≤ index < |l|`. It cannot.
- If it could, `CreateSnapshot(|l|)` would then hit `Panicf` (`storage.go:250-252`) under the candidate's
  precondition.
- No real client reaches this. A client holds `ownStorage` only through a snapshot `Ready`'s loan
  (`ApiVocab.txt:19-24`). That loan comes after an `Advance` that raised the floor to every `storHoldsLb` length.
  But the instance's proof cannot see that discipline. `storHoldsLb` is a `StorageModel` field that `MemoryStorage`
  must prove from its own specs.

**Callers**: kvreconf's in-`Ready` snapshot (`kv.go:355-358`) is the only call that needs the before-`Advance`
source. The server (`server.go:995-1006`, after `raftAdvancedC`) and kv (`kv.go:289-296`, after `Advance`)
snapshot after `Advance`.

**Restatement** (pick one):
- (a) Add a hold mark, a new `StorState` field `held`, raised by `appendReceipt_holds`. Give `ApplySnapshot` the
  premise `uint.Z σ.held ≤ uint.Z index`. Have the loan (`readyOut (some l)`) give `σ.held ≤ σ.fl`: raft lends
  only after an `Advance`, so `held ≤ |delivered| ≤ fl`. This is a statement change to `ApplySnapshot`, which the
  server and kvreconf meet from the loan.
- (b) Give `storHoldsLb` only from `Advance`, where `|l| ≤ fl`, so today's `σ.fl ≤ index` keeps it. Drop
  `appendReceipt_holds`, and make a §5 Go change: kvreconf snapshots only after `Advance` (`kv.go:357-359` removed).
  This is simpler, but kvreconf loses its random mid-`Ready` snapshot timing. That is the user's call.

Either way, write it in §4 and in the plan's U8.

#### K2. [spec; neither §0 nor the plan carries it] `snapshotCert_make` must take `uint.Z i < 2^61`

**Principles**: *Sound*; *every premise has a source*.

**Evidence**:
- The certificate a receiver reads carries `SnapListsOk`, which includes `uint.Z k.sid.index' < 2^61`
  (`Protocol/Ghost.lean:605-612`, `1552-1553`). The guard is `k.cl.Has x`, and a `Valid` membership has a voter,
  so the guard holds.
- J6's fix relies on exactly this: the `MsgSnap` bound comes "by the certificate's `SnapListsOk`".
- Today's `snapshotCert_static` takes the bound as a premise (`InvNode.lean:381`). kv proves it from its storage
  (`KV__run.lean:83`).
- Candidate 11's `snapshotCert_make` has no such premise. In a cluster with no bootstrap log (`boot = []`,
  `receiptBound ≤ 2^64-2`), nothing it takes bounds `l.length` below `2^61`: `readyFits` exists only with a
  bootstrap log, and the law does not take it anyway.
- Review 8's G6 restatement said "let `snapshotCert_make` take `uint.Z i < 2^61`". Candidate 9 adopted the rest of
  G6 but not this part, and reviews 9-10 missed it.

**Callers**:
- kv: `boot = []`. It has the bound from its `fits` checks and its storage floor.
- kvreconf: it has `readyFits`, so `isCommittedLogLb_length` gives the bound.
- The server: its storage's `Hpb` (`InvMemstorage.txt:147-151`).

**Restatement**: add `uint.nat i < 2^61` (equivalently `l.length < 2^61`) to `snapshotCert_make`, and say in §2
where clients get it.

#### K3. [spec; U1] `Membership.applyChange_valid` is kept and false

**Principle**: *Sound*.

**Evidence**:
- §1's laws paragraph still lists `applyChange_valid`. Today it reads `m.Valid → applyChange o m = some m' →
  m'.Valid` (`InvNode.txt:323-324`).
- With `applyChange` now Go's `confchange` (§4b, no `2^62` cut), it is false: a change adding `2^62` fresh ids
  gives `some` of a membership that is not `Valid`.
- Review 10's J1 restatement gave the fix. It was not applied.
- Nothing needs the law any more: `ConfRule.Ok` carries `Valid`.

**Restatement**: delete it, or add the premise `m'.ids.size < 2^62`. Also drop the "(F9)" label and §1's
`Restore`-over-`Valid` sentence: §4b's `WellFormed` spec subsumes it.

### Tier 2

#### K4. [spec; U8] The written-out `CreateSnapshot` triple is not over today's token, mask or resources

**Principles**: *Complete* (every caller); *Linearizability … in the shape of the closest sibling spec*.

**Evidence**:
- The triple uses `memSnapTokG st si`, with `si` an index, and post state `if si < i then i else si`. Today's
  token is `memSnapTokG γs σt` over a whole `StorState` (`InvMemstorage.txt:522`).
- `Compact` and `ApplySnapshot` read `σt.prev`, `σt.ss.index'` and the snapshot's lists (their `.txt`). The
  server's shared invariant keeps that token (`InvApplyAll.lean:123-164`, `srvStorTokN`).
- The mask is `⊤ ∖ ↑N` (the cluster's). It must be `⊤ ∖ ↑memSnapN`: the implementation fires the update with
  `memSnapN` open, and the server's `srvStorTokN` is disjoint from it (`InvApplyAll.lean:125`).
- Also missing: `memSnapRO`/`memKey γs.ak` (the latter given back), `memCsArg` in place of `csOpt`, and `ownSnapM`
  in place of `ownSnapS`.
- `al := cs.AutoLeave'` must agree with `snapshotCert_make`'s `al := m.autoLeave`. Either state that
  `confStateIs cs m` fixes `AutoLeave`, or use `m.autoLeave`.

**Restatement**: review 10's J2 triple:

```
AU <{ ∃∃ σt, memSnapTokG γs σt }> @ ⊤ \ ↑memSnapN, ∅
   <{ memSnapTokG γs (if σt.ss.index' < i then memStorCreated σt i t (some cs) data else σt),
      COMM (… -∗ Qok) ∧ (… -∗ Qold) }>
```

with `t := (l.getLast).term` and today's other resources.

#### K5. [obligation; not in the plan] `nodeLive`'s route through the server, and an overclaim

**Principles**: *an exclusive resource the code needs is covered by a token every caller can supply*; *the
postcondition says what the caller inspects*.

**Evidence**:
- In etcd it is the raft goroutine that calls `node.Stop`: `raftNode.start`'s deferred `onStop` calls `r.Stop()`
  (`raft.go:181`, `437-438`).
- It does so after `r.stopped` is sent by `run`'s deferred function, which runs after `sched.Stop()` and
  `s.wg.Wait()` (`server.go:819-831`).
- So the whole `nodeLive 1` must be reassembled on the raft goroutine:
  - the apply jobs' fraction comes back through `Scheduler.Stop`;
  - it is passed to the raft goroutine with the `r.stopped` send.
- Today the server never stops raft in its model (`NodeBridge.lean:11-13`, `rnStopOk`). So this is new proof work
  in U10, and the plan's U10 does not say it.
- Uncertain: whether `Scheduler.Stop`'s spec (`Proof/go_etcd_io/etcd/pkg/v3/schedule/Scheduler__Stop.lean`) gives
  back a job's resources.
- §3 says a fraction holder "rules out every stopped answer". That is true only of `ApplyConfChange`, whose post
  carries `nodeStopped`. `Propose`'s post gives `errStopped err` with no `nodeStopped` (`node__Propose.txt`), and so
  do `ReadIndex`, `Step`, `Campaign` and `ForgetLeader`.
- The stronger post is true: `ErrStopped` comes only from `<-n.done` (`node.go:513-545`). But no client needs it.

**Restatement**:
- Record in U10: "the server reassembles `nodeLive 1` on the raft goroutine: the apply path's fraction returns
  through `Scheduler.Stop` and travels with the `r.stopped` send".
- Narrow §3's sentence to `ApplyConfChange`, or add `errStopped err → nodeStopped` to the other posts.

### Tier 3

- **K6. [obligation; the plan] The plan does not carry candidate 11.**
  - `notes/raft-unified-plan.md` is unchanged since `bbc7ce9e61`.
  - U8 lacks: `storHoldsLb` as a `StorageModel` field, with a clause in `isStorageWith` and proofs in
    `MemstorageInstance`, `KVStorageInstance` and the kvreconf wrapper; and K1's choice.
  - U7 lacks: the `MsgSnap` bound's source (J6, now K2).
  - U9 lacks: `nodeLive`.
  - U10 lacks: the server's and kv's `storHoldsLb` hand-off through `raftAdvancedC` (J7), and K5's route.
  - U11 lacks: `SetHardState` importable, `ownCfgPairM` and the size law, and `validConf` keeping `prs`.
- **K7. [spec] J8 is not fixed.**
  - `ownTrackerM_assemble` still reads "(after `trk.Config = cfg; trk.Progress = prs`, the field writes' specs)
    `ownTrackerM trk (some m)`".
  - `trk` is a local value (`kv.go:225-228`). Write it as `ownTrackerM trk none ∗ ownCfgPairM cfg prs m ⊢
    ownTrackerM {trk with Config := cfg, Progress := prs} (some m)`.
- **K8. [spec, nits] J9 remains.**
  - The "Reviews: …-{1..7}" line is still there.
  - §0's U4 cites a `notes/decisions.md` entry that does not exist: grep for "newcomer"/"not a fold" finds only an
    unrelated line 18634. Say "(§6, to be recorded)".
  - The stopped `Step` should say that a `nil` message is excluded by the argument's ownership.
  - `Propose` of `[]` is a filler whose update never fires. Harmless, but unstated.
- **K9. [obligation, U9; uncertain] A stopped node given `P` must still produce the running post.**
  - Under the case-split convention, `Advance` at a node that has already stopped, called with `P`, owes the
    running post: `nodeDriver{handling := none}`, the floor `storFloor x ≥ |delivered|`, `storHoldsLb`, and
    `nodeConfig` at a snapshot's index.
  - Go's `Advance` then does nothing (`node.go:555-560`).
  - It is provable only if `run`'s exit (`close(n.done)`) leaves raft's ownership and ghost state in the node's
    invariant, so that `Advance`'s `done` branch can raise the floor and move the configuration on the dead
    node's behalf.
  - I did not check that this is consistent with the protocol invariant. Say in U9 how it is done.
- **K10. [spec] kvreconf's size check needs the `Changer`'s `prs`.** §5 should say that `validConf` keeps
  `cfg, prs` from `Simple`/`EnterJoint`/`LeaveJoint` (today `_, _, err`) and tests `len(prs)`.
- **K11. [spec, nit]**
  - `Membership.empty` is used in `WellFormed` but not defined in §1. Define it as `⟨∅,∅,∅,∅,false⟩`.
  - `isMemStorage st` in §4 is not a name of today's API.

## What is good

- **J1's repair is right.**
  - `Ok`/`clamp` over `Valid` make `fold_total` and `committed_fold` true.
  - `clamp_eq` takes `m.Valid`.
  - `validated` becomes exactly what kvreconf's Go computes once the size check is added. A `Changer` success
    implies `Valid`: zero ids are skipped, and "removed all voters" is rejected.
  - `WellFormed := empty ∨ Valid` is exactly what `Restore` accepts. I traced `restore.go:79-104` for simple, joint
    and empty `ConfState`s.
- **J2's continuations are right.** A sole writer, kvreconf, picks `Qold := False`. Its snapshot index is only ever
  changed by itself, and `maybeSnapshot` takes `index > snapIndex`. So `kv.go:378-379`'s panic is excluded.
- **`nodeLive` is the right resource**:
  - fractional;
  - only `Stop` needs it whole;
  - `nodeStopped` can arise only after `Stop`, since `n.done` is closed only by `run` on `n.stop`
    (`node.go:331-341`).
  - kvreconf calls `stop()` once per replica (`cluster.go:345-349`, `kv.go:304-307`) and needs no fraction
    elsewhere.
- **`storHoldsLb` as a `StorageModel` field, over `appendReceipt`, at `st'.delivered`**, is the right shape for
  the before-`Advance` snapshot. Only its persistence argument needs K1.
- **Unchanged and still right**:
  - one parameterless `isCluster`;
  - TaDa `ownSnapsMade`/`ownProposals`;
  - `RaftLeave`/`opsOf`, with the axiom's reach in §6;
  - no credits;
  - one triple per function;
  - `oc = some cs` (`storage.go:240-242`).

## kvreconf's Go still excluded

| behaviour | where | excluded by | kind |
|---|---|---|---|
| a snapshot inside the `Ready` loop, before `Advance` | `kv.go:355-358` | K1, if option (b) is chosen | spec (or §5 Go change) |
| `validConf` returning the rule's answer at the size bound | `kv.go:219-240` | §5 Go change (not made; K10) | Go change |
| a newcomer's `Storage` with `c0`'s `ConfState`; `Replica.cs` starting at it | `cluster.go:174-175`, `kv.go:24`, `244-254` | §5 Go change (not made); scope restriction in §6 | Go change |
| unmarshalling raft's automatic leave | `kv.go:443-447` | the axiom's approval (§0) | trust base |
| a joiner at `c0`; pre-votes at term 0 | `cluster.go:163-176` | U4 (§0, plan) | obligation |
| `ApplyConfChange` after a rejected entry; a snapshot pending | `kv.go:461-472` | U6m, U0/U3 (§0, plan) | obligation |
| raft's automatic leave | `raft.go:742-760` | U5 (§0, plan) | obligation |
| a forwarded `MsgTransferLeader`; `MsgTimeoutNow` | `reconf.go` (`Disrupt`) | U7 (§0, plan) | obligation |

**Not excluded** (checked):
- `SetHardState` (J5, `memStorMeta` from `NewMemoryStorage`);
- the post-`Advance` snapshot (`storHoldsLb` from `Advance`, `nodeConfig_fold`; K2's premise from `readyFits`);
- `CreateSnapshot`'s panic (J2);
- `maybeCompact`;
- the stopped paths: `r.cs = nil`, then `validConf(nil, …)` and the case-split preconditions;
- duplicated and delayed messages;
- `Status`, `TransferLeadership`, `Campaign`, `ForgetLeader`, `Report*`;
- the `Snapshot` wrapper.

## Ranking (most in need of revision first)

1. **§4's storage** (K1, K4): decide K1, (a) or (b), and write `ApplySnapshot`'s change, or kvreconf's Go change.
   Restore the triple's token, mask and resources.
2. **§2's `snapshotCert_make`** (K2): one premise.
3. **§1's laws** (K3): delete `applyChange_valid`, or restate it.
4. **The plan** (K5, K6, K9): U7-U11 updated to candidate 11.
5. **Records and nits** (K7, K8, K10, K11).

## Uncertain

1. K1: that no `MemoryStorage`-level invariant, without a spec change, could keep `storHoldsLb` across
   `ApplySnapshot`. I argued it from the spec's preconditions; I did not try a proof.
2. K5: whether `Scheduler.Stop`'s spec returns a job's resources.
3. K9: whether the protocol invariant allows a dead node's floor and configuration to be advanced ghostly.
