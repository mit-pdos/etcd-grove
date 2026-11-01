# Review of the unified node-API candidate (candidate 1 + 2 + 3), round 3

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate.md`, the result of candidate 1
  as amended by "Candidate 2" and "Candidate 3". It is a design and is not implemented, so no finding can be
  stale against `HEAD`.
- **Compared with**: the node API as committed at `eb59bb8d1b`: `interface/Proof/go_etcd_io/raft/v3/
  {InvNode,NodeApiVocab}.txt`, `interface/Spec/go_etcd_io/raft/v3/*.txt` and `ApiVocab.lean`, read with
  `git show`. The worktree is at `HEAD` `0e20a1ad0f`, which retranslates raft from a2. Another agent's
  uncommitted U0 edits are in `Protocol/StepR.lean`, `StepRInv.lean`, `RefinementDyn.lean` and others. I read
  them only to judge A5, and they may change.
- **Go**:
  - raft: `.lake/raft-fork`, `565c2bd` (a2);
  - kvreconf: `examples/kvreconf/*.go`, read in full;
  - kv: `examples/kv/kv.go`;
  - etcd's server: `~/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261027220749-a20f6760ff43/
    etcdserver/server.go`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md` (the main checkout's copy; this
  worktree has no `.claude/skills/spec/`). I also used reviews 1 and 2.
- **Not run**: build, `lean-check`, `tcb-report`.

## Summary

Candidate 3 fixes review 2's two server regressions properly:
- `Propose`'s update is one-shot again (A2);
- `isFiller` is type 0 again, and raft's own leave is recognised by where it sits in the log (A3, `RaftLeave`).
  I checked `RaftLeave` against the Go code and it is right.

It also fixes three more:
- the founders' configuration, `γ.c0 = simple ps` (A1);
- `Advance` of a snapshot `Ready` (A4);
- the order of a certificate's lists (A7).

But A1 opens a soundness hole that candidate 1 did not have. And three of review 2's points are only half
fixed. The result has **five Tier-1 findings**:

1. **B1 (new, soundness).** With `c0 = simple ps`, `cluster_alloc` hands every founder both a `nodeBoot` and
   a `nodeRestartBoot`. A client may then start one id twice, or start some founders with `StartNode` and
   others with `RestartNode`. Either way raft's committed logs diverge (a concrete run is in B1). The
   allocation must hand out one kind of token or the other, and it must state `boot ≠ [] → c0 = simple ps`.
2. **B2 (A2 half fixed).** For a duplicated `MsgProp`, `msgCredits_prop` asks the client for one update per
   entry of `st.ents`. Nothing tells the client what those entries are. kvreconf's invariant cannot accept an
   entry it cannot identify, so it cannot supply the update. A copy may also commit before the original. A
   TaDa "proposed" witness is missing.
3. **B3 (A6 half fixed).** The stopped answers are guarded by `nodeStopped`, but every precondition stays.
   After `ApplyConfChange` returns `nil`, kvreconf sets `r.cs = nil` and keeps applying and calling `Advance`.
   It can no longer meet `ApplyConfChange`'s rule premise or `Advance`'s `NoConfChangeIn`. Specs whose only
   precondition is `nodeStopped` are needed. Go makes them sound: `nil` means the change was not applied.
4. **B4 (A10 not fixed).** Read credits are still a finite supply, `2^64 - 2`. kvreconf's `Read` retries
   without bound and its network duplicates `MsgReadIndex`, so it cannot divide that supply up.
5. **B5 (A5 partly fixed).** The translation is now a2 (`0e20a1ad0f`). The model is not: in U0's working
   tree, `applyConf` still needs `r.snap = false`, and `snapRestore` moves `cidx`. So an `ApplyConfChange`
   that runs after a concurrent restore (kvreconf does this) is still outside the model.

Tier 2: the cost of A9 and of the TaDa no-snapshot argument to the server (B6, B7), `opsOf`'s new arguments
(B8), the membership in `Advance`'s snapshot post (B9), and the joiner's provability (B10).

Tier 3: kvreconf's Go changes that are not listed, stale text, and smaller points (B11 to B14).

I found no bug in the Go code. B1's divergence is a misuse that the API wrongly allows, not a raft bug.

---

## Earlier findings: are they fixed?

| finding | status in the amended candidate |
|---|---|
| R1 F1 one cluster for snapshots and reconfiguration | fixed (`isCluster`) |
| R1 F2 `snapOk`/`decode` parameters, static/dynamic family | fixed: TaDa `ownSnapsMade`, one family. `γ.rule` is a caller function fixed in `γ`, a deliberate departure from "TaDa, not HoCAP" (A8; B14) |
| R1 F3 newcomers | `nodeJoin` + `RestartNode` from `c0`: sound in Go. Provability uncertain (B10); B1 is a side effect |
| R1 F4 rejecting a committed change | fixed (`nodeConfig_reject`) |
| R1 F5 auto-leave, raft's leave entry | fixed by A3 (`RaftLeave`, checked below) |
| R1 F6 duplicates | proposals: half fixed (B2). Reads: not fixed (B4) |
| R1 F7 transfer on | stated (A9). Its protocol obligation is not acknowledged (B6) |
| R1 F8 `Campaign`/`ForgetLeader`/`Status`/`Stop` | specs added. The post-`Stop` preconditions are missing (B3) |
| R1 F9-F11, F13, F14 | promised, not reviewable yet |
| R2 A1 `c0 = ∅` false | fixed (`c0 = simple ps`). Introduces B1. The `cluster_alloc` premise is unstated (B1). kvreconf's `r.cs` is not listed (B11) |
| R2 A2 persistent `Propose` update | fixed (one-shot). The per-copy updates lack a witness (B2) |
| R2 A3 empty v2 entry as a filler | fixed, correctly. Costs `opsOf`'s signature (B8) |
| R2 A4 `Advance` of a snapshot `Ready` | fixed. The post's membership is unstated (B9) |
| R2 A5 a2 not in translation/model | translation: fixed at `HEAD`. Model: in progress, the window still excluded (B5) |
| R2 A6 `Stop` | half fixed (B3) |
| R2 A7 lists' order | fixed (`confStateIs`). `SnapListsOk` as written is off (B12) |
| R2 A8 rule's reason, `shouldApplyV3` | fixed. Verified at `server.go:2047-2053`, where `ApplyConfChange` is skipped when `!shouldApplyV3`. The `ConfRule.Ok` workload note for etcd that A8 asked for is not added (B13) |
| R2 A9 transfer mode, Q-B | mode dropped. Q-B left stale (B12). Obligations in B6 |
| R2 A10 `SnapListsOk`, reads, wrapper | `SnapListsOk` partly (B12). Reads not fixed (B4). Wrapper fine (`RestartNode.spec` takes `InitialState` as a callback premise) |

---

## Findings, ranked

### B1. `cluster_alloc` gives every founder two start tokens, and `c0` is not tied to the peers (Tier 1: sound; new in candidate 3)

**Evidence**

- `cluster_alloc` concludes both `[∗list] id ∈ ps, nodeBoot γ N ps ctxs id` and
  `[∗set] id ∈ c0.ids, nodeRestartBoot γ N id`, unconditionally.
- Candidate 1 had `c0 = ∅` for a `StartNode` cluster, so the second set was empty. A1 makes `c0` the peers'
  configuration, so `c0.ids = listToSet ps`, and each founder gets both tokens.
- `RestartNode.spec` takes "either `nodeRestartBoot γ N id` or `nodeJoin γ N id`".
- Today, `nodeRestartBoot` comes only from `cluster_alloc_static` (`InvNode.txt:33-37`), which has no
  bootstrap log. The two allocations are separate for exactly this reason.

**Why it is unsound.** Take `ps = {1,2,3}`:
- Node 1 is started with `StartNode`. Its log is the three `AddNode` entries at term 1, with `committed = 3`
  set by fiat (`bootstrap.go:59-77`, `raftLog.committed = len(ents)`), not by a quorum.
- Nodes 2 and 3 are started with `RestartNode` from `c0`: voters `{1,2,3}`, an empty log, term 0.
- Node 2 campaigns at term 1, node 3 votes for it (empty logs are equally up to date), and node 2 becomes
  leader at term 1. It appends its empty entry at index 1, term 1.
- Node 1 holds `AddNode 1` at index 1, term 1. On `MsgApp`, `findConflict` sees matching terms and keeps its
  own entry.
- Two logs now have the same (index, term) and different contents. The bootstrap entries that
  `ownCommittedOps γ boot` promises are committed are not in the leader's log.
- Starting the same id with both tokens breaks vote uniqueness the same way.

Some combination of the allocation, `StartNode.spec` and `RestartNode.spec` is therefore unprovable.

**A second gap.** The statement still takes an arbitrary `c0` beside `ps`. Nothing says `boot ≠ [] → c0 =
Membership.simple (listToSet ps)`. A founder's tracker after `Bootstrap` is `simple ps` (`bootstrap.go:77-79`),
whatever `c0` was chosen.

**Callers**: none misuses this today, because kvreconf and the server start founders only with `StartNode`.
But the law as stated lets one.

**Restatement**

```lean
theorem cluster_alloc ... :
    c0.Valid → rule.Ok → BootLog ps ctxs boot →
    (boot ≠ [] → c0 = Membership.simple (listToSet ps)) → (boot = [] → c0.voters ≠ ∅) → ... →
    ... ={E}=∗ ∃ γ, ⌜γ.c0 = c0 ∧ γ.rule = rule⌝ ∗ isCluster γ N ∗ ... ∗
        joinAuth γ (listToSet ps ∪ c0.ids) ∗
        (if boot = [] then [∗set] id ∈ c0.ids, nodeRestartBoot γ N id
         else [∗list] id ∈ ps, nodeBoot γ N ps ctxs id)
```

Or use two allocation laws. This settles Q-A: two tokens, never both in one cluster.

### B2. The per-copy updates of a duplicated `MsgProp` cannot be built: no witness of what its entries are (Tier 1: sufficient for kvreconf; A2 half fixed)

**The candidate.** `msgCredits_prop : st.msg.Type' = MsgProp → ([∗list] e ∈ st.ents, AU <{∃∃ ops,
ownCommittedOps γ ops}> … <{∀∀ t, ownCommittedOps γ (ops ++ [⟨t, e.type, e.data⟩]), COMM True}>) ⊢ |==>
msgCredits γ N st`. Its rationale: "kvreconf's invariant pays for a copy of an operation already applied: a
no-op on its abstract state".

**Why it fails.**
- A copy is not necessarily committed after its original. kvreconf's `deliver` steps the copy right after
  the original, or after a delay (`cluster.go:245-265`). Either copy can reach the leader first.
- So the client cannot reserve "the linearizing update" for the original and "a no-op" for the copy. Each
  update it gives raft, at `Propose` and for every copy, must be the generic one: "open my invariant;
  linearize this operation if its id is not yet applied, else do nothing".
- That update has to re-establish kvreconf's invariant for `ops ++ [e]`. The invariant says every committed
  decodable `EntryNormal` is a registered operation, and every committed `EntryConfChange` or
  `EntryConfChangeV2` unmarshals. Otherwise `applyEntry` panics (`kv.go:438-446`), or a stray `Put`
  changes the store with no linearization point.
- So the client must know that each `e ∈ st.ents` is an entry it proposed. Its premise has only `st`, a pure
  value it read off a pointer.
- Nothing provides that knowledge: `sentMsg` says nothing about a `MsgProp`'s entries (`isRaftMsg`,
  `ApiVocab.lean:384-386`). Review 2's restatement included this witness (`sentMsg ⊢ ∀ e ∈ props st, proposed
  γ e.data`). Candidate 3 dropped it.

**Callers**: kvreconf (duplication 1 in 32, `cluster.go:261`). The server and kv never duplicate.

**Restatement (TaDa, client-owned).**

```lean
def (sealed) ownProposed (γ : Cluster) (P : List LogEntry) : IProp GF   -- exclusive, client's
def (sealed) proposedLb (γ : Cluster) (e : LogEntry) : IProp GF          -- persistent
theorem proposed_elem : ownProposed γ P ∗ proposedLb γ e ⊢ ⌜∃ t, {e with term := t} ∈ P⌝
theorem sentMsg_prop : st.msg.Type' = MsgProp → sentMsg γ N src st ⊢ [∗list] e ∈ st.ents, proposedLb γ e
```

- `Propose` and `ProposeConfChange` take `ownProposed γ P` and give back `ownProposed γ (P ++ [e])`. A client
  that never duplicates can ignore them: a layer that keeps `ownProposed` in a trivial invariant.
- A cheaper alternative, if threading `ownProposed` costs too much: drop it and give `proposedLb` in
  `Propose`'s post. The client then keeps the persistent `proposedLb`s and matches the bytes itself.
- Correct the candidate's sentence: the copy's update is the same generic update as the original's, not a
  "no-op".

### B3. After `Stop`, the methods kvreconf still calls have no satisfiable precondition (Tier 1: sufficient for kvreconf; A6 half fixed)

**The candidate.** A6: `node.Stop.spec` gives a persistent `nodeStopped n γ N`. A stopped answer appears in a
post only under that guard, e.g. `ApplyConfChange`: `csp = null ∗ nodeStopped ∨ csp ≠ null ∗ …`. Nothing is
said of the null branch's `nodeConfig`, and no precondition is relaxed.

**What kvreconf does after `Stop`.**
- `Replica.stop` closes `stopc`, then calls `node.Stop()` (`kv.go:304-307`). The run loop may be in the
  middle of a `Ready`.
- `applyConf` stores whatever `ApplyConfChange` returns: `r.cs = cs` (`kv.go:470-472`), so `r.cs` becomes
  `nil`.
- The later conf entries of the same `Ready` are then decided by `validConf(nil, …)`, i.e. on `∅`, not by
  the rule. kvreconf may call `ApplyConfChange` on a change the rule rejects, and skip ones it applies. Then
  it calls `Advance` (`kv.go:353`).
- So `ApplyConfChange`'s premise `γ.rule (l.take v.applied) v.membership e = some o'` and `Advance`'s
  `NoConfChangeIn …` both fail.
- Nothing panics: a stopped node answers `nil` and returns, and `maybeSnapshot` skips a `nil` cs (`kv.go:372`).
  But the proof cannot get past these calls.

**What Go guarantees** (this makes the restatement sound):
- `run` closes `done` only in its own `case <-n.stop` (`node.go:449-450`).
- Once `run` has taken `cc` from `confc` (`node.go:400`), it blocks on `confstatec <- cs` (`node.go:430`);
  its `<-n.done` branch cannot fire, because only `run` closes `done`.
- So `ApplyConfChange` (`node.go:562-573`) returns `nil` **only if the change was not applied**.
- Likewise, `Advance` after `Stop` does nothing (`node.go:555-560`).

**Restatement.**
- `ApplyConfChange`'s null branch returns `nodeConfig n γ N v` unchanged.
- Add one spec, a case split on the state (not a disjunction of alternative specs), for every node method
  kvreconf calls after a stop (`ApplyConfChange`, `Advance`, `Step`, `Tick`, `Propose`, `ReadIndex`,
  `Report*`, `Status`, `Campaign`, `ForgetLeader`, `TransferLeadership`): precondition `isNode n γ N id ∗
  nodeStopped n γ N`, no other resource; post the stopped answer (`nil`, `ErrStopped`, `Status{}`, unit).
- Or: a law that `nodeStopped` turns any `nodeDriver`/`nodeConfig` into the token those specs take.

The alternative is a kvreconf Go change: leave `run` as soon as `ApplyConfChange` returns `nil`, and never
call `Advance` after it. But the delayed deliveries' `Step`s and `Report*`s on stopped nodes
(`cluster.go:254-258`) still need the `nodeStopped` path.

### B4. Read credits: a finite supply against unbounded retries and duplicates (Tier 1: sufficient for kvreconf; A10 not fixed)

**Evidence**
- The candidate keeps `readCredits γ (2^64 - 2)` from allocation, and `msgCredits_readIndex` spends one per
  copy: "the budget `2^64 - 2`, which kvreconf splits among its transport's copies".
- `Cluster.Read` retries without bound (`cluster.go:325-333`: `for { … }`).
- Each try is a fresh `ReadIndex`, and its forwarded `MsgReadIndex` may be duplicated (`cluster.go:261`).
- kvreconf has no a-priori bound on either, so no static division of the supply exists.
- kv and the server bound their reads by their id space (`readCredits γ.cl (2 ^ 48)`, `examples/common/
  Defs.lean:187`; `SrvRaftLog.lean:1572`). kvreconf's `nextRead` is a `uint64` per replica, with up to 9
  replicas.

**Restatement.**
- Tie the credit to time receipts, as ticks already are (`tickCredit_intro : ⧗n ⊢ tickCredit γ n`,
  `InvNode.txt:24`): `readCredit_intro : ⧗1 ⊢ readCredit γ`, if raft's read counter is bounded by the steps
  taken. **Uncertain**: I did not trace which 64-bit counter `rdCred` stands for (`InvNode.lean:164-167`:
  "until the read path's bounds are redesigned").
- Otherwise kvreconf must change in Go to bound its read attempts. List that as an exclusion.

### B5. The a2 window is still outside the model (Tier 1: provable; A5 partly fixed)

**What is done.** `HEAD` `0e20a1ad0f` translates the a2 fork, and a2's `appliedSnap` switches the
configuration (`raft.go:766-788`).

**What is not done.** In U0's uncommitted `Protocol/StepR.lean`:
- `snapRestore` keeps `cfg` but sets `cidx := uint.nat m.index`;
- `applyConf` still requires `r.snap = false` and `r.cidx ≤ k`.

So the model still forbids the case kvreconf hits: an `ApplyConfChange` of an entry from an earlier `Ready`,
run after the network goroutine's `Step(MsgSnap)` has restored a snapshot (`issues/raft-snapshot-during-
apply-stale-confchange.md`). Go a2 applies it to the old configuration, and the candidate's `ApplyConfChange`
spec promises exactly that.

**Restatement.** In the model:
- `snapRestore` leaves both `cfg` and `cidx`;
- `applyConf` is allowed while `snap` is set, on the pre-restore full log;
- `applySnap` sets `cidx` and `cfg`.

List this as a prerequisite of `ApplyConfChange.spec`.

**Uncertain**: the file is mid-edit.

### B6. A9 is a new protocol obligation, and it moves cost to the server (Tier 2: provable; caller burden)

- **The shape law needs a new proof.** Today a sent message's shape (`SentMsgOk`, which requires a stamped
  term `≠ 0` and excludes `MsgTimeoutNow`/`MsgTransferLeader`) comes only from the no-transfer mode:
  `isRaftMsg`'s `⌜γ.reNoXfer = true → SentMsgOk st⌝` (`ApiVocab.lean:384`). That mode needs a bootstrap log
  for the terms past 0 (`reNoXfer_ok`, `Protocol/Ghost.lean:335`).
  - "`SentMsgShape` holds in every cluster" therefore needs a new proof for every sending path. It must cover
    `c0` clusters (`boot = []`) and joiners at term 0.
  - `stepIn_intro` must admit `MsgTransferLeader`. The step proof already handles it when `reNoXfer = false`
    (`InvNodeChan.lean:469,499`); what is missing is the network-side `NetMsgOk` for it.
  - **Uncertain**: whether any raft path sends a stamped message at term 0 from a joiner. I found none: its
    rejections are at a term it adopted, `raft.go:1183,1279`.
- **The server pays.** Its network proof avoids a tick credit because a no-transfer message is never a
  `MsgTimeoutNow` (`InvNet.lean:86-89`: `SentMsgOk.ne_timeoutNow`, then `tickCredit_zero`). Without the mode
  it pays `⧗1` from each `Step` call. That is feasible, but it changes `InvNet.lean`, `InvBuild.lean:164-170`,
  `NewServer.lean:1134` and `SrvRaftLog.lean:648`.
- **Restatement.** List the protocol obligation and the server's migration in the candidate. Keep a law
  `sentMsg_shape : sentMsg γ N src st ⊢ ⌜SentMsgShape st⌝` and say exactly which types are unstamped.

### B7. The server's no-snapshot facts become invariant openings (Tier 2: caller burden, locality)

- **Today the facts are pure.** The server proves that no snapshot travels or arrives with pure laws:
  `srv_sentMsg_notSnap` (`SrvRaftLog.lean:1390-1410`), through `snapshotCert_data … (fun _ _ => False)` or
  `sentMsg_dynamic_notSnapshot`, and `srv_readySnap_none`.
- **Under TaDa they need the exclusive set.** The only route is `snapshotCert_made` + `snapMade_elem` against
  the server's exclusive `ownSnapsMade γ []`. That resource has to sit in an invariant, and each of these
  `⊢ ⌜…⌝` laws becomes a `={E}=∗` that opens it, which changes masks in their callers.
- **Restatement.** A law that lets a client that never makes snapshots give the set up for a persistent fact:
  `ownSnapsMade γ [] ==∗ noSnapsEver γ` (persistent), and `noSnapsEver γ ∗ snapshotCert γ N k ⊢ False`. Then
  the server's laws stay pure. It is an instance of the general TaDa spec, not a second family.

### B8. `opsOf r c0 l` changes every client's statement (Tier 2: coupling, size)

- **The cost.** A3 changes the signature of `opsOf`, which is used about 62 times in `SrvRaftLog.lean`, 13 in
  `KVAuthModel.lean`, and in kv's `Base`/`Lemmas`/`KV__Read`. Each use must now mention the sealed `γ.rule`
  and `γ.c0`.
- **A law keeps the server's uses.** `opsOf_noType2 : (∀ e ∈ l, e.type ≠ W32 2) → opsOf r c0 l =
  l.filter (¬ ·.isFiller)`, with today's `opsOf` kept under a name. Together with `committed_type2`, this
  leaves the server's uses unchanged.
- **`committed_type2` needs restating.** Its "(∃ o, `e.data` marshals a client `ConfChangeV2` o proposed)"
  names no predicate. Say instead: "the entry is in `opsOf` at its position, or `RaftLeave`".

**I checked `RaftLeave` against Go.** Raft appends its leave only when `r.trk.Config.AutoLeave && newApplied
>= r.pendingConfIndex` (`raft.go:742`):
- `pendingConfIndex` covers every conf entry the leader holds (`raft.go:976`, `1361`), so the entries between
  `applied` and the leave contain no conf entry;
- the leader's tracker is the rule's fold of its applied prefix (by `nodeConfig_fold` and the `Advance`
  premise);
- so the leave's prefix folds to the joint, auto-leave membership.

A client's explicit `ConfChangeV2{}` is refused while a leave is pending, or when the configuration is not
joint. So both leaves never commit in one joint period, and a client's leave at a `RaftLeave` position is
practically unreachable (and harmless, with `COMM True`).

### B9. `Advance`'s snapshot post leaves "the snapshot's" membership unstated (Tier 2: the post says what the caller inspects)

kvreconf sets `r.cs` to the snapshot's `ConfState` clone (`kv.go:403-414`). It then needs that its validation
input matches `nodeConfig`'s membership.

**Restatement**: `L = some l → nodeConfig n γ N {applied := l.dlv.length, membership := m} ∗
⌜Membership.fold γ.rule γ.c0 (strip l.dlv) = some m ∧ confStateIs l.snap.Metadata'.ConfState' m⌝`.

### B10. A joiner in a cluster with a bootstrap log: provability not shown (Tier 2: provable; uncertain)

- **Go accepts it.** The joiner's tracker is `c0`, so it is not promotable: `id ∉ c0.ids`, and `promotable()`
  is false (`raft.go:1947-1949`). Its applies of the bootstrap entries are no-ops on `c0`.
- **The model may not.** Today an `rnInit`-style node (persisted voters `c0`, empty log, term 0) exists only
  in a cluster without a bootstrap log (`cluster_alloc_static`). `RestartNode.dynamicSpec` was dropped,
  because dynamic mode took no `MsgSnap` (`InvNode.lean:692-699`, per review 1).
- **Uncertain**: whether `RInv` admits a term-0 empty-log node whose `cfg = c0`, beside founders whose ghost
  log starts with the bootstrap entries. To settle: state the joiner's initial `RState` and check `StepRInv`'s
  cases.

### B11. kvreconf Go changes the candidate does not list (Tier 3: sufficient)

- **`r.cs`'s initial value.** `newReplica` leaves `r.cs = nil` for founders and joiners (`kv.go:280-283`).
  `nodeConfig`'s membership is `c0` at `applied = 0`, so `validConf(nil, …)` (on `∅`) and the rule (on `c0`)
  agree only on the bootstrap `AddNode`s. A proof can special-case index 1 through `ownCommittedOps γ boot`,
  but initialising `r.cs` to `c0`'s `ConfState` removes that case.
- **One `Storage` for founders and joiners.** `StartNode.spec` wants an empty initial `ConfState`, while A1
  wants a joiner's storage to answer `c0`'s. Either kvreconf's `Storage` takes a flag, or `StartNode.spec`
  accepts an initial `ConfState` that is empty or `c0`'s. Go accepts the latter: `Bootstrap` checks only
  `lastIndex == 0` (`bootstrap.go:36-43`), and its `AddNode` of a voter already present is a no-op.
- **The joiner's `InitialState`.** The `c0` lists, as kv's does (`examples/kv/kv.go:68-71`): listed. Fine.

### B12. Stale or inaccurate text (Tier 3)

- **Q-B** still says kvreconf "must bound its campaigns", which contradicts A9.
- **Q-A** is answered by B1.
- **Candidate 1's `StartNode.spec` bullet** still reads `γ.c0 = ∅`, and the `cluster_alloc` comment says
  "[] when the nodes start from c0 alone". Rewrite them under A1 and B1 rather than leaving them superseded.
- **A7/A10 "`SnapListsOk` …: `index < 2^61`, no repeats, ids nonzero".**
  - `SnapListsOk` (`Protocol/Ghost.lean:605-611`) has no nonzero-id clause. It has the list well-formedness
    `CSWf`, `Nodup`, the `2^62` size bound and `outgoing = [] → al = false`.
  - Say whether it is a premise of `snapshotCert_make` or derived. If derived, `index < 2^61` needs a law
    stronger than `isCommittedLogLb_length`, which gives only `< 2^64` (`InvNode.txt:307-308`). The
    `Lx < receiptBound + bootLen ≤ 2^61` bound in `readyRest` suggests one holds. **Uncertain.**

### B13. Smaller points carried over (Tier 3)

- **No workload note.** `ConfRule.Ok` has no docstring note that etcd's own validation can remove the last
  voter (`issues/raft-remove-last-voter-panic.md`), so etcd's rule is `Ok` only after filtering (review 2,
  A8).
- **`bootedCluster` in a `c0` cluster.** `stepIn_intro` still takes `⌜≠ MsgPreVote⌝ ∨ bootedCluster γ`
  (`InvNode.txt:302`), and `bootedCluster` comes from `nodeBoot_booted` only. A `c0` cluster (`boot = []`)
  can therefore never deliver a `MsgPreVote`. kvreconf (a `StartNode` cluster) and kv (no `PreVote`) are
  unaffected. Cite it as a scope restriction, or derive `bootedCluster` from `isCluster`.

### B14. `γ.rule` is a caller function fixed in the cluster (Tier 3: a recorded departure)

PRINCIPLES' "TaDa, not HoCAP" forbids a caller-provided predicate as a parameter. `γ.rule` is not a
parameter of `isCluster`, but it is chosen by the caller and appears in `ApplyConfChange.spec`,
`nodeConfig_*`, `opsOf` and `snapshotCert_*`.

A8's reason holds: `DynCfg` is fixed in `RaftNames.reDyn` (`Ghost.lean:173-176` and `:285`). This is a
departure the principles allow when it is said so. Record it in `notes/decisions.md` with A8's reason. I
checked that `DynCfg.adj` holds for a fold that may reject (a rejected entry counts in `confCount` and leaves
the configuration), or that applies another accepted change in its place (etcd's `NodeID` 0).

---

## What is good

- **The core shape holds.** One cluster predicate; `nodeConfig` on every node, with `_fold`, `_skip` and
  `_reject`; the TaDa snapshot set (`ownSnapsMade`, `snapMade`, `snapMade_elem`, `snapshotCert_made`), enough
  for kvreconf's data (an invariant over `S`) and for etcd's (none).
- **`ConfRule` and `Membership.fold`.** `ConfRule.validated` is exactly kvreconf's `validConf`, given F9's
  laws (`kv.go:205-229`).
- **A2's one-shot `Propose`** keeps the server's `srvPropAu1`/`kvOpAu1`.
- **A3's `RaftLeave`** is right, and so is keeping `isFiller` as type 0 (B8).
- **A4's split** is right: a snapshot `Ready` carries no committed entries (`log.go:225-228`).
- **A7's `confStateIs` certificates.**
- **A8's restated reason**, and the `shouldApplyV3` scope restriction, verified at `server.go:2047-2053`.
- **A9's receipt-paid campaigns.** `tickCredit_intro` exists, and kvreconf's `Disrupt` needs no Go bound.
- **The specs added.** `Campaign` (one credit; one term step per `MsgHup`), `ForgetLeader`, and `Status`
  ("nothing about contents" is enough: kvreconf only passes `Status().Lead` to `TransferLeadership`, whose
  `lead` is free, `node__TransferLeadership.txt`).

## kvreconf's Go still excluded under the amended candidate

| kvreconf behaviour | where | excluded by | finding |
|---|---|---|---|
| a duplicated forwarded `MsgProp` (and an original that commits after its copy) | `cluster.go:261`, `kv.go:546` | no witness of a `MsgProp`'s entries for `msgCredits_prop` | B2 |
| `ApplyConfChange` (`r.cs := nil`), the next conf entries decided on `∅`, then `Advance`, after a concurrent `Stop` | `kv.go:304-307, 461-473, 353`; `check.go:177` | the post-`Stop` preconditions | B3 |
| unbounded `Read` retries; duplicated `MsgReadIndex` | `cluster.go:325-333, 261` | finite `readCredits` | B4 |
| `ApplyConfChange` of an earlier `Ready`'s entry after a concurrent `Step(MsgSnap)` restore | `kv.go:470` vs `cluster.go:268` | model (U0 in progress) | B5 |
| a joiner (`startNew`) | `cluster.go:163-178` | needs Go: `Storage.InitialState` = `c0` (listed); provability uncertain | A1, B10 |
| `r.cs = nil` at start | `kv.go:280-283` | workable with a special case; Go change recommended | B11 |
| one `Storage` type for founders and joiners | `cluster.go:133, 174` | `StartNode`'s empty-`ConfState` premise | B11 |
| forwarded `MsgTransferLeader`, duplicated `MsgTimeoutNow` | `reconf.go:107`, `cluster.go:261` | covered by A9/F7 once B6's obligation is proved | B6 |

Not excluded: snapshots between applied entries (F10), compaction (`kv.go:389-401`; after a snapshot install
`hi < first`, so no `Compact` needs a floor), unserialized and rejected conf changes, joint and automatic leaves
(A3), `Campaign`, `ForgetLeader`, `Status().Lead`, delayed `Step`/`Report*` (given B3).

## Per target

- **Allocation** (`cluster_alloc`, `joinAuth`, `nodeBoot`/`nodeRestartBoot`/`nodeJoin`): B1, B10, B13. Most in
  need.
- **`msgCredits_prop`/`msgCredits_readIndex`**: B2, B4.
- **The stopped-node specs** (`node.Stop.spec`, every method's post-`Stop` behaviour): B3.
- **`ApplyConfChange.spec` and the protocol model**: B5. The statement is right; its proof needs U0.
- **`sentMsg`/`stepIn_intro`/A9**: B6.
- **The snapshot laws** (`snapshotCert_make`/`_made`): B7, B12. Otherwise good.
- **`opsOf`, `committed_type2`**: B8.
- **`node.Advance.spec`**: B9.
- **`ConfRule`, `Membership.fold`, `nodeConfig_*`, `Campaign`/`ForgetLeader`/`Status`**: B13, B14 only.

## Ranking (most in need of revision first)

1. `cluster_alloc` and the start tokens (B1).
2. `msgCredits_prop`: the proposed witness (B2).
3. The stopped-node specs (B3).
4. Read credits (B4).
5. The model's a2 window, U0 (B5).
6. A9's shape law and the server's migration (B6), and the server's no-snapshot facts (B7).
7. `opsOf`'s signature and `committed_type2` (B8); `Advance`'s snapshot post (B9); the joiner's provability
   (B10).
8. Text and kvreconf's listed Go changes (B11-B14).

## Go defects

None new.
- **B1's divergence** is a misuse that raft's documentation excludes (all founders `StartNode` with the same
  peers, or all start from one `InitialState`). The fault is in the API's tokens, not in raft. Not filed. No
  reproduction was written (read-only review).
- **`ApplyConfChange` never returns `nil` for an applied change** (`node.go:400-433, 449-450, 562-573`): no
  defect, and it is the fact B3's restatement rests on.

## Uncertain points

1. **B4**: whether `⧗1 ⊢ readCredit γ` is provable: what raft's read counter is.
2. **B5**: U0 is mid-edit, so the model may soon admit the window.
3. **B6**: whether any stamped message is sent at term 0 by a joiner, or in a `c0` cluster, and so whether
   `SentMsgShape` can keep "term ≠ 0".
4. **B10**: whether `RInv` admits a joiner beside bootstrap founders.
5. **B12**: whether `index < 2^61` follows from a committed-log length law.
6. **Not checked**: F9-F11, F13 and F14, which are promises and not statements yet.
