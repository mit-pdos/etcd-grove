# Review of `notes/trace-check-design.md`, round 2 (revision 1, commit `d4e42ae90b`, branch `trace-check`)

Reviewer: an independent agent. It was read-only: nothing was checked in Lean and no build was run. It
was judged against `.claude/skills/spec/PRINCIPLES.md`, the Go harness
(`examples/raft/tracecheck/concurrent.go`), raft's Go at the traced revision (`.lake/raft-trace/`:
`node.go`, `rawnode.go`, `raft.go`, `bootstrap.go`, `state_trace.go`) and the Lean the document cites.
"Uncertain" marks what I could not check. The previous review's arguments were not reused; each point
below was re-derived.

## Summary

- **Revision 1's answers to round 1:**
  - F1 holds.
  - F2 holds, and the four call sites are right.
  - F3 holds for `node.Advance.spec` in both orders and for the traced spec when the run loop commits
    first. It does not hold as written for the traced spec when the driver sends first (A1 below).
- **The links the document leaves unargued:**
  - **L1** holds of the Go. The "derivation option" does not work against today's posts, so the new
    post conjunct is required (A2).
  - **L2 (ii)** holds and has a short Lean route (B3).
  - **G3** holds of the Go. The source list misses raft's automatic leave, and the ticket/registry route
    cannot see an empty `EntryConfChangeV2` (A3).
  - **L5** holds of the Go. `TrNoSnap`, a plain wand, cannot be derived from the storage contract's
    `={⊤}=∗` bound as it stands (A4).
- **New problems:**
  - `node.Advance` gets two proved triples, against a hard rule (A5).
  - The harness's `ConfChangeV2` arm is refuted using a raft-internal fact (A6).
- **Order of work:** the existing **closed** results stay `sorry`-free. Steps 1 and 2 cannot be landed
  separately, and step 1 re-opens proved traced theorems whose new obligations are L1 and L2 (B1).
- **Bugs:** none found in raft's or etcd's Go. Nothing for `issues/`/`nonissues/`.

---

## First tier: links that do not hold, or statements that are false or insufficient

### A1. §3.2 item 4, `SndPending`: `run` cannot "see `j ∈ dom M`"

**The statement.** "`run`, meeting it, holds `np`, so opens `rtkInv` (`pend = false`, so the deposited
count is `a`), sees `j ∈ dom M = [0, a)`, and puts the persistent 'key `j` deposited' fact
`monoNatLb γn.dep (j + 1)` in the `RcvCommit` answer."

**Why it fails.**
- In the `SndPending` case only the request is in `advInv`: `req` records the number `j`. The claim
  `ghostMapElem γn.rtk j (DFrac.own 1) ms` stays with the driver.
- `run` holds no fragment for key `j`, so opening `rtkInv` tells it nothing about `j`. It cannot give
  `monoNatLb dep (j+1)`.
- The driver cannot repair this later on its own. When it opens `rtkInv` after `RcvCommit`, `pend` may
  be `true` again, with pending key `a_now − 1`. The driver cannot rule out `j = a_now − 1` from the
  current state, because nothing persistent records that `j` was allocated before the rendezvous.
- The window is real. The driver receives its claim at the `readyc` commit, while `pend = true`
  (`node.go:435`, before `acceptReady`). It may call `Advance()` at once and enter `SndPending` before
  `run` deposits.

**What does hold.**
- The `RcvPending` case is right: `np` sits in `advDep`, so the sender sees `pend = false`, and its
  `j ∈ dom M` comes from its own element.
- `node.Advance.spec` (no claim) is right in both orders.
- The Go argument is right: `advancec` is armed only at `node.go:438`, after `acceptReady` (whose last
  statement is `traceReady`, `rawnode.go:437`), and `readyc` is re-armed only at `advancec == nil`
  (`node.go:354`).

**Caller affected.** `node.Advance.tracedSpec`, and therefore `app`.

**Fix (either works).**
- (a) Put the claim in the payload. In `SndPending`, `advanceP` carries an optional
  `ghostMapElem γn.rtk j 1 ms` (`none` for `node.Advance.spec`). `run` swaps it into `rtkInv` at the
  meeting and leaves `[∗list] readyTok` in `RcvCommit`, keyed by `req`'s `j`.
- (b) Add a persistent allocation witness. `rtkInv` gains `monoNatAuth γn.al a`, and
  `readyToksClaim` carries `monoNatLb γn.al (j+1)`. The driver puts that lower bound in its
  `SndPending` payload (it is persistent), so `run` learns `j + 1 ≤ a = count` and can give
  `monoNatLb dep (j+1)`.
- Add whichever is chosen to Probe B item 3.

### A2. L1 (§3.6, §9): the outbox's types are not derivable from `raft.Step.tracedTriple`'s post; the `OutTyStep` conjunct is required

**The statement.** "either a new conjunct `OutTyStep s s'` … or a derivation from `raft.Step.spec`'s
`LeaderNonpropResultC` and the role results if they pin the queued types."

**Verdict.** The type list of §3.6 holds of the Go. The second option fails.

**Why the derivation option fails.**
- `Hrefines` is `md.StepOut` (`StepGhostMode.lean:93`), a `StepC`/`StepR` closure. `StepC`
  (`Protocol/StepC.lean:387-660`) admits:
  - `sendFree`, which sends any `preVote`/`preVoteResp` at any time;
  - `sendApps`/`win` with `ReplOk = AppOk ∨ SnapOk` (`Model.lean:1596`), where `SnapOk`
    (`:1588`) has no compaction premise;
  - `readFwd`, and the `readAck`/`preadRespondAll` read responses.
- The role results' broadcasts are `ReplSends` (`Defs.lean:1559`). These exclude `.snap` only when
  `s.gh.ns = true`, and `NsCap` makes that impossible: the mode is off at raft's level
  (`raft__maybeSendAppend.lean:107-113`).
- `SimIdle`'s `P = pendAbs C outbox` (`TracedCap.lean:104`) filters out untraced types, and
  `recvTokOf` is vacuous on them (`TracedRecvTok.lean:29`). So neither statement can see a `MsgSnap`,
  `MsgTimeoutNow` or `MsgReadIndexResp` in the outbox.

**Where the information exists.** Inside the paths. `maybeSendAppend`'s traced branch already refutes
the snapshot fallback with `TrNoSnap` (`raft__maybeSendAppend.lean:121-124, 431-434`), so each path can
record what it queued.

**Callers affected.**
- `rnTrace` clause 1(b).
- `acceptReady`'s `TrSent` tokens, and through them every `stepIn` at a traced node.

**Fix.**
- Make `OutTyStep` a decided post conjunct of `raft.Step.tracedTriple`, `RawNode.Tick.tracedTriple`
  and the prop path, with its scope `lt = none ∧ ReadIdle`.
- Strike the "derivation" alternative.
- Count it as re-opening every path of `stepBundle_traced` (30c), with the queued type pinned per path.
- In §3.6's exclusion list, cite `TrNoSnap` at `maybeSendAppend` as the source of "no `MsgSnap`",
  rather than `ReplSends`.

### A3. G3 (§3.4 item 4, L2 (iii)): the source list misses the automatic leave, and the registry cannot see a filler

**The statement.** "entries enter a log only by `Bootstrap`, a leader's append of a proposal's entries
(…) and `becomeLeader`'s empty normal entry. Whether … the entry tickets `entTk` … can strengthen to
'normal past `boot`' is not checked."

**Verdict.** G3 holds of the Go (no conf entry past `|boot|` at a traced cluster), but not by the route
proposed.

**Why the route falls short.**
- **A fourth source is missing.** `appliedTo` (`raft.go:742-761`) steps an empty `ConfChangeV2`
  proposal at a leader whose configuration has `AutoLeave`. It enters the log as an
  `EntryConfChangeV2`, which `hasUnappliedConfChanges` counts (`raft.go:1028`).
- **The registry route cannot exclude it.** `Filler ty d := d = [] ∧ (ty = 0 ∨ ty = 2)`
  (`Protocol/Ghost.lean:1177`). An empty `EntryConfChangeV2` is a filler: `entTk` is `emp` and there is
  no deposit (`Ghost.lean:1359`). So "deposits at a traced cluster are of normal type" leaves it out.
  `ProposeConfChange` with an empty `ConfChangeV2` would make the same filler; it is refused.

**What G3 must be.** A joint invariant, proved by induction over the cluster's steps:
- (a) every non-filler entry past `|boot|` has type `EntryNormal`. Its sources are `node.Propose`
  (`propEntryM`, type 0, `ApiVocab.lean:335`), the gated `fwdP`, and `becomeLeader`;
  `ProposeConfChange` is refused;
- (b) no node's configuration is joint (`c.autoLeave = false`), since only the boot `AddNode`s
  (`ConfChange` V1, never joint) are ever applied.

Each half needs the other. (b) is also what §4's last row assumes (`MsgStorageApplyResp → … →
c.autoLeave = false`). The invariant is cluster-wide (followers' entries come from leaders), so it
belongs in the cluster ghost state, not in `ownRawNode`.

**Callers affected.** The leader exclusion at the `confc` arm, and §4's `autoLeave` premise.

**Fix.**
- Restate G3 as (a) and (b) together, and add `appliedTo` to the sources.
- Name where the cluster-wide invariant lives: the proposal registry for (a), and the node's `RInv`
  for (b) at every node.
- Keep 29n's leader line lemma as the fallback.

### A4. L5 (§5.2, §9): `TrNoSnap` cannot be obtained from a gated `storBnd` as written

**The statement.** "`TrNoSnap` from the storage's gated `storBnd` (L5)."

**Verdict.** It holds of the Go: the harness never compacts (`SnapshotEvery = 0`), and a fresh
`MemoryStorage` is compacted only at 0. It does not hold in the logic as stated.

**Why.**
- `TrNoSnap tr ls` is a plain persistent wand,
  `□ (⌜tr ≠ none⌝ -∗ (⌜prev.index ≠ 0⌝ ∨ storPast ls.storage 1) -∗ False)` (`TracedSend.lean:42`).
- The storage contract gives the bound only under an update: `"#Hbound" ∷ □ (∀ c, storCompacted st c
  ={⊤}=∗ Bnd c)` (`InvStorage.lean:282`).
- A gated `Bnd` therefore gives `storPast st 1 ⊢ |={⊤}=> False`, not `False`. No such
  persistent wand can be built at `setupNode`.
- The gate also has to go through raft's own copy of the bound (`raftBnd`, `storBnd_raftBnd`,
  `StartNode.lean:107`).

**Callers affected.**
- `rnTrace` (it holds `TrNoSnap`).
- The two refutations in `raft__maybeSendAppend.lean:121-124, 431-434`, both inside a WP, where a
  `|={⊤}=>` is usable.

**Fix (either works).**
- (a) Restate `TrNoSnap` as `□ (… -∗ |={⊤}=> False)`. Check that the two uses run at mask `⊤`. This
  re-opens `TrNoSnap`'s ~20 mentioning files, through `trNoSnap_traced` only.
- (b) Keep the wand pure, and have `setupNode` derive it from a pure fact raft owns. For example, the
  storage key's names could carry a persistent "no compaction past 0" that `storBnd_raftBnd` turns into
  `raftBnd`'s gate.

Either way, L5 costs the clients more than §9 counts (B2).

### A5. §3.1 (design rule) and §7: `node.Advance` gets two proved triples

**The statement.** "the traced statement is a separate, proved triple whose untraced reading is
today's; today's spec stays proved for every `γ`." So `node.Advance.spec` is re-opened and proved,
`node.Advance.tracedSpec` is proved again, and §7 marks both.

**Why it fails.** It breaks the hard rule "One spec per function; special cases are instances … a
variant … only as a corollary of the one proof, never a second proof". `Step` and `Ready` comply:
`node.Step.tracedSpec` is a corollary, and the untraced `isReadyChan_recvAu` drops the claim. `Advance`
does not.

**Fix.**
- Make `node.Advance.tracedSpec` the one proof, and `node.Advance.spec` its instance at `ms = []`.
- This needs a trivial claim, so define
  `readyToksClaim n γ N ms := ⌜ms = []⌝ ∨ (escrow element)` with
  `readyToksClaim_nil : ⊢ readyToksClaim n γ N []`. The left disjunct records `none` in `req`, exactly
  F3's claim-less driver.
- `node.Advance.spec`'s text and its clients are unchanged. The protocol is the same.

### A6. §2.3 `handleReady`: the `ConfChangeV2` arm is refuted by a fact the client does not see

**The statement.** "The `ConfChangeV2` arm: dead (the bootstrap entries are `EntryConfChange`, and no
other conf entry is committed, G3)."

**Why it fails.**
- G3 is raft-internal.
- What `handleReady` holds of `rd.CommittedEntries` (`readyGotT`'s `committedEntriesAt`,
  `isCommittedLogLb`) does not give entry types past `boot`.
- So this breaks "every premise has a source the client sees".

**Caller affected.** `handleReady`, and through it `app` and `RunConcurrent.spec`.

**Fix.**
- Handle the arm as kvreconf does (`kvreconf/Replica__applyEntry.lean`): `proto.Unmarshal` into a
  `ConfChangeV2` (the existing axiom `proto.UnmarshalConfChangeV2`, already among §6's fifteen),
  `confPolicy_decide`, then `node.ApplyConfChange.spec`.
- Cite the same decode fact kvreconf uses to exclude `Unmarshal`'s error, which would `panic`
  (`concurrent.go:322-324`).
- Alternatively, export G3 as a client-visible law at a traced cluster. That makes an internal
  invariant part of the API and is not recommended.

---

## The links the document asks about, checked

### F1 (thread bound): holds

- `init_adequate` fixes `threadBound = n + 2` and `receiptBound = n + 1` (per the document; the round-1
  review agrees).
- `n + 2 ≤ 2^31` gives `ThreadBoundLe tcGF (2^31)` (`Bounds.lean:62,66`), and
  `receiptBound + 3 = n + 4 ≤ 2^61`.
- In `netJoin.wp_Add`, the adder's token with `threadToks j` gives `j + 1 < threadBound ≤ 2^31`
  (`Threads.lean:433`).
- `WaitGroup.Add.spec` needs `0 ≤ sint.Z oldc + 1 < 2^31` (`Perennial/Spec/sync/WaitGroup__Add.lean`).
  The `oldc = 0` case needs `ownWaitGroupWaiters γ 0`, which an adder with `q > 0` finds in `njInv`'s
  left disjunct.
- The AU's mask is the wait group's namespace. `njInv` must therefore be in a sibling namespace and be
  opened before, and closed after, the `|={⊤,↑N.wg}=>`, as `tokJoin` does.
- Minor: `ThreadBoundLe.weaken (n + 2) (of_eq HT) Hn` does not elaborate, because `weaken`'s instance
  argument is instance-implicit. Write `haveI := ThreadBoundLe.of_eq HT; ThreadBoundLe.weaken (n+2) Hn`,
  or use the anonymous constructor the document also gives.

### F2 (`stepIn` gated on the token): holds

- There are exactly four `stepIn_intro` call sites outside the witness part:
  - `server/.../InvNet.lean:101` (`srvClusterOk`'s last conjunct, `SrvRaftLog.lean:768`);
  - `kvreconf/Cluster__step.lean:93`;
  - `kvdurable/Cluster__step.lean:90`;
  - `kv/deliver.lean:90`.
- kv's `kvPeerOk` (`kv/Cluster.lean:98-101`) lacks the fact, and `StartCluster.lean:296` has `%Htr0` in
  scope. The plan is right.
- `node.ProposeConfChange` unfolds `stepIn` itself (`node__ProposeConfChange.lean:119-122`), so its
  refusal premise is used.
- `node.Step.wp_proof` only passes `stepP` through (`node__Step.lean:166-173`).
- The other local senders reach `netP` through `netP_local`/`netP_hup` (`InvNodeChan.lean:563-636`).
  At a traced node, `ReportUnreachable`'s `MsgUnreachable` and `Campaign`'s `hupP` stay admissible, and
  the other four types need the refusals. §3.5 matches.
- `trTok_type` is read before `Step` (`concurrent.go:356`) and kills both `ReportSnapshot` calls.

### F3 (the escrow): holds except A1

The `RcvPending` order, the claim-less driver, and stale claims are right. In the `readyc` arm the
commit (key inserted, `pend := true`), `acceptReady`, and the deposit run in sequence with no other
`select` case in between (`node.go:435-441`). That is what the escrow needs.

### L2 step (ii): holds, with a shorter Lean route than "read against `undecFree`/`cam`" (see B3)

### G3: A3. L1: A2. L5: A4.

---

## Second tier: improvements

### B1. §9 "Order of work"

1. **Steps 1 and 2 must land together, or 2 before 1.**
   - Gating `netP`/`fwdP` in step 1 breaks `stepIn_intro`'s proof (`ApiImpl.stepIn_intro_impl`) and
     the local senders' proofs at a traced `γ`.
   - Today those specs hold for every `γ` with no trace premise, so they cannot be "re-proved by
     rewriting the gate". Their premises are step 2.
   - Step 1's text ("every proof … has `γ.raft.reTrace = none` (… or the client's fact)") does not
     cover them.
2. **`rnTrace`'s clauses in step 1 re-open proved traced theorems whose new obligations are not yet
   argued.**
   - 1(b) must be re-established by `raft.Step.traced`/`stepBundle_traced` (A2's `OutTyStep`, every
     path).
   - 1(c) must be re-established by `RawNode.Tick.traced` and the `MsgHup` path, via `HupCampaigns`'
     "no unapplied conf entry" (`SpecResults.lean:61`) and lemma (i).
   - Neither is under a closed result: the tracecheck collection's roots are `Results`/`etcdraft/Link`,
     and the raft collection reaches only untraced triples. But adding the clauses before L1 and
     lemma (i) are proved means `sorry`s in proved theorems, which changes `etc/tcb-baseline.txt`.
   - Sequence it: L1's per-path conjunct and lemma (i) first, then the clauses.
3. **The closed results do stay `sorry`-free.** I checked the shared both-mode specs on the untraced
   path:
   - `acceptReady.spec` takes `TrOutTy` from its own precondition's `rnTrace`, empties the outbox,
     and moves only `applying`;
   - `readyWithoutAccept.spec` only reads;
   - `node.Advance.spec` and `isReadyChan_recvAu` need only the driver's side of the escrow.
   None needs L1, L2 or L5.
4. **A8.1 re-opens proofs under a closed result.** `simInit`'s readers
   (`TraceSimRun`/`TraceSimSpecInv`/`MainSim`) sit under `tracecheck_Events_traceAccepts`, a root of
   `etc/tcb-collections/tracecheck.txt`. Say that A8.1 lands with all of them re-proved, never as a
   `sorry`. Uncertain: whether every reader is voter-only, as A8.1 argues.
5. **`node.run.gated_of`'s hypotheses are incomplete.** They are `hAdv` and `hCC` only. L1 (A2),
   lemmas (i)-(iii) (A3) and L5 (A4) are also needed. Each is either proved before step 3 or listed as
   a hypothesis.

### B2. L3 does not count L5's clients

`storBnd` is unfolded by clients:
- `kv/KVStorageInstance.lean:272-276` and `kvreconf/KvrStorageApi.lean:273-276` (`unfold memBnd storBnd
  … exact .rfl`);
- kvdurable's `KdStorageApi.lean` in the same way;
- the server's `NodeStart.lean:322` through `memStorage_isStorage`.

Gating `storBnd` breaks each of them, and each needs `Cluster.trace γ = none`. Export an introduction
law (`storBnd_intro_untraced`, and the harness's `c = 0` case) instead of the unfolds, which
PRINCIPLES' "a client does not unfold" already forbids. Then add these sites to L3's count.

### B3. L2 (ii): state the short route

- At the `confc` arm, `DynCCPre` gives `rs.capplied ≤ k` (`InvRawnode.lean:555-557`), and `confcP`
  gives `DynCCPreOp`'s `ca ≤ k` with `NoUndecConfIn` (`ApiVocab.lean:369-373`).
- Lemma (ii) is then `uint.nat s.logst.applied ≤ rs.capplied`, an invariant to establish at
  `RawNode.Advance`. Its post fixes `capplied := ca` (`advRS`, `InvRawnodeReady.lean:1344`; call at
  `node__run.lean:1158-1160`).
- Uncertain: whether that inequality is already stated in `ownRawNode`, or follows from `Hca`.
- Write the lemma in this form. The `undecFree`/`cam` reading in §3.4 is the long way round.

### B4. §2.3 `proto.ClonePb` at `pbMessage`: the import pulls in the server

`pbMessage` is in `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/PbMessage.lean`, which
publicly imports `…/rafthttp/Net` (lines 29-31). The tracecheck harness would depend on etcd's server
proof tree. Move `pbMessage` next to `InvPbMsg` (raft) or into proto's proof library, or record the
dependency as intended.

### B5. §2.2, `go c.app(r)`: say where `app`'s thread token comes from

`app` deposits a `threadTok` at each `c.net.Add(1)` and gets a fresh one at each `go`
(`wp_fork_tok_self`). Its first token, and the one it must hold at exit, come from `RunConcurrent`
forking it with `wp_fork_tok` and handing the fresh token in (`Lifting.lean:1964`). State it, so that
Probe A checks it.

### B6. §3.2 items 3-4: masks

- The `readyc` commit (the escrow insertion) and the `advancec` commits run inside channel AUs, which
  may be executed by the other party's thread.
- Name `rtkN` apart from the `readyc` and `advN` namespaces. State that `rtkInv` is opened inside the
  AU at `⊤ ∖ ↑(chan)`.

### B7. §3.3: be precise about which proved triples need only a frame

Clause 1(c) does not change in `acceptReady`, which moves `applying`, not `applied`, and keeps the role.
Clause 1(a) is established there by the `Ready` line. Saying so narrows "re-opened" for `acceptReady` to
the `readyTok` body and 1(b).

---

## Per statement

| Statement | Provable from its callees? True of the Go? | Sufficient for its callers? |
|---|---|---|
| §1 (settled) | yes, given `RunConcurrent.spec` | — |
| `tracecheck_adequate_of` | yes (F1 arithmetic checked); fix `weaken`'s call | yes |
| `RunConcurrent.spec` | yes, given A6, B5 | yes |
| `app` | yes, given A1 (traced `Advance` in the driver-first order) | yes |
| `handleReady` | **no as written (A6)**; yes as kvreconf does it | yes |
| `send` | yes | yes |
| `netJoin`, `join3` | yes (F1) | yes |
| `isReadyChan_recvAu.tracedSpec` | yes | yes |
| `node.Advance.tracedSpec` | **not in the `SndPending` order (A1)** | yes |
| `node.Advance.spec` | yes for every `γ`, but a second proof (A5) | yes |
| `node.Step.spec` / `.tracedSpec` / `stepIn_intro` / `trTok_type` | yes (F2) | yes |
| the five refusals | yes | yes |
| `node.run.gated_of` | depends on L1 (A2), G3 (A3), L5 (A4), A1; hypotheses incomplete (B1.5) | yes, given those |
| `rnTrace` 1(a) | yes (only `acceptReady` moves `delivered`, after the `Ready` line) | yes |
| `rnTrace` 1(b) | needs `OutTyStep` per path (A2) | yes |
| `rnTrace` 1(c) | yes: `HupCampaigns` plus lemma (i) | yes, with (ii) and G3 |
| §3.4 lemmas (i), (ii) | hold (B3) | — |
| §3.4 lemma (iii) / G3 | true of the Go; route insufficient (A3) | — |
| `TrNoSnap` at `setupNode` (L5) | **not derivable as stated (A4)** | — |
| A8 (`trCapB_bootDone`, end law) | yes; A8.1 re-opens closed-path proofs (B1.4) | yes |
| §5.2 traced constructors | positions match `raft.go`/`bootstrap.go` | yes |

## Ranking by need of revision

1. §3.2 item 4 / §3.1, the escrow and `node.Advance` (A1, A5): one gap, one hard rule.
2. §3.6 / L1 (A2): a decided post conjunct, re-opening 30c.
3. §3.4 / G3 (A3) and §5.2 / L5 (A4): each needs a restatement before the `confc` and `setupNode`
   proofs.
4. §2.3 `handleReady` (A6).
5. §9's order of work and L3 (B1, B2).
6. B3-B7.

No bug found in raft's or etcd's Go code. Nothing for `issues/`/`nonissues/`.
