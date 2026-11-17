# Review of `notes/trace-check-design.md`, round 1 (commit `77bff94368`, branch `trace-check`)

Reviewer: an independent agent (read-only; nothing checked in Lean, no build run). Judged against
`.claude/skills/spec/PRINCIPLES.md`, the Go harness (`examples/raft/tracecheck/concurrent.go`,
`main.go`), raft's Go at the translated revision (`.lake/raft-trace/`: `node.go`, `rawnode.go`,
`raft.go`, `bootstrap.go`, `state_trace.go`, `util.go`) and the cited Lean statements. "Uncertain"
marks what I could not check.

## Summary

The chain's shape is right, and the harness-level ordering argument (§2.3) is correct against the Go.
Three links do not hold as written:

- **F1.** The closed statements of §1 have to change. The `netJoin` idiom needs
  `threadBound GF ≤ 2^31`, and the adequacy theorem fixes `threadBound GF = n + 2`. So
  `n + 4 ≤ 2^61` cannot stay.
- **F2.** `node.Step.spec` cannot be the "untraced instance" of `node.Step.tracedSpec`. It also
  becomes false at a traced cluster unless its precondition (or `stepIn_intro`) gains something.
- **F3.** `node.Advance.spec` (no claim) cannot be proved at a traced node under the "both `rtk`
  halves back" protocol.

F2 and F3 together contradict the claim that "no existing client changes" outside §3.5. The rest are
second-tier: inaccuracies, a duplicated lemma, sealing and naming, sequencing.

---

## First tier: links that do not hold

### F1. §1.2/§1.3 and §6 (Q34, L4): the step bound must change, and the corollary needs a thread bound

**Statement.** §6 makes `isNetJoin` carry `⌜threadBound GF ≤ 2^31⌝`. L4 says: "from the
`ThreadBoundLe` instance … Otherwise it is a premise of `RunConcurrent.spec` (not of the closed
theorem), discharged in `tracecheck_adequate_of` by the adequacy's choice of the bound", and
"none touches §1". §1.2 says the step bound `n + 4 ≤ 2^61` is unchanged "word for word".

**Why it fails.**
- `tracecheck_adequate_of` uses etcdstart's `init_adequate`
  (`Proof/.../examples/lib/etcdstart/Adequacy.lean:111-119`). That theorem passes
  `receiptBound GF = n + 1` and `threadBound GF = n + 2` (`goose_adequacy (n + 1) (n + 2)`).
  Tracecheck's proof ignores the second today (`Adequacy.lean:114`, `fun hG HN _ => …`).
- With `n + 4 ≤ 2^61`, `threadBound GF ≤ 2^31` is not derivable. No `ThreadBoundLe GF (2^31)`
  instance exists at `tcGF` for every admitted `n`.
- This is not a proof artifact. `sync.WaitGroup.Add.spec` requires the new counter to be below
  `2^31` (Perennial `Spec/sync/WaitGroup__Add.lean`), and Go's `WaitGroup` panics on a wrapped
  counter. `send` runs `c.net.Add(1)` once per message (`concurrent.go:351`), with no bound but the
  live goroutines.
- So any proof of `RunConcurrent` needs fewer than about `2^31` threads. That is the closed
  theorem's `n`, the same mechanism as putget's `Hn : n + 2 ≤ 2^28`
  (`putget/Results.lean`, `Adequacy.lean:137`).

**Callers affected.** `raft_tracecheck_safe` (§1.2: its `Hn` changes) and `raft_tracecheck_accepts`
(§1.3: it needs `[ThreadBoundLe GF (2^31)]` or `threadBound GF ≤ 2^31` beside `Hrb`, because
`RunConcurrent.spec` will take it). Both are the user's section, so the change must go to the user.

**Fix.**
- §1.2: `(Hn : n + 2 ≤ 2 ^ 31)`. It implies `n + 4 ≤ 2^61`. Derive both `Hbound` and the thread
  bound in `tracecheck_adequate_of` from `HN`/`HT`, as putget does.
- §1.3: add `[ThreadBoundLe GF (2 ^ 31)]`.
- `RunConcurrent.spec`: take `[ThreadBoundLe GF (2 ^ 31)]`, which follows the bounds plan better than
  a raw premise.
- Delete L4's "none touches §1", and list the change in §9's "The user's".
- Explain it to the user in plain terms: the harness starts one goroutine per message, and Go's
  WaitGroup panics past `2^31` of them, so the theorem covers runs of fewer than `2^31` steps.

### F2. §3.1 (`node.Step`, "text unchanged … the current `node.X.spec` is derived from `node.X.tracedSpec`") and §3.2 item 5

**Statements.** `node.Step.spec` (`Spec/go_etcd_io/raft/v3/node__Step.lean`) is `∀ γ …,
{{ … isNode n γ N id ∗ nodeCtx ctx cd ∗ stepIn γ N id ml }} n.Step(ctx, ml) {{ … }}`. It has no
trace premise. `stepIn_intro` (`InvNode.lean:449`) builds `stepIn` from `sentMsg ∗ msgPtsC ∗
msgCredits ∗ snapLocalMsg`, with no token and no trace premise.

**Why it fails.**
1. *The direction is wrong.*
   - `stepIn` is a sealed wand (`InvApi.lean:3432`:
     `⌜ml ≠ null⌝ ∗ ∀ γn, ⌜NodeOk γ γn⌝ -∗ ⧗ 1 ={⊤}=∗ stepP γn id ml`).
   - `node.Step.tracedSpec`'s precondition holds the components. Those components imply `stepIn`
     (by `stepIn_intro`), but `stepIn` does not imply them.
   - So `node.Step.spec` cannot be obtained from `node.Step.tracedSpec`, even at `trace = none`.
     "One proof per function" fails for `Step` as designed.
2. *It becomes false at a traced cluster.*
   - `StartNode.tracedSpec` gives `isNode` at a traced `γ` (`TracedNodeApi.lean:115`).
   - At such a γ, `stepIn_intro` followed by `node.Step.spec` delivers a sent message to the traced
     `run` without its `recvTokOf`.
   - The redesigned traced `netP` (§3.2 item 5) requires that token, so `node.Step.wp_proof` cannot
     be re-proved for all `γ`.
   - It would let a client deliver a message twice, which the trace's bag forbids. That is the reason
     the token exists.

**Callers affected.** Every client of `node.Step.spec` or `stepIn_intro`: 13 and 17 files, including
etcd's server (`NodeApiLink`, `NodeBridge`, `NewServer`, `NodeStart`), kv, kvreconf, kvdurable, and
raft's own `node.ProposeConfChange`.

**Fix (recommended).**
- Keep **one** proved spec, `node.Step.spec`, with its text unchanged.
- Gate `stepIn`'s sealed body: `stepP`'s traced `netP`/`fwdP` need the token and `TrSent`.
- Give `stepIn_intro` the premise `trTok γ st`. Untraced clients discharge it with
  `trTok_untraced γ st h`, where `h : Cluster.trace γ = none` comes from `cluster_alloc`
  (`InvNodeRule.lean:214`).
- `node.Step.tracedSpec` then becomes a corollary (`stepIn_intro` + `node.Step.spec`), and the
  harness is unchanged.
- The cost is the threading of `h` to `stepIn_intro`'s callers. Count it with
  `etc/importers.py --uses stepIn_intro` and add it to L3.
- The alternative, `Cluster.trace γ = none →` on `node.Step.spec`, costs the same and leaves two
  statements to keep in step.

### F3. §3.1 (`node.Advance`) and §3.2 item 4: `node.Advance.spec` at a traced node

**Statement.** §3.2.4: "run ends the rendezvous with both `rtk` halves, ready for the next `Ready`."
§3.1: `node.Advance.spec` is "the untraced instance" of `node.Advance.tracedSpec`, and no client
changes.

**Why it fails.**
- `node.Advance.spec` (`Spec/.../node__Advance.lean`) has no trace premise, and its precondition has
  no `readyToksClaim`.
- At a traced node a driver using it brings no claim half. `run` therefore cannot recover its second
  `rtk` half at the rendezvous. Under the stated protocol it cannot update `rtk` at the next
  `readyc` send, so `node.run`'s proof does not go through for that driver.
- Deriving `node.Advance.spec` from the traced spec needs `readyToksClaim_untraced`, which needs
  `Cluster.trace γ = none`.
- So either `node.Advance.spec` gains that premise (15 files: every driver, etcd's server and the
  three kv examples), contrary to "no existing client changes", or the protocol changes.

**Fix (recommended: change the protocol, not the clients).**
- Allocate the claim **per `Ready`**. At the `readyc` commit, `run` allocates a fresh `dghostVar γx`
  at `ms`, keeps one half, and gives `readyToksClaim` (`∃ γx`, the other half) in `readyP`.
- At the rendezvous, `run` deposits `[∗list] q ∈ ms, readyTok …` with its half under `γx`. In
  `SndPending` the deposit sits in `RcvCommit`, keyed by `γx` rather than by `req`.
- A driver holding the claim takes the tokens by agreement. A driver without it (`node.Advance.spec`)
  leaves them, and they are dropped at the transition to `Idle` (the logic is affine).
- `run` needs nothing back, so `node.Advance.spec` stays provable for every `γ` with no premise, and
  `node.Advance.tracedSpec` stays as stated.
- If the "both halves back" design is kept instead, add `Cluster.trace γ = none →` to
  `node.Advance.spec` and count it in L3.

---

## Second tier: improvements and inaccuracies

### S1. §2.2, the conf-change proposer row: `time.Now` *is* called

- `concurrent.go:206` computes `deadline := time.Now().Add(time.Duration(cfg.Proposals) * cfg.ProposeGap)`
  before the loop. Only the second `time.Now()` (`:207`) and `Status` are short-circuited.
- The proof needs `time.Now.spec` and `time.Time.Add.spec`. Both exist in Perennial.
  `time.Now.wp_proof` is a Perennial **axiom** (`Perennial/Proof/time/Now.lean:24`).
- Related, in §1/§6: the tracecheck collection's baseline (`etc/tcb-collections/tracecheck.txt`,
  no axiom today) will gain every existing axiom on the path once `RunConcurrent` is proved, not
  only `strconv.Itoa`: kvreconf's 15 (`proto.*`, `DescribeConfChange`, `fmt.Errorf`, …) and
  `time.Now`. None is new to the trust base, so "no axiom is added" still holds. But §6's framing
  ("why `strconv.Itoa` … joins this collection's report") should say "every axiom of the node API's
  path joins it", with the list.

### S2. A8.2: `bootEvAt_pos_unique` already exists

`bootEvAt_unique` (`TraceSimBootSeg.lean:218`) is exactly this statement. Use it, and do not add a
copy.

### S3. A8.3/A8.4: sealing of `startDone` against the end law's argument

- A8.3 says `StartNode.tracedSpec`'s post is `startDone γ cv.ID'`, "sealed over `bootDone`".
- `Cluster.traceSim_bootEnd` takes `□ [∗list] i ∈ vs, bootDone tn i` at the harness's `tn`.
- The harness would then unfold `startDone` (a match on `Cluster.trace γ`) and apply
  `traceDir_agree` itself, which PRINCIPLES' "a client does not unfold" forbids.
- **Fix:** state the end law over what the client holds:
  `Cluster.trace γ = some γd → traceDir γd tn ∗ □ [∗list] i ∈ vs, startDone γ i ∗ … ={E}=∗ …`.
  Or export one elimination law `startDone_bootDone`.
- Likewise, `HarnessEnd.lean`'s `BootEnd` should then be stated over `startDone`.

### S4. §5.2: `Λ2`/`Λ_end` and the capability's configuration

- `Λ : Option TraceEv → Prop` does not see the `C` bound inside `trCapB`.
  `Λ2 o := ∃ x, o = some x ∧ BootEvAt C id 2 x` must be written at the caller's `vs`
  (`startTraceC` gives `tn.voters = vs`). `trCapB_bootDone`'s `hΛ` then holds with `C = vs`.
- `newRaft.tracedSpec`'s capability must be at the voters' configuration `cC`, not the node's
  configuration `c`, which is empty in positions 0-2. `raft.becomeFollower.traced` keeps `cC` and `c`
  apart for exactly this reason (`TracedHooks.lean:417-421`, `hcC : b = true → cC = c`). Write the
  post with `cC`.

### S5. §3.3/§7: `acceptReady.spec` is listed as proved and unchanged, but §3.6 changes its post

Its tokens become `⌜TrSent q.st⌝ ∗ recvTokOf …`. So `readyTok`'s body or `acceptReady`'s post
changes, and its proof re-opens. Mark it ★ in §7.

More generally, every new clause added to `rnTrace` (§3.2 item 1) re-opens every proved traced triple
that re-establishes `ownRawNode`:
- `RawNode.Tick.traced`;
- `acceptReady` and `readyWithoutAccept`;
- `wp_rn_raft_Step_prop_traced`;
- the `raft.Step.traced` assembly.

§7 marks all of these "proved". Either list the re-openings, or keep the clauses that only `run`
reads in `run`'s own invariants:
- the flag-to-delivery clause could sit in `runMid`, if `rnTrace` exports the flag;
- `role ≠ follower → applied ≥ |boot|` is needed only at `confc`.

### S6. §3.4: `AccIdle` has no leader clause

`AccIdle` (`TraceSimMatch.lean:4437`) says:
- not joint;
- `commit ≤ |log|`;
- no pending configuration change;
- the last committed configuration entry is the current configuration.

It says nothing about the role. The leader case is a real obstacle for another reason: at a leader,
`switchToConfig` (`raft.go:2015-2028`) also logs the `Commit` line through `maybeCommit` and sends
through `bcastAppend`/`maybeSendAppend`. `trCapB_hookGate_applyCC` covers neither, and needs the phase
`SimIdle` (`TracedApplyCC.lean:174`). Restate the obstacle; the conclusion (exclude the leader case)
stands.

### S7. §3.4/L2: the exclusion argument is right in Go; state its two lemmas

Checked against the Go:
- `hup` refuses while `hasUnappliedConfChanges()` (`raft.go:1001`), which reads `raftLog.applied`.
- `applied` rises only at `Advance` (`MsgStorageApplyResp`).
- The harness applies a `Ready`'s conf entries before its `Advance` (`concurrent.go:274-275`).

Two things are missing:
- Turning `¬ hasUnappliedConfChanges` into `applied ≥ |γ.reBoot|` also needs `committed ≥ |boot|`
  and "the log's entries `1..|boot|` are the bootstrap conf entries". These come from the bootstrap
  log prefix of the committed log. Name that fact.
- State the `confc`-arm lemma explicitly: an entry `node.ApplyConfChange.spec` admits is undecided,
  and with A1 at `Advance`, that gives `index > raftLog.applied`. It is the only unargued step.

### S8. §1.1: a name clash

`tracecheck.BootFacts boot` (new, over `BootLog`) sits next to `TraceCheck.BootFacts C L`
(`MainSim.lean`, over `newTrace`), and A8.4 refers to "`BootFacts vs L`'s body". Rename the new one,
for example to `tracecheck.BootLogFacts`.

### S9. Sequencing against the acceptance test (§3.2, §7)

Two steps would put a `sorry` under every existing raft client result until all of `run`'s arms are
proved. That is the hazard `TracedApiDraft.lean`'s header records:
- dropping `node.run.spec`'s `γ.raft.reTrace = none`, while the traced `RawNode.Advance` and
  `raft.applyConfChange` are ★;
- deriving `node.Advance.spec` from a `sorry`-backed traced spec.

Say in §8/§9 that the one-spec swap happens only once every arm is proved, and that until then the
traced arms are hypotheses of a separate theorem.

### S10. L3's cost

With F2 and F3 as written, the refusal premise also lands on `Step` (or `stepIn_intro`) and on
`Advance`, not only on the five §3.5 specs. Etcd's server threads it through `raftNode`, the read
loop and the transport.

Two smaller points:
- `ReportSnapshot` needs no premise for the harness: its call is dead by `trTok_type`.
- The premise on `ProposeConfChange` is redundant if F2's fix is taken: its `n.Step` already needs
  the token's `TrSent`, which excludes a conf-change `MsgProp`. Keep it only as a documentation
  premise, or drop it.

### S11. A8.2's list of `simInv` re-establishers is incomplete

`trCapB_perm` (`TracedFamilies.lean:188-208`) also re-establishes `simInv`, with `L` unchanged, so
the new `Dn` clause carries trivially. Add it to the list, with `Cluster.traceSimInv_alloc` (the
empty `Dn`) and `TraceSimEnd`'s laws.

### S12. Smaller points

- **§2.2/§2.3 `Propose`.**
  - `node.Propose.spec` needs `AU <{ ∃∃ ops, ownCommittedOps γ ops }>` at `⊤ \ ↑N` (`γ.dup = false`).
  - The harness must keep `harness_alloc`'s `ownCommittedOps γ boot` in an invariant of its own,
    outside `N`, to supply the AU per call. Name that invariant in §2.2.
  - Likewise, `ownConfDecisions γ ∅` is shared by the three `app`s, which apply the same three
    entries. It needs kvreconf's shared policy invariant, not one app's ownership. Uncertain:
    I did not check kvreconf's form.
- **§2.3 `handleReady`.** The snapshot branch is cited as dead "by `TrNoSnap`". `TrNoSnap`
  (`TracedSend.lean:42`) is raft-internal and not client-visible. The harness must refute it from
  what it holds: `ownSnapsMade γ []` and `readyGot`'s loan. Cite that instead (uncertain which
  `readyGot` conjunct gives it).
- **§3.2 item 2.** `γ.rtk` must be a field of `NodeNames` (per node, allocated in
  `newNode`/`setupNode`), not of the cluster. Say so. It is moot if F3's per-`Ready` allocation is
  taken.
- **`readyToksClaim`.** It is a resource every traced driver threads from `Ready` to `Advance`, of
  the kind PRINCIPLES' "no identification handles" warns about. It carries content (which messages
  the tokens are for), so it is a defensible departure. Say so in its docstring, with the alternative
  considered: keeping `ms` inside the sealed `nodeDriver`, which needs a field in the client-visible
  `NodeDriverState`.
- **A8.1.** "`bootInit C` is `simInit C` by definition" is propositional (function extensionality
  and an `if` over the same test), not definitional. Keep `bootInit_eq` as a lemma.

---

## Per statement (§7's rows)

| Statement | Provable from its callees? True of the Go? | Sufficient for its callers? |
|---|---|---|
| `raft_tracecheck_safe` | yes, once `Hn` matches the thread bound (F1) | statement must change (F1) |
| `raft_tracecheck_accepts` | yes, plus a thread-bound instance (F1); `runOver c` is exactly `tracecheck_Events_traceAccepts`'s pre | yes |
| `Main.spec`/`tcMainSpec` | yes (threading only); `tcMainSpec` must become `∀ hG, (⊢ premises boot) → Main.spec`, as putget | yes |
| `RunConcurrent.spec` | yes, given F1's bound, S1's `time.Now`, S12's AU invariant | yes |
| `app` | yes. The order claim is correct: the tokens are minted in `acceptReady` (`rawnode.go:437`) before the `advancec` arm is armed (`node.go:435-446`), and `send` follows `Advance` (`concurrent.go:275-284`) | yes |
| `handleReady` | yes (S12) | yes |
| `send` | yes. `trTok_type` is read before `Step` (`concurrent.go:356`), and covers both `ReportSnapshot` branches | yes |
| `netJoin`, `join3` | yes against `WaitGroup.Add.spec`'s `< 2^31` and `oldc = 0` waiters case, given F1 | yes |
| `StartNode.tracedSpec` / `.gatedSpec` | yes (A8.3), with S3's sealing | yes, with S3 |
| `newRaft`/`Bootstrap`/`setupNode` traced | positions match the Go (`raft.go:469,479,487`, `bootstrap.go`) | S4 |
| `trCapB_bootDone` | the argument holds. Uses `simRun_parse` and `booted_str`'s converse (all events parse), and `bootEvAt_unique` (S2) | yes |
| `Cluster.traceSim_bootEnd` | yes | yes, with S3 |
| `isReadyChan_recvAu.tracedSpec` (revised) | yes; the untraced law follows by weakening | yes |
| `node.Advance.tracedSpec` | yes | the untraced instance does not follow without a premise (F3) |
| `node.Step.tracedSpec` | yes | `node.Step.spec` does not follow from it and is false at a traced γ (F2) |
| the five refused specs | yes | S10 |
| `node.run.spec` (one spec) | depends on the ★ arms, L1, L2 (S5-S7, S9) | yes, given F2/F3 |
| `rnTrace`'s new clauses | L1 as flagged; the re-openings are under-counted (S5) | — |
| `TrSent`, G1/G2 | consistent with `state_trace.go`'s traced types and `node.go`'s `MsgProp`→`propc` routing. A forwarded proposal's non-emptiness (`stepLeader` panics on an empty `MsgProp`, `raft.go:1314`) comes from `fwdP`'s `isMessage` (`isMessage_propose_pure`, `InvNodeRun.lean:895`) | yes |

**Good:**
- The §2.3 ordering check is right.
- The §3.5 list is complete against every sender on `recvc`/`propc` in `node.go`.
- The `MsgUnreachable` guard: `IsResponseMsg` includes it (`util.go:47`), and its `From` is always a
  voter, so it is never filtered.
- The §3.2 bounds arithmetic holds (`traceNumBound = 2^61`, `readyFits`).
- Q35 is right: `NewTicker` panics at `d ≤ 0`.
- A8's position-uniqueness and `bootDone_snoc` arguments hold.
- §1.1 follows putget's D19r pattern, and `harness_alloc` already consumes `bootMarshal`.

**§1's meaning.** "No panic, no stuck thread, `#()`" together with `Main`'s panic unless `TLCOK`
says that every *finished* run's trace passes the Go checker. It is partial correctness: a harness
deadlock is not excluded, which is normal for safety. The corollary (§1.3) states the acceptance
directly. Both rest on `Hprem` being true of the real `proto.Marshal`: deterministic bytes for these
three `ConfChange`s.

Beyond F1, nothing in them is weaker or stronger than it should be. The form at `defaultCConfig` is
reasonable for a closed corollary; option (b) would be the general one, with (a) its instance.

## Ranking by need of revision

1. §1.2/§1.3 and §6's `netJoin`/L4 (F1): a user-visible statement change.
2. §3.1/§3.2 `node.Step` and `stepIn` (F2).
3. §3.1/§3.2.4 `node.Advance` and the `rtk` protocol (F3).
4. §3.2/§3.6/§7 `rnTrace`'s clauses and the re-opened proved triples (S5, S9).
5. A8.3/A8.4 sealing (S3), §5.2 `Λ`/`cC` (S4).
6. §2.2's table (S1, S12), §3.4's wording and lemmas (S6, S7), naming and duplicates (S2, S8, S11).

No bug found in raft's or etcd's Go code. The harness's unbounded `c.net.Add(1)` can overflow
`WaitGroup`'s counter only past `2^31` live goroutines. It is this repository's own example code, not
an upstream bug, so no `issues/`/`nonissues/` entry; F1 is where it is recorded.
