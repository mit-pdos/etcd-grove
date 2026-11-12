# Review: step 5's statements (`TracedBootSpecs.lean`), round 1

Reviewed at `d70152f956` (branch `trace-check-s5`), read only. The file typechecks:
`etc/lean-check.py -a` reports 0 errors. Nothing imports it yet. I checked each claim against the Go
source in `.lake/raft-trace` and against the proved laws the statements cite. A claim I could not
check is marked *uncertain*.

**Summary.** No first-tier finding. Every statement is true of the Go code. Every premise has a source
at its caller, and the design's tables are right, including the order of `isStorage_trNoCut` before
`storBnd_raftBnd`. The untraced instances are honest. §1 does not change. Points (1)-(5) of the brief
are answered below. The second-tier findings are:
- S1: `2 ≤ vs.length` goes into the client API, and it is a scope restriction rather than a need of
  the code.
- S2: `tracedSpec_of_gatedSpec` has to split on the mode.
- S3: `trCapStart` is a copy of `trCapB`'s body.
- S4: three documents still say `bootDone` is minted at `setupNode`.
- Three nits.

## Answers to the brief's points

**(1) The gate form of `switchToConfig`/`applyConfChange` is right. Step 4's `tracedSpec` still follows,
but the derivation must split on the mode (S2).**

The gate form is true of the code:
- `switchToConfig` calls `traceConfChangeEvent(cfg, r)` first (`raft.go:1981`). It runs before
  `r.trk.Config` is overwritten, so the event's `conf` is the old configuration `c0` and its `cc.NewConf`
  is `cfg.Voters[0]`, the new one (`state_trace.go:272-285`). That is `CCEvOf id s c0 c`.
- At a follower, the rest of `switchToConfig` takes no traced branch. The step-down at `:1994` and the
  commit and broadcast at `:2011` are leader-only. So the one line is the hook's, and the premise
  `s.gh.tr ≠ none → s.role = .follower` (`TracedBootSpecs.lean:299`) is enough.
- `applyConfChange` runs only the `Changer` before `switchToConfig` (`raft.go:1953-1971`), and the
  `Changer` does not trace. So `HookGate s.gh.tr r (CCEvOf id s c c'.cfg) Q` (`:351`) names the right
  state and the right pair of configurations.
- Untraced, `TraceFire none tl _ Q` is `⌜TraceLoggerOk tl⌝ ∗ Q` (`TracedCap.lean:519-523`). That is the
  old `%Htlok` together with `Q`, so `appliedSnap`'s call is `Q := emp`. The binder `γ` was only there for
  the capability and can go.

`tracedSpec_of_gatedSpec` (to write) can be proved, as follows:
- The gate comes from `ownRaftPhysC_traceLoggerG` (`RaftReadLend.lean:187`), which gives the field and
  `s.gh.tr = none → TraceLoggerOk`, followed by `trCapB_hookGate_applyCC` (`TracedApplyCC.lean:166`).
- `hboot`, `hcl` and `hbnd` are `tracedSpec`'s traced premises (`TracedRunSpecs.lean:182-187`).
- The post's `Q` is the capability at `c`, idle at `s`. It moves to `c'.cfg = c` and `s'` through
  `ApplyCCOkC`'s follower arm: `SwitchOkC`'s non-leader branch gives `s' = {s with progress, prvals,
  isLearner}`, so `toPState s = toPState s'` and `simIdle_congr` applies. This is exactly the argument
  `raft__switchToConfig.lean:70-78` already makes.

See S2 for the case split.

**(2) Minting `bootDone` at `Bootstrap`'s end is sound, and it is the only point where the law applies.**
- `trCapB_bootDone.statement` (`TracedCap.lean:1295-1301`) needs `Λ o → BootEvAt C id (|C| + 3) o`.
- After the last per-peer `applyConfChange`, `Λ = bootAt ps id (|ps| + 3)` and `bootPhase` fixes
  `C = ps`.
- Position `|ps| + 3` is `(|ps| - 1) + 4`, the last `k + 4` position allowed (`k < C.length`,
  `TraceSimGhost.lean:279`).
- After `Bootstrap` returns, `ownRawNode`'s `rnTrace` holds the capability at the default `Λ`
  (`InvRawnode.lean:2705-2706`). So `setupNode` can no longer apply the law.
- Nothing between `Bootstrap`'s return and the minted witness's use logs: `setupNode` only runs
  `newNode(rn)` (`node.go:263`), and `run` is forked afterwards (`:273`).
- The witness is persistent. Later lines keep `Dn`'s clause through `bootDone_snoc`, which A8.2 already
  proved for every fire law.
- `bootDoneG (raftNames γ).reTrace id` equals `startDoneB γ id` once both sealed names are unfolded:
  `Cluster.trace γ = γ.raft.reTrace` (`InvNode.lean:84`) and `Cluster.raftNames γ = ApiImpl.Cluster.raft
  γ` (`TracedApiDraft.lean:51`).

The docs still say "at the end of `setupNode`": S4.

**(3) `TrNoSnap`'s source through the `InitialState` answer is sound and necessary.**
- `isStorage_trNoCut` is true. `isStorageP`'s `#Hbound` is `storCompacted st c ={⊤}=∗ Bnd c`
  (`InvStorage.lean:282`). At a traced cluster, `storBnd` is `⌜c = 0⌝` (`InvNodeRule.lean:648-651`), so
  `storPast st 1` (some `n ≥ 1` compacted) gives `|={⊤}=> False`.
- The order works. In `StartNode`, `isStorage γ K st` is persistent, so a copy can be turned into
  `trNoCut` before `storBnd_raftBnd` repacks it as `isStorageD` (`StartNode.lean:472-483`).
- `trNoCut_trNoSnap` is immediate. `TrNoSnap`'s first disjunct is refuted by `prev.index = 0`, which
  holds at `Bootstrap`'s fresh log (`rawNodeFreshT`'s `%Hlog`), and the second by `trNoCut`
  (`TracedSend.lean:45`).
- The contract exists only from `InitialState`'s answer on, and `R'` is abstract to `setupNode`. So the
  boot bundle has to name it: the design's argument holds. Proving the law needs `storBnd` (sealed in
  `InvNodeRule`) and `Cluster.raftNames` (sealed in `TracedApiDraft`). It belongs in a raft-internal
  module that `import all`s both, which the sealing rule allows.

**(4) `2 ≤ vs.length` is sufficient but stricter than needed, and it reaches the client API (S1).**
- Sufficient: `readyFits γ N` is `receiptBound + bootLen ≤ 2^61` (`InvNode.lean:221`), and
  `bootLen = |reBoot| = |vs|` by `BootLogOk`. So `|vs| ≥ 2` gives `receiptBound + 2 ≤ traceNumBound = 2^61`
  (`Model.lean:227`). It also gives `traceReadyFits` (`TraceFits.lean:32`) at
  `γn.raft = γ.raft` (`NodeOk`, `InvApi.lean:1649`).
- The weaker form S1 offered is a disjunction of two specs, which the principles reject. A better form
  is in S1 below.

**(5) `applyConfChange` has `CfgSizeOk c0`.**
- At `applyConfChange`, `c0` is the struct's configuration `c`. The struct is opened at its tracker
  (`ownRaftPhysCV_reconfigCore`), and `ownTrackerC_pure`'s `Hdom` and `Hsize` give `CfgSizeOk c`. This is
  exactly how `ownRaftPhysC_readT` derives it (`RaftReadLend.lean:216-233`, the `have Hsz` at `:227`).
- Placing it inside `trOwn` (`:312`) is right: `appliedSnap` (untraced) need not prove it.
- `switchToConfig` cannot derive it itself. It holds only `Hold`'s maps of `c0`, not `c0`'s tracker
  bound.

## Per target

### `raft.switchToConfig.gatedSpec` (`:290-324`)

**Good:**
- The step-4 statement is reduced to what the code needs: a follower, the fire and the old maps.
- `becomeFollower.spec`'s shape is reused.
- Dropping `γ` removes the `raftNames0` stand-in from `appliedSnap`.

**Findings:** none. The step-4 `c = c0` is no longer needed: the capability arithmetic moves to the
caller's gate, and the read view's size bound comes in by (5).

### `raft.applyConfChange.gatedSpec` (`:336-360`)

**Good:**
- One proof serves both modes.
- Both today's untraced spec and step 4's `tracedSpec` survive as corollaries, which "One spec per
  function" allows. So the 4 untraced callers and `run`'s `confc` arm are untouched.

**The `Bootstrap` instance checks.** For peer `k`, `trCapB_hookGate_ccBoot` (`TracedNodeBoot.lean:396`)
needs:
- `hBN`: the event at position `k + 4` (`TraceSimGhost.lean:279-282`) must have term `1`, vote `0`,
  commit `|ps|` and log size `|ps|`, with `newconf` a permutation of `ps.take (k+1)`. These hold because
  `Bootstrap` calls `becomeFollower(1, None)`, appends `|ps|` entries and sets `committed = len(ents)`
  before the loop (`bootstrap.go:52-80`). `C = vs = ps` in peer order, so `take` matches the order in
  which the loop adds peers.
- `hOk`: follows from `|ps| < 2^40`.

**Findings:**
- **S2 (second tier; proof plan): `tracedSpec_of_gatedSpec` must split on the mode.**
  `trCapB_hookGate_applyCC`'s `hcn : |elements cn.incoming| ≤ |elements c.incoming|`
  (`TracedApplyCC.lean:171`) is not gated on the mode. `tracedSpec` constrains `c'.cfg = c` only when
  traced (`TracedRunSpecs.lean:182-183`), so untraced `hcn` can fail.
  - Restatement of the plan: "traced, `trCapB_hookGate_applyCC` at `cn := c'.cfg = c`; untraced,
    `hookGate_none` (`TracedCap.lean:724`) with `Q := emp`, and `trCapB none` is `emp`."
  - The design's table row for `run`'s `confc` (`notes/trace-check-design.md`, step-5 section) should
    say so.

### `newRaft.gatedSpec` (`:388-460`), `NewRawNode.gatedSpec` (`:467-517`)

**Good:**
- Positions 0-2 match the code:
  - `traceInitState(r)` runs right after the struct literal (`raft.go:469`). At that point
    `Term = 0` (not yet loaded), `committed = prev.index = 0` and `lastIndex = 0`.
  - The struct's switch logs the empty `newconf` (`:479`).
  - `becomeFollower(r.Term = 0)` follows (`:487`).
- `validate` writes only `MaxUncommittedEntriesSize`, `MaxCommittedSizePerReady`, `MaxInflightBytes` and
  `Logger` (`raft.go:313-333`). So the `TraceLogger` that `trCapStart` names is the one the struct gets.
- `s.cq = cv.CheckQuorum'` is true: `ownRaftPhysC`'s `HnoCheckQuorum` is `rv.checkQuorum' = s.cq`
  (`InvRaftPhys.lean:1168`).
- The untraced instance is today's statement:
  - `trCapStart none` is `⌜TraceLoggerOk⌝`, and `trCapB none` is `emp`.
  - `trNoCut none` can be added to the persistent `InitialState` triple by consequence.
  - `s.gh = {sn, tr := none}` is `{sn}`.
  - `vs` is free but appears only under the gates.
- `RestartNode`'s one call works with the cluster's `γ.raft` at `reTrace = none`.
- `NewRawNode` logs nothing between `newRaft` and its return (`softState`, `hardState`;
  `rawnode.go:51-61`).

**Findings:**
- **S3 (second tier): `trCapStart` (`:144-153`) is a second copy of `trCapB`'s body** (`TracedCap.lean:1078-1088`),
  with the logger as a parameter in place of the field. A conjunct later added to `trCapB` (as A6 added
  `C.length ≤ γ.reBoot.length`) has to be added here too, and `trCapStart_trCapB` re-proved.
  - The principles concern spec families, so this is a maintenance cost, not a hard-rule break.
  - Restatement: factor the traced arm as `trCapCore tr γ id tl c b Φ Λ`, then
    `trCapB … := ∃ tl, r.traceLogger ↦□ tl ∗ trCapCore …` and the traced `trCapStart := trCapCore … false …`.
    `trCapStart_trCapB` then holds by unfolding.
  - Alternatively, keep the copy, with a sentence in `trCapB`'s docstring that `trCapStart` must follow it.
- **N1 (nit): `BootFresh`'s `cv.Applied' = W64 0` (`:125`) is redundant.** At `σ.prev = ⟨0,0⟩`, `σ.ents = []`,
  `HsEmpty hs`, newRaft's existing premise `Applied = 0 ∨ prev.index ≤ Applied ≤ committedAfter …`
  (`:410-411`) already forces it. No traced line reads `Applied`.

### `RawNode.Bootstrap.gatedSpec` (`:537-570`)

**Good:**
- The traced scope (pre-vote off, `s.cq = false`, `|ps| < 2^40`) is exactly what the packing of `rnTrace`
  needs (`InvRawnode.lean:2700-2706`):
  - `s.prevote = false`, `learners = ∅` and `checkQuorum ↦□ false` (via `ownRaftPhysC_cq`);
  - `RnTrBoot` (`:2634`): a follower, `BootLogOk`'s conf entries;
  - `simIdle_boot`'s hypotheses (`TracedNodeBoot.lean:137`): term 1, vote 0, lead 0, the log the
    bootstrap entries, committed `|ps|`, outbox empty. All hold after `becomeFollower(1, None)` and the
    loop.
- The untraced instance is today's: `s.gh.tr = none = γ.reTrace` from `rawNodeFresh`'s `Hgh`, and `r`
  eliminated from the existential.
- The error paths return early, and the post's `err = nil` excludes them, as today.

**Findings:** none on the statement. Docs: S4.

### `setupNode.gatedSpec` (`:578-639`)

**Good:**
- Every premise has its source as the design's table says:
  - `BootFresh` follows from today's premises.
  - `pre`/`s.cq` come from `NewRawNode`'s `cv.PreVote'`/`cv.CheckQuorum'`.
  - `rawNodeAtT` goes to `rawNodeFreshT` as today.
- The untraced instance is today's (`bootDoneG none = True`).

**Findings:** none.

### `startTraceF`, `StartNode.gatedSpecF`, `startTraceF_trCapStart`, `startTraceF_untraced` (`:660-722`)

**Good:**
- `startTraceF_trCapStart` replaces `startTrace_trCapB`'s premise `hc` with facts `nodeBoot` provides:
  `ps.Nodup` and `id ∈ ps` for the permutation of `bootCfg vs`, and `BootLogOk` for
  `C.length ≤ |reBoot|` (`InvApiBoot.lean:53-55`).
- What `run` needs is all there (`node.run.gatedSpec`, `TracedRunSpecs.lean:86-92`):
  - `RunTracedOk`'s first conjunct is `HdynOk` (`StartNode.lean:327`).
  - The second and third come from the law's pure part (point 4).
  - `gateTr (rtkRun γn.esc none)`, `isAdvChan`'s `gateTr (rtkInv …)` (`adv_start`, `InvAdvance.lean:399`) and
    the driver's `escReq` (both `rq` halves, `InvRtk.lean:451`) all come from one `rtk_alloc`
    (`InvRtk.lean:210-230`, which keeps both `rq` halves out of the invariant), done before `γn` is built.
  - *Uncertain*: whether `StartNode`'s current construction of `isNodeChan` and `nodeDriver` needs any
    other gated piece at the initial state. The `readyc`/`advancec` payloads at `Idle` are `True`, so I
    expect not.
- The harness discharge is as the design says:
  - `tcRunFits` is `receiptBound + 3 ≤ 2^61` (`Fits.lean:36`).
  - `γ.bootLen = boot.length` is `probeA_alloc`'s `Hbl` (`ProbeA.lean:142`, `RunConcurrent.lean:382-384`),
    and `Hbf.1 : boot.length = 3` is in scope before `:443`.
  - `by decide` for `2 ≤ |tcVoters|`.
- §1 is unchanged: `raft_tracecheck_safe`/`_accepts` do not mention `HarnessOpen`.

**Findings:**
- **S1 (second tier): `2 ≤ vs.length` (`:664`) is a scope restriction, not a need, and it becomes part of the
  traced node API.**
  - Principle: "No unneeded premise: … a scope restriction marked as such and filed". Also "a contract
    between packages states the receiver's need, not the supplier's mechanism".
  - Evidence: `run` needs `receiptBound + 2 ≤ traceNumBound`, the ceiling's headroom. `|vs| ≥ 2` is one
    way to get it from `readyFits`. A traced single-voter cluster is legal raft, and it is excluded only
    because `bootLen = 1` leaves one unit too few.
  - `startTraceC` is in `TracedNodeApi`, which is on `etc/api/raft.txt:162`. So the restriction becomes
    part of the client-facing traced `StartNode` (and `interface/…/TracedNodeApi.txt`), not only an
    internal statement.
  - Affected: the harness, today unaffected (3 voters). Any future traced client with one voter.
  - Restatement: a sealed fit naming the need, in the node API's vocabulary, next to `readyFits`:
    `@[no_expose] def traceFits (γ : Cluster) (N) : IProp GF := ⌜receiptBound GF + max γ.bootLen 2 ≤ 2^61⌝`.
    It needs an intro law from the pure bound and a law `traceFits ⊢ readyFits`. `startTraceF` then takes
    `traceFits γ N` in place of `readyFits γ N ∗ ⌜2 ≤ |vs|⌝`. The harness discharges it from `tcRunFits`
    (`max 3 2 = 3`) with the same glue.
  - If the agent keeps `2 ≤ |vs|`, say in `startTraceF`'s and `startTraceC`'s docstrings that it is a
    scope restriction (single-voter traced clusters excluded), and why.

### The laws (`:246-267`, `:710-722`)

**Good:** each holds at both literals of its free mode:
- `trCapStart_trCapB` untraced reduces to the nil logger and `emp`.
- `trNoCut_trNoSnap` and `isStorage_trNoCut` are vacuous untraced.
- `startTraceF_trCapStart` untraced is `⌜tl = nil⌝ ⊢ ⌜vacuous⌝ ∗ ⌜TraceLoggerOk tl⌝`.

Each is stated from its consumer's goal.

**Findings:**
- **N2 (nit, law coverage):** `trNoCut` and `bootDoneG` are boxed or persistent in body, but no `Persistent`
  instances are declared. `TrNoSnap` has one (`TracedSend.lean:48`). Add them next to the definitions.
- **N3 (nit):** `bootDoneG tr id` (`:167-170`) and `startDoneB γ id` (`TracedApiDraft.lean:88-91`) have the
  same body. Defining `startDoneB γ id := bootDoneG (Cluster.trace γ) id` makes the step that
  `StartNode`'s proof needs a definitional unfolding instead of a law.

### Documentation

- **S4 (second tier):** the decisions entry says it supersedes A8.2's minting point, but three places still
  say `setupNode`:
  - `notes/decisions.md`'s Amendment A8 entry (`:37157`, "minting the witness at the end of
    `setupNode`") is not marked *superseded in part* with a pointer, which the header requires
    (`notes/decisions.md:13-14`).
  - The design's §5.3 (`notes/trace-check-design.md:1941`, "Nothing below is to do but the minting at
    the end of `setupNode`") also lacks a pointer to the step-5 section.
  - `startDoneB`'s docstring (`TracedApiDraft.lean:86-87`) has the same sentence, to fix when the Draft is
    replaced in place.

## Go code and `issues/`

I found no bug in the Go code. The `validate` call, the order of the hooks in `newRaft` and `Bootstrap`,
and `traceConfChangeEvent`'s reads are all as the statements assume. Nothing to file.

## Ranking (need of revision)

1. `startTraceF` / `StartNode.gatedSpecF`: S1 (API-visible scope restriction).
2. `raft.applyConfChange.gatedSpec`'s derived `tracedSpec`: S2 (proof plan and design table).
3. `trCapStart`: S3 (duplicate body). `BootFresh`: N1.
4. Laws: N2, N3. Documentation: S4.
5. `raft.switchToConfig.gatedSpec`, `RawNode.Bootstrap.gatedSpec`, `setupNode.gatedSpec`,
   `NewRawNode.gatedSpec`, `rawNodeAtT`/`rawNodeFreshT`: no finding.

No first-tier finding: the statements can be proved as they stand.
