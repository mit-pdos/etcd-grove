# Plan: a closed proof that raft's traces pass its own TLA+ trace validation (draft, 2026-11-08)

Branch `trace-check`. Background, harness, transcription and its checks:
`notes/raft-trace-validation.md`. Status: **resumed against the corrected specification (`etc/tla-fixes/`, the user's decision, 2026-11-08; see "Resumed" below); before the Freeze.** The stage follows
`notes/spec-first-plan.md`'s phases (Scope, Draft, Review, Test, Probe, Freeze, Prove; no proof
before the user's freeze, the tag `trace-check-frozen`); amendments after the freeze are dated,
below the section they amend.

## Paused (the user's decision, 2026-11-08)

Draft, Review, Test and Probe are done; nothing is frozen and Prove has not started. The reason:
`etcdraft.tla` turned out not to fit raft in many places (two of its invariants are false of raft
and of the specification itself, seven fidelity gaps where trace validation rejects a correct
run, and an evaluation error in `Restart`; ten write-ups, two of them, the invariants, already
reported upstream by others: etcd-io/raft#549, #515), each avoidable only by narrowing the workload or patching
the model, which erodes what the closed theorem was for (an external, upstream specification). So
the stage's work went instead into writing up those findings, each with a test at raft `main`
(`issues/raft-tla-*.md`; `notes/raft-trace-validation.md`, "Where etcdraft.tla does not fit raft").
Q4 (b) stays in place in both transcriptions; Q5-Q7 stay open (the discussion of Q5 on 2026-11-08:
its option (c), letting the specification refuse a vote, branches, which upstream's `TraceMatched`
and this checker's `branched` reject; so (a), the in-order links, or (b), modelling raft's `lead`).
Resuming means choosing what the theorem is against: upstream's model as it is (narrow workload),
a corrected model (the findings' fixes), or another specification.

## Resumed (the user's decision, 2026-11-08)

Against `etc/tla-fixes/`'s series (`notes/decisions.md`, "Trace-check against the corrected
`etcdraft.tla`"). Done: both transcriptions follow the series (checked against TLC on state spaces
and traces, and against each other), Q7 replaced by the relational acceptance (`CheckTraceRel`,
`TraceAccepts`), layer C's specs and proofs rebuilt (`Timeout` with `Set.Subset` and `IsQuorum`
new). Next: Q6's premises redrafted against the corrected specification (the user agreed to the
premises a proof needs, gated on a traced cluster, existing proofs kept; shown side by side before
Lean), the verified raft fork gaining 0001 and 0011's trace logging (raft code), then layer C's
remaining actions and the checker's loop (S6), the simulation (S5), the harness (S7).

**Progress under the goal (`notes/trace-check-goal.md`, 2026-11-09):** Q6 step 1 (the gate) and
step 2 (`InvTrace`: the event, the trace ghost, the logger's contract) committed, the first passing
the acceptance test; S5's Draft begun: `TraceSim` (`evConv`, `entAbs`, `msgAbs`, `SimServerR`),
`TraceSimGhost` (`simInit`, `SimRun`, `simNode`, `inFlight`, `simInv`, `simRun_accepts`),
`Trace.RunRel` with its acceptance lemma (proved), `TracedApiDraft` (`Cluster.trace`, sealed in
`InvNode`; `StartNode.gatedSpec`). **Decided by the agent:** each gated node-API statement replaces
its current spec only once proved (a `sorry` in `StartNode`'s proof would reach every closed
theorem). **Found:** `StepR`'s `rejectVote`, `commit` and `beat` (`HeartbeatOk`) are looser than raft; the
exactness comes from the code facts at the hooks, in the traced specs of raft's internal functions,
not from `StepR` (which cannot state `rejectVote`'s: `toPState` hides a pre-candidate's leader)
(`notes/trace-validation-sim.md`, revision 13). **Per-rule simulation lemmas proved**
(`TraceSimLemmas.lean`): vote grant, higher term, campaign, `recordVote`, `becomeLeader`, append,
adopt-leader, `commitTo`, `appResp`, `lose`; `maybeAppend` as the specification's truncate/append
steps (`Conflict`, `NoConflict`, `AlreadyDone`, stale, heartbeat, reject); `AdvanceCommitIndex` at
the quorum index; the sends (`MsgApp`, heartbeat, self-acknowledgement, vote requests); a line with
one successor checked without branching. **The global steps (2026-11-09, proved):** a run (`SimRun`, now over the
prefix's parsed lines, `linesTrace`: `newTraceWith` can fail on a prefix) extends by a line with one
successor (`simRun_snoc_single`), through the trace congruences (`next_congr`, `stepLoop_congr`,
`checkLine_congr`, `runRel_congr`, `bootstrapOf_snoc`); raft's formatted ids parse back
(`parseID_decStr`); a node line matches the `R`-related server (`stateMatches_node`); the `Commit`,
`BecomeLeader` and `Replicate` lines' steps (`simRun_commit`, `simRun_becomeLeader`,
`simRun_replicate`, `simRun_becomeCandidate`, `simRun_ready`, `TraceSimMatch.lean`) and every send
line's (`simRun_heartbeat`, `simRun_msgApp`, `simRun_requestVote`, `simRun_selfVote`, `simRun_selfAck`;
replies to others skipped, `simRun_skipResp`), each modulo the invariants at the result
(`violated = none`; the pure half proved: `InvFacts` gives it, `TraceSimInv.lean`) and the line
past the node's bootstrap lines. Receive lines: a line's rounds as a chain of single successors
(`Chain`, `simRun_snoc_chain`), a receive's successors from the one matching message
(`next_receive`), the first receive line's step (`simRun_recvAppResp`, a successful append response at
the leader), modulo the network's message uniqueness (`MsgsDet`/`AppSlices`, layer B's invariants).
Then (2026-11-09, proved, `TraceSimMatch.lean`): every receive line of the hook table
(`notes/trace-validation-sim.md`): vote requests and responses, accepted append requests through
their truncation chains (`chain_appAccept`), heartbeats, stale and rejected append requests, lower-term
responses (`DropStaleResponse`) and requests (the phantom reply), a response of the node's term at any
role (`respSt`), each after a first round where raft has one (`FirstRound`: `UpdateTerm` at a higher
term, a candidate's `ReturnToFollower`; the rounds fresh by term or role, `srvKey`); and the
`BecomeFollower` lines, skipped after such a first round or stepping down (`isBF_eq`: the node's last
line decides). Each step is pure, modulo its premises: `R` before and after, the invariants at the
states visited, the line past the bootstrap lines, the matched message unique among those the line
could match. Next: those premises from raft's ghost state (the hook-path traced specs, Q8).

S5 Draft (2026-11-09, `TracedHooksDraft.lean`, in review round 1): the hooks traced (`TraceFire`,
`TraceFireOpt`, `TraceFireN`), `raft.send.tracedSpec`, and a line's effect `LineEffect` stated for
every trace and global state where the line could occur (the per-line lemmas are generic in the
trace), so the global step is one pure theorem (`simRun_lineEffect`, proved: a run extended by a line
with an effect, given the bootstrap, skip and uniqueness conditions and the invariants at the
intermediate and final states); `lineEffect_heartbeat` proved as the first effect. Layer C's
`types.go` functions delegated (a worktree branch, `trace-check-layerc-types`).

**S5 Draft review round 1 (`notes/trace-validation-reviews/s5-r1.md`): six first-tier findings,
repaired in the Draft** (F5 by the revision already made: the effect is stated on the global state,
so a message line acting on another server than its node cannot pass): F1 `traceNodeEvent` premise
`evt` below the names (`String()` panics past them); F2/F3 the message hooks' gates keyed on
`(mtypeOf …).bind` (`recvGate`, `sendGate`: `raft.Step` traces every message it receives, local
ones too, and `send` sends `MsgTimeoutNow`); F4 `trCap` carries raft's configuration as the voters'
permutation and the node's membership, `SimIdle` the `2^63` bounds; F6 `PhaseStep` is for lines other
than `BecomeFollower` (its skip bit comes from the node's previous line, the caller's phase). Second
tier taken: S2 (`PhaseStep` for every server the share stands for), S6 (`TraceFireOpt none` is `Q`),
and the header now says the traced triples are vacuous until Q8's logger clause
(`ownRaftPhys`'s `TraceLoggerOk` gated on the mode) lands. Open, for the next round: S1 (state the
global theorem as one Iris law, `trCap Φ ∗ PhaseStep E Φ Φ' ⊢ TraceFire E (trCap Φ')`), S3 (a
receive's phantom reply and the `Ready` line's movement of pending messages in the shares), S5
(`traceInitState` at `newRaft`, outside `ownRaftPhys`).

**The invariants from the per-server facts (2026-11-09, `TraceSimFacts.lean`, proved):** `simInv`'s
per-server facts drafted (`srvFacts γ C j v`: `v`'s log is raft's log `es` read by `logAbs`, `es`'s
records `logRecs`, its committed prefix `isCommitted`, a leader `isLeader`, the numbers in range;
`allFacts`: every voter's), and from them `MoreThanOneLeaderInv` (`isLeader_unique`), `LogInv`
(`isCommitted_agree`), `LogMatchingInv` (`logRecs_agree`, `plog_match_down`: the specification's
entries are determined by position and term) and `CommitOk`. Left: `ElectionSafetyInv`,
`QuorumLogInv`, `LeaderCompletenessInv`, `CommittedIsDurableInv` (the notes' table: route (b)
clauses and the acknowledgement-history copy). Then: `ElectionSafetyInv` from the specification
invariant `LeaderEntries`, `CommittedIsDurableInv` from `DurInv`, `LeaderCompletenessInv` from the facts
(a server's commit certificate `commitIn`, a leader's full log `leadFull`), raft's vote table and the
specification invariant `CommitWithinLeader` (`commit_in_leader`: `restart_ack_one`'s three cases,
`lc_core` for an earlier term); all seven together (`simFx_violated`, `TracedHooksDraft.lean`) with
`QuorumLogInv`'s fact a clause of `simFx` until the acknowledgement-history copy replaces it. The
three specification invariants' preservation by each action is delegated (worktree branch
`trace-check-specinv`).

**The global step's law, proved (2026-11-09, `TracedHooksGlobal.lean`, `trCap_fire`):** for a line
consuming no message and not bootstrap-named, a capability in phase `Φ`, a `PhaseStep id E Φ Φ'` and
the caller's `FxPres` (its line keeps the state's facts) give the event builder's gate whose update
leaves the capability in phase `Φ'`: inside the logger's atomic update the simulation's invariant
(beside raft's commit invariant, `simNS γ`) steps by the line's effect (`simStep_pure`:
`simRun_lineEffect`, the shares and the pending bag by counts, `BagRep`), the invariants from the facts
with raft's vote table (`simFx_violated`). Next: the law's variants for receive lines (a token and
the bags' uniqueness), `BecomeFollower` lines (the skip bit) and `Ready` lines (pending to sent), then
the hook paths' traced statements and proofs, which supply `PhaseStep` and `FxPres`. The receive variant is proved too (`trCap_fire_recv`: the caller's token `inFlight tn k m`
consumed, the bags' uniqueness `MsgsUniq` a clause of `simFx`, the intermediate states' invariants
from the caller's `FxPresR`). Layer C's `types.go` leaves merged (26 functions); `spec.go`'s state
functions and actions delegated (`trace-check-layerc-spec`). S5 Draft review round 2 started.

**The specification invariants' preservation (merged, `TraceSimSpecInv.lean`, proved):** `DurInv` as
stated is **false** (`durInv_not_preserved`: a leader's self-acknowledgement of its whole log sits in
`pendingMessages` past its durable log until its `Ready`); the strengthened `SpecInv` (`LeaderEntries`,
`DurS`, `TermsLe`, `CandS`, `PrevOk`, `CommitInDurable`, `ReqCommit`, `ReqCommitC`, `LeaderDurPrefix`,
`LogTermsLe`; since review round 3's B6) holds at `Init` and is preserved
by every action the lines take, giving `ElectionSafetyInv`, `CommittedIsDurableInv` (through the
corrected `DurInvFixed`) and `CommitWithinLeader`. What raft must supply, as named hypotheses:
`becomeLeader`'s freshness (no entry, message or request of the new term yet: a term's leader is
unique over time and the only creator of its entries), leader completeness where a server joins a
term (`updateTerm`, `timeout`: `LeaderComplete`; `becomeLeader`'s `hcw`), `MoreThanOneLeaderInv`, and
`AppendEntries`' range `b ≤ Len(log) + 1` (an arbitrary `b` breaks `CommittedIsDurableInv`: a second
place where the specification's action is broader than `NextAsync`). `simFx` is to carry `SpecInv`
in place of `LeaderEntries`/`DurInv`/`CommitWithinLeader`.

**The lines' effects (2026-11-09, `TraceSimMatch.lean`, proved, `LineEffect` form for the callers'
`PhaseStep`s):** sends (`MsgApp`, heartbeat, vote request, the self vote and self acknowledgement,
skipped replies), node events (`Commit`, `BecomeLeader`, `Replicate`, `BecomeCandidate`), receives of
the node's term (responses at any role, `respSt`; vote requests; heartbeats, stale and rejected
append requests), and the generic converters (`lineEffect_nr`, `lineEffect_recv1`,
`lineEffect_recv2` for a first round, `UpdateTerm` or `ReturnToFollower`). Left: the accepted append
request's chains with their intermediate shapes, lower-term messages (a stale response's discard; a
stale request's phantom reply, which must go to the phantoms, not the node's share: round 1's S3),
`Ready` (its bags move as a function of the pending bag, outside `withNode`'s shape: its own law),
`BecomeFollower` (the skip bit) and the bootstrap lines.

**S5 Draft review round 2 (`notes/trace-validation-reviews/s5-r2.md`): seven first-tier findings.**
Repaired: A1 (`PhaseStep`/`PhaseStepR` given raft's configuration facts), A2 (`FxPres`/`FxPresR` given
the call site's premises: pre-vote/check-quorum off, `σ.violated = none`, the received message in
the bag, and the vote table threaded through), A3 (`simFx` carries every message's facts,
`msgFacts`: an append request's source leads its term, its entries' records), A4 (`send` and
`traceCommit` take the caller's `FxPresT`; `maybeCommit` proves its own, blocked until
`QuorumLogInv`'s history copy), A5's first half (`MsgsUniq` over both bags), A8 (`DurS` bounds the
servers' match indices only; `advanceCommitIndex`'s preservation takes the configuration within the
servers). Open, the next slices: A5's second half (`Ready`'s own law: its bags move as a function of
the pending bag, phantoms included), A6 (a receipt answered by a phantom: the reply split between the
share and the phantoms), A7 (laws for bootstrap-named lines after a node's segment, with a per-node
"segment over" witness, for the bootstrap lines themselves, and for the self-addressed messages'
tokens at `Advance`), A9 (whether the leader's facts at a `Replicate` line can have the new entry's
records: raft creates them after the hook), A10-A12 (monotonicity of `TraceFire`, cosmetics). Since repaired: A6 (a receive line's replies split into the share's and the phantoms',
`PhaseStepR`'s `P'`/`Pph`), A5's second half (`trCap_fire_ready`, proved: a `Ready` line moves the node's
pending messages, its share's and its phantoms', to the network, its share empties, and the caller
receives the tokens of its share's messages under fresh keys, `mapSeq (keyBound B)`; `simInv` records
that a node's share holds only its own messages, which `PhaseStep(R)` guarantee for what they add;
the bags by counts, `BagCnt`, with `filter`/`plus`/`minus`). Next: A7 (bootstrap lines and
bootstrap-named lines after a node's segment: a per-node "segment over" record; the self-addressed
messages' tokens at `Advance`).

**A7, first part, and S7's recorder (2026-11-09, proved).** The nodes' `booted` flags (`simBoot`,
`simInv` tying each to the trace: set iff the node has logged a non-bootstrap line; `trCap = ∃ b,
trCapB b`; the three laws set it) and the bootstrap lines' law (`trCap_fire_boot`: an unbooted node's
bootstrap-named line is flagged, `bootFlags_unbooted`, and `TraceNext` steps over it, `simRun_boot`).
Left of A7: bootstrap-named lines after the segment (a lost election's `BecomeFollower`, the
`ApplyConfChange` lines after the first `Ready`: their law, the skip bit from the node's previous
line), and the self-addressed messages' tokens at `Advance`. **S7 (merged):** the recorder meets the
logger's contract (`SyncRecorder.TraceEvent`, `isSyncRecorder_traceLogger`), `Events` returns the
trace, `ConvertEvents` gives `NewTrace`'s input `L.map evConv`, and a fresh recorder allocates the
trace's two halves; found: `ConvertEvents` needs the events ASCII (`TraceEv.Ascii`: the checker
relates strings by `strRel`), which the simulation must supply (a `simInv` clause: raft's names,
roles and types are ASCII constants, its ids `FormatUint`'s).

**A7 finished, A10 (2026-11-09, proved).** The flag map now also records each node's last event
(`simBoot tn i b o`, `LastOf`; `simInv`: a booted node has one), and the capability carries a
predicate `Λ` on it (`trCap … Φ Λ`, default `True`), which the laws set from their events (premise
`∀ e, E e → Λ' (some e)`) and the laws' posts are `trCapB … true` (the node's segment over). With
them: `trCap_fire_bf`, a `BecomeFollower` line past the node's segment, skipped or a step-down as
`bfCond` of the recorded last event decides (`PhaseStepBF`, `FxPresBF`, `bfSrv`; the caller's
`Λ` says what its previous line was: a higher-term receipt, a lost election's response);
`trCap_fire_booted`, any other line of a booted node, bootstrap-named or not (`PhaseStepB`), whose
effect for the application's `ApplyConfChange` is the identity at a server it leaves as it is
(`lineEffect_applyCC`, `AccIdle`: not joint, not a leader, its last committed configuration entry
its configuration, no progress outside it). The self-addressed messages' tokens need nothing more of
the laws: `trCap_fire_ready` hands out the tokens of all of the share's messages, the self-addressed
ones included; keeping them until `Advance` is the `RawNode`'s spec. A10: `traceFire_mono`,
`traceFireOpt_mono` (Iris-Lean lacks `atomic_update_wand`: a local `aupd_wand_post`,
`notes/perennial-changes.md`). Open of round 2: A9 (`Replicate`'s records), A11, A12; then round 3.

**The last effects, the ASCII clause, `newTraceWith` (2026-11-09, proved).** Every line kind of the
workload now has its effect: an accepted append request (`lineEffect_appRecv`, the truncation chain's
intermediate servers `appMid`; after a first round, `lineEffect_appRecvU`), a lower-term response
dropped (`lineEffect_staleResp`) and a lower-term request answered by a phantom (`lineEffect_staleReq`,
`phantomOf`), the application's `ApplyConfChange` (`lineEffect_applyCC`); the higher-term variants of
the one-handler receipts go through `lineEffect_recv2`. `ConvertEvents`'s ASCII premise is a `simInv`
clause (`∀ x ∈ L, TraceEv.Ascii x`, the definition moved to raft's `TraceSim.lean`), which the laws
keep from their events (premise `∀ e, E e → TraceEv.Ascii e`, from `nodeEvOf_ascii`/
`sendEvOf_ascii`: `SendEvOf` now records the message's vote a decimal and no `cc` property, as
`makeTracingMessage`/`traceSendMessage` write). `newTraceWith_len` and `newTraceWith_lines` are
proved (`newTraceWith_ok`), so the simulation's files have no `sorry`. Review round 3 of the S5
Draft started (a fresh reviewer, `notes/trace-validation-reviews/s5-r3.md`); layer C's
`invariants.go` delegated (branch `trace-check-layerc-inv`), `spec.go`'s agent still at work.

**S5 review round 3 (`notes/trace-validation-reviews/s5-r3.md`) and its repairs (2026-11-09).**
Six first-tier findings. Repaired: B1 (the `Ready` law's tokens name their list's phase), B2 (an
accepted append's intermediate states only past the batch's first conflict, `ConflictBy`: at the
others `QuorumLogF` can fail), B3 (`ApplyConfChange`'s effect zeroes the progress outside the
configuration, `accSrv`; `AccIdle` takes no pending change instead of "not a leader"), B4 (heartbeat
responses at any term, lower-term heartbeats, and the higher-term second rounds as one-round
receipts, `RecvAt`/`lineEffect_recvU`/`recvAt_*`), B5 (`CCEvOf`, `traceInitState.tracedSpec`,
`traceConfChangeEvent.tracedSpec`, `trCapB_cfg`; open: `newRaft` and `switchToConfig` must hold
`ownRaftPhysCV` closed at the hook), C2-C4 (the hook paths' capability keeps the flag and the last
event; `trCap_fire_any` unifies the plain laws; docstrings), and the reviewer's Go finding filed
(`nonissues/raft-trace-sendmessage-sender-progress.md`). B6 repaired (branch
`trace-check-specinv-b6`): `SpecInv` gains `ReqCommitC` (an append request's sender a server, its
commit index within the sender's), `LeaderDurPrefix` (a leader's entries of earlier terms durable)
and `LogTermsLe` (entries' terms within their server's, their message's); `CommitWithinLeader`
becomes `CommitInDurable` (within the leader's durable log; `CommitWithinLeader` derived) and
`ReqCommit` bounds by the durable log. `CommitInSenderDurable` is gone: `CommitInDurable` gives it.
In exchange `UpdateTerm`/`Timeout` take `LeaderComplete` (`allFacts_commitOk` and
`allFacts_leaderCompleteness`'s entry-level statement, not the commit index within the leader's log
length, which cannot give the durable bound). `QuorumLogS` (= `QuorumLogF`, `QuorumLogF_eq`) is kept
by `AppendEntriesAlreadyDone` (`quorumLog_appendEntriesAlreadyDone`, both of its `CommitTo`s, the
heartbeat's included), given `CommitOk` (`allFacts_commitOk`), `i` and the sender of one
configuration (`SimServerR`), and the two committed prefixes comparable in the new state
(`allFacts_logInv` of the post-state). **A9 decided by the agent (2026-11-09):** `srvFacts`
allows a leader's pending entries (its `Replicate` lines' entries, which raft appends, and so
records, only after the hook): the abstract log is `es ++ pend`, records and `leadFull` over `es`,
`pend` the leader's own term's (branch `trace-check-a9`). The alternative, the leader minting the
records before the hook, would leave raft's predicate with its ghost log ahead of its physical one
at `traceReplicate`'s call. **Done (branch `trace-check-a9`):** `srvFacts` as decided, plus one clause the decision
missed: with `pend ≠ []`, the leader's campaign log `F0` (`isCamp`) is a prefix of `es`, and `es` is
`F0` or ends in an entry of the term (raft's `campOwn` for a leader; `es = F0` at `becomeLeader`'s own
entry, traced before the win's append). Without it `LogMatchingInv` does not follow: `leadFull γ T
es` is a lower bound (a full log the leader once had), so another server's recorded entry of `T` past
`es` is not excluded, and nothing persistent stops `es` from extending `F0` by entries of earlier terms
(`isTermLog`'s initial log and `isCamp`'s `F0` are separate records), where that server's log has
`T` from `F0` on (`recs_chain`): their terms would differ below a position where both have `T`. All
derivations re-proved with their statements unchanged (`pend_match`, `commit_in_leader_pend`). Open: C1 (`FxPresReady`/`FxPresBF` proved once, after B6), C5, C6
(`MsgsDet`), C7; then round 4.

**Round 3 closed, round 4 started (2026-11-09).** Merged: A9 (with a campaign clause the derivation
needs: a leader with pending entries has its campaign log a prefix of its recorded one, which ends in
its term or is that log; raft's `campOwn` holds it), B6 (`SpecInv` gains `ReqCommitC`,
`LeaderDurPrefix`, `LogTermsLe`, `CommitInDurable`; `CommitInSenderDurable` gone; `UpdateTerm`/`Timeout`
take `LeaderComplete`, which `simFx` gives; `QuorumLogF` at a raised commit, `quorumLog_commitTo`),
C1 for `Ready` (`fxPresReady`, the law's premise dropped; `FxPresBF` stays the caller's: with
A9's pending entries a leader's step-down keeps the facts only where it has none), and layer C's
`invariants.go` complete (`Violated` through the package fact for `Invariants`, `etc/gen-init.py`).
Open: C5 (pure premises into preconditions, when the traced statements become `X.spec`), C6, C7;
`trace.go` delegated (branch `trace-check-layerc-trace`); review round 4 under way
(`notes/trace-validation-reviews/s5-r4.md`; D1 done: `SpecInv`'s `CfgFixed`, `hcfg` gone).

**Round 4's first tier (2026-11-09).** D1 merged (`SpecInv`'s `CfgFixed`; `specInv_applySimpleConfChange`).
D2 merged: `becomeLeader_hyps` (`TraceSimLeader.lean`) derives `specInv_becomeLeader`'s four hypotheses
from the new leader's `isLeader`/`isCamp`/`logRecs F0`, its term map without the term, the vote table
and `simFx`; `msgFacts` now also says only an append request carries entries, within `w64` (raft's
every message), and carries an append request's commit certificate (D4). **Open for the Prove phase
(raft's own proof, not the Draft):** raft's ghost takes a vote win in one step
(`ownRaftGhost_step_win`, after `stepCandidate` returns), so at `traceBecomeLeader` it never holds
`isLeader γ i T` with no term log of `T`; the step must be split, the registration (`reWins`,
`win_register`) before `becomeLeader`'s hook and the term log with the empty entry at its append, with
`WinsOk` relaxed for a registered win. D3, D4, D6 done; D5 (`FxPresBF` a lemma for `VoteLost`) left as
the caller's; C5-C7 open (second tier).

**Round 5 (`notes/trace-validation-reviews/s5-r5.md`, 2026-11-09): one first-tier finding, repaired.**
E1: the `BecomeLeader` line's facts need the new leader's term log absent before the step and present
after, so a persistent `FxPres` cannot carry them; the plain-line laws now take `FxPresU` (consumed
once, with a ghost update `==∗` and a resource `R'` returned with the capability; `FxPres` is its
case `R' = emp`, `fxPres_upd`), so the term log is created inside the line's step. The split of
raft's win step is then: the registration before `becomeLeader`'s hook, the term log in the line's
step, the empty entry at the append, with `WinsOk` and (E4) `campOwn`'s leader clause relaxed until
that append. E2: `msgFacts`' commit certificate dropped (raft's `Step` has the real source, its
message facts `#Hmsg`, `commitIn_move`); E3 docstrings. Open (second tier): D6 (`send` with
`PhaseStepB`), C5-C7. Next: round 6.

**Round 6 (`notes/trace-validation-reviews/s5-r6.md`, 2026-11-09): nothing first-tier; the S5 Draft
is frozen** (tag `trace-check-frozen`, the freeze delegated by the user). Second tier: F4 done
(`FxPresUT`, the mode gate); F3 docstrings done. F1 and F2 correct this plan's account of the Prove
phase's raft-side changes: **(F1)** the records of a leader's new entries are needed before raft
creates them (raft broadcasts them in the same `Step`: `becomeLeader(); bcastAppend()`, `appendEntry`
then `bcastAppend`), so each `Replicate` line's `FxPresU` creates them (`propTk_set` is a basic update;
the rest of a record is persistent or the term log's), the send lines only reading them; **(F2)** the
win's registration before the hook: `stepCandidate`'s spec gains the converse of its win
(`JQuorum → won`, as `JointConfig.VoteResult`) and `Step` keeps the ghost open across the handler, so
nothing needs relaxing; else `WinsOk` and `TermsOk` (not `campOwn`) are relaxed until the end of
`Step`. Also for the Prove phase: `maybeCommit`'s new `isCommitted` must be created before its
deferred `traceCommit` (the law holds `raftLogInv` open and passes `FxPresU` only `votesTbl`).
F5 (D6, C5-C7) cosmetic, open.

**Prove phase begun (2026-11-09).** Layer C's `trace.go` merged (41 functions; the checker's package
fact now holds `Invariants` and the three tables, both proved by `etc/gen-init.py`'s generated
`Init.lean`, the tables' literals in the initializer's insertion order); its rest (the out-of-scope
actions' `*IfLogged` branches, `nonReceive`, `Next`, `StepLine`, `NewTrace`, `CheckTrace`) delegated
(branch `trace-check-layerc-top`). **Q8 staged (decided by the agent):** stage 0, mechanical: raft's
logger clause becomes `TraceLoggerOkS s.gh.tr tl`, and the hook paths' specs take a pure
`s.gh.tr = none` premise threaded up to the node invariants, which record the mode (the untraced
clients' `reTrace = none`), checked against Q6's acceptance test (branch `trace-check-q8`); stage 1
replaces that premise by the traced capability function by function, from the hooks up, with the
raft-side ghost changes rounds 5-6 recorded (the win's split, the records in the `Replicate` lines'
steps).

**Q8 stage 0 done (2026-11-09, branch `trace-check-q8`).** Raft's logger clause is
`TraceLoggerOkS s.gh.tr tl` (`InvLogger.lean`: `TraceLoggerOk` when `none`, `True` when `some`);
`ownRaftPhysC_traceLogger` takes `s.gh.tr = none`. Premise `s.gh.tr = none` on the hook paths' specs
(`send` and every caller of a hook up to `raft.Step`, `tickElection`/`tickHeartbeat`,
`applyConfChange`/`switchToConfig`, `appliedTo`/`appliedSnap`; `Step`'s dispatch lemmas, `stepLeader`'s
helpers); `γ.reTrace = none` on the `RawNode` specs that reach them (`Advance`, `ApplyConfChange`,
`Bootstrap`, `Campaign`, `ForgetLeader`, `Propose`, `ProposeConfChange`, `ReadIndex`, `Ready`,
`ReportSnapshot`, `ReportUnreachable`, `Step`, `Tick`, `TransferLeader`, `acceptReady`,
`readyWithoutAccept`), `setupNode`, `node.run` (`γ.raft.reTrace = none`); `Cluster.trace γ = none` on
`StartNode`/`RestartNode`. Invariants: `ownRawNode`, `ownRawNodeIdle`, `ownRawNodeReady` record
`s.gh.tr = γ.reTrace` (`%Hgtr`); `ownRaftPhysC_view`'s and `ownRaftPhysReady`'s close wands keep
`g.tr = s.gh.tr`. `cluster_alloc` gives `⌜Cluster.trace γ = none⌝` (from
`ownRaftGhost_alloc_core_reg`'s `γ.reTrace = none`); kv, kvreconf, kvdurable and the server carry it to
their `StartNode`/`RestartNode` calls (`kvCluster_alloc`, kvreconf's and kvdurable's `isClusterC`,
kvdurable's `StartCluster` and `kd_alloc`, the server's `srvClusterOk`, `newRaftNode`'s and
`NodeStartSpec`'s `%Hraft`). **Decided by the agent:** `newRaft` keeps setting `tr := none`
(`s.gh = { sn := sn }`), not the cluster's mode: in stage 0 its own `becomeFollower` needs
`tr = none`, so a mode parameter would only add a premise; stage 1 parameterizes it with the traced
capability.

**Q8 stage 1 (slice 1), 2026-11-09 (branch `trace-check-q8s1`): the capability's gate; the hooks'
traced proofs blocked.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1: the capability's
gate"): no wrapper over the Draft's capability, which is already mode-indexed (`trCapB none … = emp`,
`TraceFire none tl E Q = ⌜TraceLoggerOk tl⌝ ∗ Q`, `FxPresT none … = True`); stage 1 adds the gate
`trOwn tr P` (`emp` untraced) on what a hook reads only when traced (raft's state, the message), so
that the untraced call sites, which hold the struct open, keep their proofs, and the untraced phase
`phaseBot` with its vacuous phase steps. The Draft's vocabulary moved verbatim to `TracedCap.lean`
(the specs must import it, and the Draft imports the specs); no statement of the Draft changed. **Not
done: the hooks' unified specs, and with them every function above** (each proof takes its callees'
specs, so nothing above a hook changes before the hook is proved). Scoping the traced branch of
`traceEvent` found: (1) `r.state.String()` reads the package variable `stmap`, absent from raft's
package fact (`isInitialized`, `Base.lean`): to add (proved from the initializer; one full rebuild,
`Base` reaching about 4,700 modules); (2) `makeTracingMessage`'s `m.GetType().String()` is the
trust-boundary axiom `raftpb.MessageType.String`, which returns *some* string, while the Draft's
`MsgEvOf` needs the type's name: the traced `traceSendMessage`/`traceReceiveMessage`, hence
`raft.send`, are not provable without a stronger trust assumption (**Q9**, the user's); (3) `send`'s
traced proof needs the queued message after the queue accessor has taken it (an accessor lending the
last queued message of `ownRaftPhysCV (sendMsgs s out)`); (4) new specs and proofs for the
builders the traced `traceEvent` calls (`stateMachineEventType.String`, `StateType.String`,
`formatConf`, `makeTracingState`, `makeTracingMessage`) and accessors lending `ownRaftPhysCV`'s
reads (`hardState()`, `raftLog.lastIndex()`, `trk.Voters[i]`, as `ProgressTracker.ConfState`'s
proof reads them). Next: (1) with the next full build; the node-event hooks (`traceNodeEvent` and
the six that call it) after (1) and (4); `send` and its callers after Q9 and (3).

**Q8 stage 1 (slice 2), 2026-11-09 (branch `trace-check-q8s2`): the node-event hooks, one spec for
both modes.** Done: (1) raft's package fact holds `stmap` (`"#stmap" ∷ globalAddr stmap ↦□ stmapV`,
`Base.lean`; proved in `Proof/go_etcd_io/raft/v3/Init.lean`, which is hand-written, not generated by
`etc/gen-init.py`: raft's packages are its `RAFT_INIT`, outside the script). (2) Specs and proofs of the
event builders: `stateMachineEventType.String` (the name, `evtNames`), `StateType.String` (`roleStr`, from
`stmap`), `formatConf` (the ids in decimal, `decStr`), `makeTracingState` (through `r.hardState()`),
`makeTracingMessage` (its nil case only: the message case names the type, Q9). The accessors were not
needed as new lemmas: `traceEvent`'s proof reads `r.id`, `r.raftLog` and `r.state` with the existing
`raft.wp_load_*C`, the log with `ownRaftPhysC_log_at` and the tracker with `ownRaftPhysC_tracker`
(`Voters[i].Slice()` as `ProgressTracker.ConfState`'s proof). (3) `traceEvent.spec` is one spec for both
modes, by the caller's mode `tr`, in a lending form (`trOwn tr (∃ c id s, ownRaftPhysCV … ∗ ⌜…⌝ ∗
(ownRaftPhysCV … -∗ R))`, so that its untraced callers need no node state), its traced case covering node
events (`m`, `prop` nil); proved, the event's cell and slices made read-only, the logger's `TraceEvent`
handed the caller's update. `traceNodeEvent` and the seven hooks calling it (`traceBecomeFollower`,
`-Candidate`, `-Leader`, `traceReady`, `traceCommit`, `traceReplicate` with `TraceFireN`, `traceInitState`
in `traceEvent`'s lending form: `newRaft` has no node state at the call) are one spec each, at `s.gh.tr`
(`trOwn s.gh.tr (ownRaftPhysCV …)`, `TraceFire s.gh.tr tl (NodeEvOf …) Q`); the Draft's `tracedSpec`s of
`traceNodeEvent`, the three `traceBecome*`, `traceReady`, `traceReplicate` and `traceInitState` follow
(`TracedHooks.lean`, `trOwn_split`). Their direct callers (`becomeFollower`, `becomeCandidate`,
`becomeLeader`, `maybeCommit`, `appendEntry`, `newRaft`, `RawNode.acceptReady`) instantiate the untraced case
(`wp_node_hookC`, `trOwn_of_none`, `traceFire_of_none`, `traceFireN_of_none`): **their `s.gh.tr = none`
premises stay** (decided by the agent): replacing them by the capability needs each caller's phase step
for its line (`PhaseStep*`, `FxPres*` from the node's ghost, the laws `trCap_fire*`), the Prove phase's next
step, not a mechanical change. **Decided by the agent:** `TracedCap.lean`'s gates (`TraceFire`,
`TraceFireOpt`, `TraceFireN`, `trOwn`, their lemmas) moved to a section at any `HasLC` (statements
unchanged; they were at `HasLC.hasLC` with the rest of the Draft), so the hook specs keep the callers'
`HasLC`. **Found wrong and fixed:** `isTraceLogger`'s `TraceEvent` returned any value (a panic's included),
which left `traceEvent`'s continuation unprovable; it now returns `#()` (`InvTrace.lean`; the recorder's
proof, `tracecheck/Logger.lean`, already had it). Not done: `traceCommit.tracedSpec` and
`raft.maybeCommit.tracedSpec` (capability level), the message hooks and `send` (Q9; slice 1's item 3, the
accessor lending `send`'s queued message, not started), `traceConfChangeEvent` (still the untraced spec).

**Q8 stage 1 (slice 3), 2026-11-09 (branch `trace-check-q8s3`): the node-event hooks' direct
callers, one spec for both modes.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1 (slice 3)"):
a direct caller of a node-event hook takes, in place of `s.gh.tr = none`, **the hook's gate from its
caller**, `HookGate s.gh.tr r E Q` (`TracedCap.lean`: an update at `⊤` run at the hook, giving the
logger field and `TraceFire s.gh.tr tl E Q` for the line's events `E`), and gives `Q` back. Done:
`becomeCandidate` (`E` the `BecomeCandidate` events of `becomeCandidate id s`), `becomeFollower` (the
`BecomeFollower` events of `becomeFollower s term lead`; a traced node's struct at its configuration's
voters, `s.gh.tr ≠ none → V = c.voters`), `maybeCommit` (the `Commit` events at each outcome,
`maybeCommitOut`: `Committed()`'s quorum index and `raftLog.maybeCommit`'s test, also in its
postcondition; the gate per outcome, run once the outcome is known: where the caller creates the new
commit's `isCommitted` before the law opens raft's commit invariant). Their **capability forms**, the
Draft's shape (`trCapB` in phase `Φ`, the line's phase step, last event and facts, `trCapB … true Φ'`
out), are corollaries at `HasLC.hasLC` (`raft.becomeCandidate.traced`, `raft.becomeFollower.traced`:
`trCap_fire_boot` during the node's bootstrap segment, `trCap_fire_bf` after it; `raft.maybeCommit.traced`;
`TracedHooks.lean`, from `trCapB_hookGate`/`trCapB_hookGate_bf`, `TracedHooksGlobal.lean`). Derived: the
Draft's `traceCommit.tracedSpec` (`traceCommit.tracedSpec_of_spec`, the `Commit` line's phase step
`phaseStepB_commit` from `lineEffect_commit`, for every server the share stands for: `simServerR_toC`,
`advancesTo_toC`). Their callers instantiate the untraced case (`X.untraced`, `TracedUntraced.lean`; the
call sites unchanged). **Why the gate, not `trCapB`, in the specs:** the capability holds `inv` and raft's
commit invariant, at `InvGS GF` (`HasLC.hasLC`), while these functions and their callers are proved at
any `HasLC`; stating it would move them and their results there. **Not done:** `raft.maybeCommit.tracedSpec`
(the Draft's: the `Commit` line's facts proved inside, which needs `QuorumLogInv` at the raised commit,
the Draft's A4/C4 blocker; `raft.maybeCommit.traced` takes them from the caller); `becomeLeader` and
`appendEntry` (`appendEntry` calls `send`, whose spec keeps `s.gh.tr = none` until Q9 and `send`'s queue
accessor; with them the `BecomeLeader` line's term log and the `Replicate` lines' records in their
`FxPresU`); `newRaft` (still `tr := none`: its `traceInitState` runs before raft's predicate holds, round
1's S5, and a traced `newRaft` would create the node's capability); `RawNode.acceptReady` (the struct is
open at `traceReady`, `ownRaftPhysReady`'s fields, and the RawNode-level spec hides the struct,
configuration and state). Next: the traced `raft.Step` handlers' phase steps and facts (from raft's
ghost) for these lines, with the win's split; `send` after Q9. Checked: full `lake build` green; `etc/tcb-report.py --check` (807 axioms, 4 `sorry`s, unchanged) and every collection `--reuse --check`; `interface/` differs in the three functions' proof files only; `etc/api-check.py` 0 errors; `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 4), 2026-11-09 (branch `trace-check-q8s4`): the message hooks, one spec for both
modes; `raft.send` blocked on the queued message's lending.** Decided by the agent (`notes/decisions.md`,
"Q8 stage 1 (slice 4)"). Done: (1) `makeTracingMessage` in full: its message case (a conjunct beside the
nil one, as the getters' specs) builds a read-only `TracingMessage` holding `traceMsgOf ms` (the type's
name `raftpb.msgTypeString`, Q9's exact spec; sender, receiver, vote in decimal; a `MsgSnap`'s entry count
its snapshot's index, `snapIdx`), proved over the getters (`TracedMsg.lean`: `traceMsgOf`,
`msgEvOf_traceMsgOf`: for a traced type it is the Draft's `MsgEvOf` of the abstraction). (2)
`traceEvent.spec` generalized to a message and properties: the caller lends raft's state and the message
in turn out of one resource `P` (`RaftLend`, `MsgLend`, persistent accessors; `traceEvent` reads the
state, then the message last) and gives the properties read-only (`tracingPropsRep prop e0`); every event
whose header is the state's (`EvHdrOf`), message `traceMsgOf`, properties `e0`'s is allowed by `E`
(`traceNodeEvent`'s proof instantiates it with the state alone, no message, `noProps`). (3)
`traceSendMessage.spec` and `traceReceiveMessage.spec` are one spec for both modes in that lending form, at
the caller's mode `tr` with the Draft's gates (`TraceFireOpt tr tl oE Q`, `oE = sendGate …`/`recvGate …`),
the untraced nil logger as a premise (`tr = none → TraceLoggerOk tl`); proved: the type's `switch`, for a
`MsgApp` the sender's `Progress` read into the properties map (`match`, `next`, the map made read-only:
`tracingPropsRep_mn`; none when the lookup fails, `tracingPropsRep_empty`), `time.Sleep` on receipt
(Perennial's proved spec, linked through `Perennial.Proof.time.Link`), `traceEvent`. The Draft's
`traceSendMessage.tracedSpec` and `traceReceiveMessage.tracedSpec` are derived (`TracedHooks.lean`,
`X.tracedSpec_of_spec`: the state and message apart, `raftLend_sep`/`msgLend_sep_some`). Their callers stay
untraced through instance lemmas (`traceSendMessage.untraced`, `traceReceiveMessage.untraced`,
`TracedUntraced.lean`, the statements before slice 4): `raft.send`'s proof, `raft.Step`'s bundle,
`wp_Step_MsgProp` and `raft.appliedTo`; their call sites unchanged. **Blocked: `raft.send`'s traced
case, hence everything above it in this slice** (`sendAppend`, `maybeSendAppend`, `maybeSendSnapshot`,
`sendHeartbeat`, `sendTimeoutNow`, `bcastAppend`, `bcastHeartbeat(WithCtx)`,
`releasePendingReadIndexMessages`, `sendMsgReadIndexResponse`, `appendEntry` with the `Replicate` records,
`becomeLeader` with the term log): slice 1's item 3, "an accessor lending the last queued message of
`ownRaftPhysCV (sendMsgs s out)`", is not provable. `send` queues `m` before `traceSendMessage(r, m)` runs,
so at the hook the queue owns the message (`outboxRel`'s `msgQ`, at `1`); the hook reads raft's state
through specs on `ownRaftPhysCV` (`hardState()` in `makeTracingState`, ...) and the message through its
getters, alternately (the type, the sender's `Progress`, the state, the message). Raft's state, closed,
holds the message; reopening it to lend the message needs to know which queued pointer is `m`, and
`ownRaftPhysCV c V r id s` does not say: its queues are existential (`outboxRel s.outbox msgs msgsAA`,
the abstract outbox up to permutation, no locations), so a lemma `ownRaftPhysCV … (sendMsgs s out) ⊢
msgOwn ml 1 st ∗ (msgOwn ml 1 st -∗ ownRaftPhysCV …)` is false (another resource satisfying the predicate
may queue other pointers), and every read spec gives back an arbitrary `ownRaftPhysCV`, losing the
witness. What would unblock it (a raft ghost change, for the user or the next slice): record the queued
message in the state the read specs preserve, e.g. `NGhost.lq : Option (Loc × MsgSt)` with
`ownRaftPhysCV`'s clause `lq = some q → q ∈ msgs ++ msgsAA` (the lending lemma then holds: `s` pins `q`,
and every read spec returns the same `s`), set by `send` before its hook and reset before it returns (its
postcondition unchanged); the queue-draining closures (`ownRaftPhysC_view`'s `Hclose`, `acceptReady`)
then need `lq = none`, which the `RawNode` predicates would record as stage 0 recorded `s.gh.tr`
(`%Hgtr`). Not attempted here: it changes `Defs.lean`'s `NGhost` (a full rebuild) and the `RawNode`
invariants. Trust base: raft's results now reach `strconv.Itoa`'s trust-boundary axiom (Q9's model's
fallback, through `MessageType.String`, which `makeTracingMessage` calls; the server's already did), and
Perennial's `time.Sleep` (proved, no axiom); no axiom or `sorry` added (the four collections `raft`, `kv`, `kvdurable`, `kvreconf`
updated with `strconv.Itoa.wp_proof`, as Q2's `FormatUint`). Checked (after merging `trace-check`, at
`452d95929b`): full `lake build` green (13774 jobs); `etc/tcb-report.py --check` (806 axioms, 4
`sorry`s, unchanged) and every collection `--reuse --check` (after the four updates); `interface/` differs
in the four functions' proof files only (`makeTracingMessage`, `traceEvent`, `traceSendMessage`,
`traceReceiveMessage`: their specs and callee hypotheses); `etc/api-check.py` 0 errors; `etc/gen-link.py
--raft` (and `--server`, `--kv*`) up to date.

**Q8 stage 1 (slice 5), 2026-11-09 (branch `trace-check-q8s5`): `send`'s queued message lent through
`NGhost.lq` (Q11 (a)); `raft.send` one spec for both modes.** Decided by the agent (`notes/decisions.md`,
"Q8 stage 1 (slice 5)"). Done: (1) **the ghost change**: `NGhost.lq : List (Loc × MsgSt)` (the messages
`send` has just queued, newest first; `MsgSt` moved from `InvPb.lean` to `PbModel.lean` so `Defs.lean`
sees it), `ownRaftPhysCV`'s clause `LqOk s.gh.lq msgs msgsAA` (each recorded message is queued), the
lending lemma `ownRaftPhysC_lq_lend` (the message out of raft's state and back at the same state:
`outboxRel` owns every queued message), the pop `ownRaftPhysC_lq_pop`; `send`'s queue accessors push the
message; the queue-draining closures (`ownRaftPhysC_view`'s, `ownRaftPhysReady`'s) take `LqOk g.lq …`,
from the `RawNode` predicates' new `s.gh.lq = []` (`%Hglq` in `ownRawNode`, `ownRawNodeIdle`,
`ownRawNodeReady`, as stage 0's `%Hgtr`). A list, not Q11's `Option`: `send` (and the Draft's frozen
`raft.send.tracedSpec`) is for any `s`, and an overwritten `Option` cannot be restored after the hook.
(2) **`raft.send`**: one spec for both modes, the hook's gate `HookGateOpt s.gh.tr r (sendOutGate id s c
m.Type' out) Q` (`TracedMsg.lean`, as slice 3's `HookGate` with the untraced nil logger), `Q` back, a
traced node sending no snapshot; proved (`send_hookW`: the message recorded, the gate run, the hook given
raft's state and the message under `trOwn`, `sendGate_le`, the pop); the Draft's `raft.send.tracedSpec`
derived (`raft.send.tracedSpec_of_spec`, `TracedHooks.lean`: `trCap_fire`/`trCap_fire_booted` for a
traced type, `trCapB_mono` otherwise); untraced callers through `raft.send.untraced`
(`TracedUntraced.lean`, the statement before slice 5; `raft.Step`'s bundle and `stepLeader`'s
`hbresp`, `handleAppendEntries`' `wp_send_appResp` take the instance). (3) Outward: `sendTimeoutNow`
(the gate at no event: `MsgTimeoutNow` is not traced), `sendHeartbeat` (the gate at the heartbeat's
commit, `∀ cm` with its two bounds), `bcastHeartbeatWithCtx` and `bcastHeartbeat` (a loop of sends: a
persistent per-heartbeat gate `□ (∀ to cm, … -∗ G -∗ HookGateOpt … G)` and the caller's `G`, threaded
through the `Visit`; each heartbeat's event read at `s`, which no send changes: `sendOutGate` at
`{ sendMsgs s ms with prvals := … }` is `sendOutGate` at `s` by `rfl`; `bcastHeartbeat`'s at the
read-only object's context `hbCtx`), each with its `X.untraced` instance for its callers (`stepLeader`'s
helpers, `sendMsgReadIndexResponse`). **Not done** (their callers unchanged, on `send`'s untraced
instance): `maybeSendSnapshot` stays untraced by design (it sends a `MsgSnap`, which a traced node never
sends, the Draft's P2: its one spec would carry `s.gh.tr = none` anyway); `maybeSendAppend`,
`sendAppend`, `bcastAppend` (a `MsgApp` or a snapshot, by the progress' state; `bcastAppend`'s loop as
the heartbeats'), `sendMsgReadIndexResponse` and `releasePendingReadIndexMessages` (their heartbeats at
the state after `readOnly.addRequest`/`recvAck`, which their gates must name), `appendEntry` (with the
`Replicate` lines' records created in their `FxPresU`) and `becomeLeader` (the term log in the
`BecomeLeader` line's `FxPresU`, after `appendEntry`): next slice. Also: `raft__campaign`'s layout
violation (`campRoleState_gh`, stage 0) fixed, `campRoleState` and its facts moved to
`LemmasCampaign.lean`. Checked (after merging `trace-check`, at `dcc3106c4d`): full `lake build` green
(13778 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections
`--reuse --check`; `interface/` differs by `NGhost.lq` (`Defs.txt`, the record literals of
`RawNode__acceptReady.txt` and `raft__Step.txt`), `MsgSt`'s move (`InvPb.txt` → `PbModel.txt`), the five
gated specs' proof files and `raft__campaign.txt`'s moved helpers; `etc/api-check.py` 0 errors;
`etc/gen-link.py --raft` unchanged; `--layout`: one new violation not this slice's (`traceEvent`'s
`wp_makeTracingMessage_arg`, slice 4).

**Q8 stage 1 (slice 6), 2026-11-09 (branch `trace-check-q8s6`): the rest of the send path, one spec for
both modes.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1 (slice 6)"). Done, each with its
`X.untraced` instance (`TracedUntracedSend.lean`, the statement before slice 6) so that its callers keep
their call sites: (1) `maybeSendAppend`, `sendAppend`: the `MsgApp`'s hook gate from the caller's `G`
back to `G` (`∀ mm`, with `AppOk`, the commit index the log's, to `to`), run only if it is sent; the
snapshot fallback excluded in traced mode by `TrNoSnap s.gh.tr s.logst` (`TracedSend.lean`: compaction,
as `maybeSendSnapshot`'s precondition states it, refuted when traced; the narrowest premise, P2).
(2) `bcastAppend`: a loop, a persistent per-peer gate at `s` (as slice 5's heartbeats;
`appGate_send_prvals`, `hookGateOpt_congr`), `TrNoSnap`. (3) `sendMsgReadIndexResponse`: the single
voter's response gate (at no event: `MsgReadIndexResp` is not traced) and the heartbeats' persistent
gate at `arriveState` (the request registered), each conditioned on its branch (`CfgSingle`). (4)
`releasePendingReadIndexMessages`: persistent per-request gates, the `k`-th request's heartbeats at the
state with the first `k` released. (5) `appendEntry`: `traceReplicate`'s gate (`HookGateN`, one
`Replicate` event per normal entry, `normalCount ents`, of the state before the append) then the
self-acknowledgement's (at the appended state), chained `G` → `G1` → `G2` (`G` back on the reject path):
a traced caller's `Replicate` gate is where the line's `FxPresU` creates the records of the leader's new
entries (round 6's F1), consumed by the next gate. (6) `becomeLeader`: three chained gates (`BecomeLeader`
of `becomeLeaderPre`, before the empty entry; the entry's `Replicate`; the self-acknowledgement at
`becomeLeaderLog`): the `BecomeLeader` gate is where the term log is created (round 5's E1). (7)
`traceEvent`'s layout violation fixed (`wp_makeTracingMessage_arg` moved to `LemmasTraceEvent.lean`).
No ghost change. **Not done:** the capability forms of `appendEntry` and `becomeLeader` (`X.traced`, with
the lines' phase steps and `FxPresUT`; the self-acknowledgement needs the send law beside
`trCap_fire_any`, `appendEntry` an induction over `TraceFireN`) and their traced caller (`raft.Step`'s
win and `MsgProp` arms); the `MsgApp` gate's facts lack P5's "the whole suffix from `Next`"
(`simRun_msgApp`'s `hents`, `hmatch`), to add with that lemma. Callers above stay on the untraced
instances (`stepLeader`'s helpers, `stepCandidate`, `switchToConfig`). Checked (`trace-check` at
`86bb19e789`, merged): full `lake build` green (13781 jobs); `etc/tcb-report.py --check` (806 axioms, 4
`sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in the
seven gated specs' proof files and `traceEvent.txt` (the helper moved out); `etc/api-check.py` 0 errors;
`--layout` 0 new (`traceEvent`'s fixed); `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 7), 2026-11-10 (branch `trace-check-q8s7`): the leader's lines on the capability;
the handlers and `campaign`/`hup` one spec for both modes.** Decided by the agent (`notes/decisions.md`,
"Q8 stage 1 (slice 7)"). Done: (1) **the capability forms** `raft.appendEntry.traced` and
`raft.becomeLeader.traced` (`TracedHooks.lean`, from the gated specs, at `HasLC.hasLC`): each line by
`trCap_fire_any`, the lines' facts **chained** (`FxPresUT … R1 ∗ (R1 -∗ FxPresUT … R2) ∗ …`), so that the
`BecomeLeader` line's update creates the term log and each `Replicate` line's the record of its entry
(rounds 5-6's E1, F1), read by the next lines; `appendEntry`'s `Replicate` lines over a family of
phases `Φs k` (the induction over `TraceFireN`: `trCap_fireN`, `fxChain_none`, packaged as
`trCapB_hookGateN`); the self-acknowledgement's send line by the same law as a gate
(`trCapB_hookGateOpt`, `hookGate_opt`, `sendOutGate_selfAck`; no new law); non-bootstrap names
(`evtNames_notBoot`). (2) **One spec for both modes, gate style**, each with its `X.untraced` instance
(`TracedUntracedStep.lean`, the statement before slice 7; callers' call sites unchanged):
`handleHeartbeat` (the reply's gate at the state with the commit moved), `handleAppendEntries` (the
reply's gate for every state and reply whose send ends in `HandleAppResult`, `∀ s1 mm`), `campaign`
(the role change's gate, `becomeCandidate`'s `HookGate` or an update for a pre-election, and a
persistent per-voter vote gate at the state after the role change; `campMsg` and the message
definitions moved to `LemmasCampaign.lean`), `hup` (`campaign`'s gates; `(⌜s' = s⌝ ∗ G0) ∨ G` back).
`raft.Step`'s bundle takes `hup`'s instance. No ghost change; no client-visible change; no axiom or
`sorry`. **Not done** (step 2's rest and step 3): `stepCandidate` (with the win's split, round 6's F2),
`stepFollower`, `stepLeader` and its helpers, the dispatch, `tickElection`/`tickHeartbeat` (they call
`raft.Step`, so after it), and `raft.Step`'s traced arms (the gates from raft's ghost, a received
message's numbers through a trace-gated conjunct of `isMessage`, the receipt bound); then the node
API (`RawNode`, `node.run`, `newRaft` traced). Checked (`trace-check` at `b5b17cfc4a`, merged): full `lake build` green (13783 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in the four gated specs' proof files only (`raft__campaign`, `raft__handleAppendEntries`, `raft__handleHeartbeat`, `raft__hup`: their specs, and `campaign`'s message definitions gone from its proof file); `etc/api-check.py` 0 errors; `--layout` 0 new, six fixed (`campMsg` … `vrespW32`, dropped from `etc/api/raft-layout.txt`); `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 8), 2026-11-10 (branch `trace-check-q8s8`): the step functions one spec for
both modes; `raft.Step`'s traced arms not started.** Decided by the agent (`notes/decisions.md`, "Q8
stage 1 (slice 8)"). Done, each with its `X.untraced` instance (`TracedUntracedStep.lean`, the
statement before slice 8; `raft.Step`'s bundle, `wp_Step_MsgProp` and `raft.appliedTo` take them, call
sites unchanged): (1) `stepCandidate`: one gate per arm, premised on the arm (`becomeFollower` then the
handler's reply for a `MsgApp`/`MsgHeartbeat`; the vote win's `becomeLeader` chain and `bcastAppend`;
the pre-vote win's `campaign` gates; a loss's `becomeFollower`), `G'` back exactly when a gate ran
(tagged by `JQuorum ∨ JLost` of the tally, `poll`'s `iff`). **The win's split (round 6's F2):** the
`BecomeLeader` gate is premised on the win's quorum, which `stepCandidate` has from `poll`, so a traced
`Step` holding raft's ghost open in `G` registers the win inside the gate, before the hook's line
creates the term log: neither `WinsOk`/`TermsOk` relaxed nor a converse added to `CandVoteRespResultC`
(the converse is the result's tag). (2) `stepFollower`: the handlers' reply gates at the state with the
sender as leader, the forwards' send gate at no event (`G` back), `MsgTimeoutNow`'s `hup` gates.
(3) `stepLeader`: gated for `MsgBeat`, `MsgReadIndex`, `MsgTransferLeader`, `MsgCheckQuorum` (their
helpers take `bcastHeartbeat`'s, `sendMsgReadIndexResponse`'s, `sendTimeoutNow`'s/`sendAppend`'s with
`TrNoSnap`, `becomeFollower`'s gates); `MsgProp`, `MsgAppResp`, `MsgHeartbeatResp` keep `s.gh.tr = none`,
now premised on their type. A `MsgSnap` stays untraced (`handleSnapshot`'s premise, P2). No ghost
change; no client-visible change; no axiom or `sorry`. **Not done:** `stepLeader`'s three arms
(`appendEntry`'s and `bcastAppend`'s gates for a proposal; `maybeCommit`'s per-outcome gate with the
new commit's `isCommitted` created before `traceCommit`, and the sends at the states after
`MaybeUpdate`/`MaybeDecrTo` and `releasePendingReadIndexMessages`, for `MsgAppResp`; the flow-control
`sendAppend` and the read-index responses for `MsgHeartbeatResp`), `raft.Step`'s traced arms (step 2:
`trCapB` in and out, the gates from raft's ghost through the `trCap_fire*` laws, the `isMessage`
trace-gated conjunct for a received message's numbers, the receipt bound), `tickElection`/
`tickHeartbeat` (step 3). Checked (`trace-check` at `1b6fb4fac0`, already merged): full `lake build`
green (13783 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53
collections `--reuse --check`, none updated; `interface/` differs in the three step functions' proof
files only (their specs); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py --raft`
unchanged.

**Q8 stage 1 (slice 9), 2026-11-10 (branch `trace-check-q8s9`): `stepLeader` gated in every arm;
`raft.Step`'s traced arms not started.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1 (slice
9)"). Done: `stepLeader.spec` has no trace-mode premise left. (1) `MsgProp`: `appendEntry`'s `Replicate`
gate (one event per normal entry of the conf-change loop's batch, `∀ cs` decoded changes) and
self-acknowledgement gate, `G` → `Gp1` → `Gp2`, then `bcastAppend`'s per-peer gate, `Gp2` to `Gp2`;
`Gp2` back when appended. (2) `MsgAppResp`: a rejection's `sendAppend` gate at `s`; an acceptance's
`maybeCommit` gate per outcome (`Hgcommit`, for every `Progress` map with the raised `Match` values
`appRespMatch` and every `(b, N)` of `maybeCommitOut` there: where a traced caller creates the new
commit's `isCommitted` before `traceCommit`), `G` to `Gc b N`, then at `commitAt s b N` the release's
gates (single voter: responses at no event; else the `k`-th request's heartbeats), the `MsgApp`s'
(`bcastAppend`, `sendAppend`, the `maybeSendAppend` loop) and the transferee's `MsgTimeoutNow` (no
event), `Gc b N` to `Gc b N`; the result says whether `maybeCommit` ran, with its outcome (it depends
on the sender's `Progress`, which the caller does not name). (3) `MsgHeartbeatResp`: the flow-control
`sendAppend` gate at `s` (shared with a rejection's, `Hgsapp`) and the read-index responses' (no event),
`G` to `G`. The intermediate states are named in `LemmasStepLeader.lean` (`propAppended`,
`appRespMatch`, `commitAt`, with header lemmas `sendOutGate_hdr`, `appOk_hdr`, `trNoSnap_logst` and the
congruences `hookGate_congr`, `hookGateN_congr`). One new premise, on a raft-internal spec: a traced
node proposes no configuration change (`MsgProp → s.gh.tr ≠ none → ∀ e ∈ ents, ¬ IsConfEnt e`, P3: the
conf-change loop's `traceChangeConfEvent` stays untraced). `stepLeader.untraced` keeps its statement;
`raft.Step` and `raft.appliedTo` unchanged. No ghost change; no client-visible change; no axiom or
`sorry`. **Not done:** (a) `raft.Step`'s traced arms (step 2): its spec still takes `s.gh.tr = none`
and every callee through the `X.untraced` instances (`raft.Step.Postulates`); the receive hook
(`traceReceiveMessage`, `recvGate`) needs the receive line's law (`trCap_fire_recv`, `PhaseStepR`,
`FxPresR`) at `Step`'s entry, each arm the step functions' gates built from `trCapB` and raft's ghost
(the lines' `PhaseStepB` from `TraceSimMatch.lean`'s `lineEffect_*`, the `FxPresUT` facts from the
term log, records, commit certificate, vote table: the Prove phase's simulation, with the Draft's
A4/C4 blocker for the `Commit` line's `QuorumLogInv`), the received message's numbers through a
trace-gated conjunct of `isMessage` (`Protocol/GhostState.lean`, every producer's proof: about 19
files) and the receipt bound to `traceNumBound` (`readyFits` gives `receiptBound + bootLen ≤ 2^61`, the
law owed); (b) `tickElection`/`tickHeartbeat` (step 3), which call `raft.Step` and follow its gated
form. Checked (`trace-check` at `cdbf0f5660`, the branch's base, no newer commit to merge): full `lake build` green (13784 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in `stepLeader`'s proof file only (its spec); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 10), 2026-11-10 (branch `trace-check-q8s10`): piece 1 done, the ghost change for a
received message's numbers and the receipt-bound law; pieces 2-4 (`raft.Step` gated, traced,
`tickElection`/`tickHeartbeat`) not started.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1
(slice 10)"). Done: (1) `traceNumBound` and `Msg.NumsBelow` moved verbatim to `Protocol/Model.lean` (no
Draft statement changed), with `MsgType.traced` (the six logged types; `sendEvt_traced`,
`recvEvt_traced`) and `Msg.TrOk`. (2) **The carrier** (amendment A1's, a1-r2's 1): the gated fact
`MsgTrOk γ m` (`γ.reTrace.isSome → m.TrOk`) is a conjunct of **`isMessageC`**, the facts a message carries
on the network (`isRaftMsg`'s), not of `isMessage`: the protocol's step lemmas, which produce
`isMessage` for every message they send, cannot prove it (terms are bounded by no receipt, only by the
`RawNode`'s budget; a `StepC` run's `trans`/`drain` sends messages no final outbox shows), the same
reason the snapshot certificate already sits there. The node's outbox carries it meanwhile: `NsLink`
gains `s.gh.tr = γ.reTrace` and `OutTr γ s`; the step helpers rebuilding `ghostRest` take `OutTrStep s
s'` (by default from the context's `s.gh.tr = none`, `outtr_tac`: `raft.Step`'s branches unchanged); the
`Ready` exits attach it (`readyWithoutAccept` from `OutTr`). A traced `raft.Step` will prove `OutTrStep`
from its send lines (each proves `Msg.NumsBelow` of its message for `TraceEv.Ok`) and take the received
message's `TrOk` as a premise its `RawNode` reads from `isRaftMsg`. (3) **The receipt-bound law**
`ownRaftGhost_traceBound`: given `receiptBound GF + γ.reBoot.length ≤ traceNumBound` (`readyFits`'s bound,
for the traced spec to take from the node API), the last index and commit index are below
`traceNumBound`; terms are not (a premise of the traced `Step`, from the `RawNode`'s `termLB`). No
client-visible statement changed (`isRaftMsg`'s text unchanged; `isMessageC`'s body raft-internal,
vacuous untraced); no axiom or `sorry`. **Not done:** piece 2 (`raft.Step.spec` one spec for both modes:
the receive hook's `recvGate` and the step functions', `hup`'s gates threaded through `raft__Step.lean`,
`raft.Step.Postulates` and the branch files, a `raft.Step.untraced` instance), piece 3
(`raft.Step.traced` at `HasLC.hasLC`: the gates from `trCapB` and raft's ghost, `OutTrStep` from the send
lines, premises the node supplies: the received message's `TrOk`, the term bound, the receipts' fit),
piece 4 (`tickElection`, `tickHeartbeat`); then the node API. Checked (`trace-check` at `bd9b2bed02`,
already merged): full `lake build` green (13784 jobs); `etc/tcb-report.py --check` (806 axioms, 4
`sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in
`Protocol/Model.txt` (the moved definitions, `MsgType.traced`, `Msg.TrOk`), `TraceSim.txt`
(`traceNumBound` gone from it) and `Protocol/GhostState.txt` (`MsgTrOk`, its lemmas, `isMessageC`'s
conjunct, `isMessageC_intro`'s argument); `etc/api-check.py` 0 errors; `--layout` 0 new;
`etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 11), 2026-11-10 (branch `trace-check-q8s11`): piece 1 done, `raft.Step` one spec for
both modes; pieces 2-3 (`raft.Step.traced`, `tickElection`/`tickHeartbeat`) not started.** Decided by the
agent (`notes/decisions.md`, "Q8 stage 1 (slice 11)"). Done: `raft.Step.spec` takes the caller's resources
`R : StepG` through `stepGates` (`LemmasStepGates.lean`: the receive hook's `recvGate`, the term preamble's
step-down `preGate`/`PreBF`, a stale message's answer `LowSend`, a vote request's answer `vrespMsgOf`,
`hupGates`, and the step functions' gate bundles `followerGates`/`candidateGates`/`leaderGates` at
`preState s m pvs`), **raft's ghost state the caller's across the handler** (the receive gate takes
`ghostIn γ md c id s R`, the closing wand `stepClose` gives it back with the caller's `Gout`), and
**`OutTrStep` from the closing wand** (traced: the caller confirms the step's new messages' numbers, from
its send lines, for any model step `StepCD … s recv s'`). Untraced-only, on the type: `MsgSnap` (P2), a
snapshot acknowledgement and an application acknowledgement with entries (`appliedSnap`'s, `appliedTo`'s
premises, not yet gated), a proposed configuration change (P3). `raft.Step.Postulates` takes the gated
specs (`traceReceiveMessage.gated`); every branch lemma threads `R` (macros `wp_recv_gate_ns`, `gates_fol`,
`gates_cand`, `gates_lead`, `bf_gate`, `p3_tac`); the dispatch opens and closes the ghost (`gate_open`,
`gate_close`); the transfer arm's `xw` record moves the gates (`stepGates_xw`) and the ghost's record
follows the closing wand. `raft.Step.untraced` (`TracedUntracedRaftStep.lean`, the statement before slice
11, gates from `stepGates_none`) serves `RawNode`, `node.run`, `tickElection`, `tickHeartbeat` (a `have` at
each proof's start; no spec of theirs changed); `raft.appliedTo` steps its leave through the gated
`wp_Step_MsgProp` with `stepGates_none`. No ghost change; no client-visible change; no axiom or `sorry`.
**Not done:** piece 2, `raft.Step.traced` at `HasLC.hasLC`: build `stepGates` and `stepClose` from
`trCapB` and raft's ghost (the receive line by `trCap_fire_recv` with `PhaseStepR`/`FxPresR`; each later
line's phase step from `TraceSimMatch.lean`'s `lineEffect_*`; the `FxPresU` facts from the term log,
records, commit certificate (`QuorumLogF` at the raised commit via `quorumLog_commitTo`) and vote table;
`maybeCommit`'s `isCommitted` at `leaderGates`' `Hgcommit`; the win registered inside `candidateGates`'
`Hgbl`; `OutTrStep` in `stepClose` from a bounded-step lemma or the send lines), with the premises only
the node supplies: the received message's `TrOk` (`isRaftMsg`'s `MsgTrOk`), a term bound (`termLB`), the
receipt fit (`readyFits`, for `ownRaftGhost_traceBound`); piece 3, `tickElection`/`tickHeartbeat` taking
`Step`'s gates for `MsgHup`/`MsgCheckQuorum`/`MsgBeat` (two steps in one tick: the second's gates at the
first's unnamed end state), with untraced instances; then `appliedTo`/`appliedSnap` gated and the node API.

**Q8 stage 1 (slice 12), 2026-11-10 (branch `trace-check-q8s12`): `Step`'s closing resource at the end
state; piece 3 done (the ticks one spec for both modes); `appliedTo` gated; piece 2 (`raft.Step.traced`)
found not derivable as `Step`'s spec stands.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1
(slice 12)"). Done: (1) `raft.Step.spec`'s `Gout : NState → IProp GF`, given at the state `Step` returns
(`stepClose` gives `Gout s'`; the snapshot acknowledgement's branch now closes at the state it returns).
(2) `raft.tickElection.spec` and `raft.tickHeartbeat.spec` take `Step`'s gates for their local messages
(`tickMsg`, `LemmasStepGates.lean`): `tickElection` one bundle at `s`, back `(⌜s' = s⌝ ∗ R.G) ∨ Gout s'`;
`tickHeartbeat` the quorum check's bundle at `s` under `s.cq = true` ending in `Gm`, `"Hskip"` (`R.G ={⊤}=∗
Gm s`), and the heartbeat's bundle produced from `Gm s1` at the state `s2` after the transfer abort
(`∃ R2`), back `(∃ s1, … ∗ Gm s1) ∨ Gout s'`; untraced instances `raft.tickElection.untraced`,
`raft.tickHeartbeat.untraced` (`TracedUntracedTick.lean`, from `untracedR`/`stepBundle_none`), which
`RawNode.Tick` takes. (3) `appliedTo`'s premise narrowed to its automatic leave (`c.autoLeave = true →
s.gh.tr = none`), `Step`'s acknowledgement premise with it; `appliedSnap` keeps `s.gh.tr = none` (P2).
No ghost change; no client-visible change; no axiom or `sorry`. **Finding (piece 2):** a traced caller's
last gate leaves the capability in a phase about the TLA server after the whole handler, i.e. about the
state raft will reach, which raft reaches only after mutations that follow the hook (vote record,
progress update, commit); the closing wand learns only `StepCD … s recv s'`, a relation that does not
pin `s'`, so `Gout s'` cannot be produced. **Next (piece 2, recommended):** give `stepClose` the code's
exact end state on the traced paths (`StepEnd c id m ents s s'`, per type and role in the gates' own
states, `True` on untraced types; each branch lemma passes it to `gate_close`); then state
`raft.Step.traced` with `trCapB … (fun C => SimIdle C s)` in and `SimIdle C s'` out, the token of the
received message, and the node's premises (`TrOk`, `termLB`, `readyFits`), and build its gates per path
(`trCapB_hookGate*`, a receive-line gate from `trCap_fire_recv` still to write, `lineEffect_*`, the
`FxPres*` facts from raft's ghost); then the ticks' traced corollaries over it and the node API. Checked (branch at its base `8ebee7832f` plus this slice): full `lake build` green (13788 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in four proof files only (`raft__Step`: `Gout` at the end state and the narrowed acknowledgement premise; `raft__appliedTo`: its premise; `raft__tickElection`, `raft__tickHeartbeat`: their gated specs); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 13), 2026-11-10 (branch `trace-check-q8s13`): `Step`'s closing wand learns the
end state; the receive line's gate; the traced bundle stated; the broadcasts block it.** Decided by the
agent (`notes/decisions.md`, "Q8 stage 1 (slice 13)"). Done: (1) **`StepEnd`** (`LemmasStepGates.lean`):
`stepClose` (now `… m ents ctx s R Gout`) receives, traced, the code's end state on the types a traced node
steps (`StepEndTy`): a stale message's (`LowSend`), `hup`'s (`HupOkC`), a vote request's answer at
`preState` by the code's decision (`VoteGrant`, `VoteEnd`; the lease only at `s.cq = true`), else the
role's step function's result at `preState s m pvs` (`StepFnEnd`); every branch lemma returns it
(`"%Hend"`) and the dispatch passes it to `gate_close` (`end_ty` for the other types); statements of
`raft.Step.untraced`, the ticks' untraced instances, `appliedTo` and the node API unchanged. (2)
**`trCapB_hookGateRecv`** (`TracedRecvGate.lean`): the receive hook's gate from the capability, traced by
`trCap_fire_recv` (`PhaseStepR`, `FxPresRT`, the token `recvTok`), untraced from the nil logger. (3)
**`stepBundle_traced.statement`** (`TracedRaftStep.lean`, a definition): the traced counterpart of
`stepBundle_none`, the capability idle at `s` and the message's token (`recvTokOf`) with the node's
premises (pre-vote and check-quorum off, `StepEndTy`, the term bound, `MsgTrOk`, the receipts' fit) giving
`Step`'s gates and a closing wand ending in the capability idle at `s'`; with `raft.Step.spec` it is
`raft.Step`'s traced triple. **Finding (not derivable on the broadcast paths):** a send line adds its
message to the node's pending share, which `SimIdle` equates with the outbox; a broadcast's per-message
gates are persistent from a fixed state and the step functions give the queued messages only as a
relation (`ReplSends`, `HupOkC`), so the closing wand cannot tie the share to the outbox (`MsgBeat`,
`MsgProp`, an accepted or rejected `MsgAppResp` and `MsgHeartbeatResp` at a leader, a won `MsgVoteResp`,
`MsgHup`). **Next (recommended, raft-internal):** index the broadcasts' gate resources by the messages
queued so far, from `send` up through the broadcast functions, `campaign`/`hup`, `becomeLeader`, the
step functions and `StepG`, so that `StepEnd` names the same `ms`; meanwhile the bundle's single-reply
paths (a follower's or candidate's `MsgApp`/`MsgHeartbeat`, a vote request's answer, stale messages, a
vote response without a win, the ignored types) can be proved path by path from
`trCapB_hookGateRecv`, `lineEffect_*` and the `FxPres*` facts; then the ticks' traced corollaries over
the bundle. Not started: any path's proof (piece 3), the ticks' traced corollaries (piece 4). Checked (branch at its base `b21eeb5bd5` plus this slice): full `lake build` green (13789 jobs; `TracedRaftStep.lean`, added during it, built after); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in three proof files only (`raft__Step`, `raft__tickElection`, `raft__tickHeartbeat`: `stepClose`'s new `ents ctx` arguments); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 14), 2026-11-10 (branch `trace-check-q8s14`): the gates' resources indexed by the
outbox; slice 13's broadcast blocker removed; the traced bundle's paths not yet proved.** Decided by the
coordinator (the indexing) and the agent (its form) (`notes/decisions.md`, "Q8 stage 1 (slice 14)").
Done (task 1): every function that may queue messages its caller cannot predict takes the caller's
resource as a family over raft's abstract outbox (`G : List Msg → IProp`; precondition `G s.outbox`, a
send's gate from `G o` to `G (o ++ [mm])`, postcondition at the returned state's outbox): `sendHeartbeat`
(`Q` by the commit), `bcastHeartbeat(WithCtx)`, `maybeSendAppend`, `sendAppend`, `bcastAppend`,
`sendMsgReadIndexResponse`, `releasePendingReadIndexMessages`, `handleAppendEntries`, `campaign`, `hup`,
`stepFollower`, `stepCandidate`, `stepLeader` (and their internal lemmas), `StepG` (`G0`, `G1`, `GE`,
`Gp2`, `Gc` families), `stepOut R o`, `stepClose` at `stepOut R s'.outbox`; two pure side conditions,
`IdxFree` (untraced: the family ignores its index, for `maybeSendAppend`'s snapshot fallback and the
`MsgSnap` arms, untraced only) and `PermInv` (order-insensitive, for `campaign`, whose result orders its
messages its own way), passed to `Step` as `stepGates`' conjunct `StepGOk`. Every untraced instance keeps
its statement (constant families); `raft.Step.spec`, the tick specs, the node API and `Link.lean`
unchanged. **Not done:** task 2, `stepBundle_traced` path by path (single-reply paths, then broadcasts),
and task 3 (`raft.Step.traced`, the ticks' traced corollaries). What task 2 now needs beyond the gates'
own laws (`trCapB_hookGate*`, `trCapB_hookGateRecv`, `lineEffect_*`, the `FxPres*` facts): the traced
families defined as "the capability with its share's pending list the outbox's traced messages", up to
order for `GE` (`PermInv`), and a **share re-ordering law** (`simNode`'s list permuted under `simInv`,
which reads it as a bag) for the closing wand to reach `SimIdle`'s exact `P = pendAbs C (toPState
s').outbox` after a campaign. Checked (branch at its base `7640e3e1e9` plus this slice): full `lake build`
green (13790 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53
collections `--reuse --check`, none updated; `interface/` differs in the fourteen changed specs' proof
files only (their gates and resources); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py
--raft` unchanged.

**Q8 stage 1 (slice 15), 2026-11-10 (branch `trace-check-q8s15`): the traced families and the share's
re-ordering; `stepBundle_traced` by paths, the local no-line paths proved; every receive-line path
blocked on the frozen `FxPresR` (Q14).** Decided by the agent (`notes/decisions.md`, "Q8 stage 1 (slice
15)"). Done: (1) **the families** (`TracedFamilies.lean`): `PhaseAt Φs o` (the server in `Φs`, the share
a permutation of `pendAbs C o`), `trFam` (`PermInv`, unchanged by untraced messages), `SimIdleS` (the
idle relation's server part, outbox-free); **the re-ordering law** `trCapB_perm` (checked: `simInv`
reads a share's list only as a bag and by membership), `trFam_idle`, `trCapB_monoΛ`, `trCapB_pin`. (2)
**The statement by paths** (`stepBundle_traced.on Path`) with what slice 13's statement lacked: local
messages at term zero, `MsgHup` not at a leader, `TrNoSnap`, a traced message's `To` the node, and the
last-event predicate given back as `stepLastEv Λ`. (3) **Proved**: `stepBundle_traced_localNoLine`
(`MsgBeat`/`MsgProp` at a non-leader; `TracedRaftStepPaths.lean`), the template for the rest (one
family `R`, guards discharged, `StepEnd` read at the close, the share re-ordered). **Blocked**: every
path of a traced type: its receive line's `FxPresR` (frozen) quantifies over arbitrary phantom replies
`Pph` that no phase or premise pins, so its facts are not provable (Q14, recommended: the phantoms a
function of the receiving server). **Not done, unblocked**: the local paths with lines (`MsgHup` at a
non-leader, `MsgBeat`/`MsgProp` at a leader: `FxPres`/`FxPresU` per line, the share pinned by
`trCapB_pin`); then the ticks' traced corollaries; `raft.Step.traced` is the bundle with
`raft.Step.spec` (slice 13), nothing to add until the bundle holds on every path.

**Q8 stage 1 (slice 16), 2026-11-10 (branch `trace-check-q8s16`): a send line's phase step; the
local paths with lines blocked on the frozen `simFx`'s `MsgsUniq` (Q15).** Decided by the agent
(`notes/decisions.md`, "Q8 stage 1 (slice 16)"). Done: `phaseStepB_send` (a send line's phase step at
the idle server, `PhaseAt (SimIdleS · s)` from `o` to `o ++ [m]`), its heartbeat instance
`phaseStepB_heartbeat` (at the exact commit), `msgAbs_source` (`TracedRaftStepPaths.lean`).
**Blocked**: `MsgBeat` at a leader, `MsgHup` at a follower or candidate, `MsgProp` at a leader, and so
the ticks' traced corollaries: each sends, and no send line's `FxPres` is provable, since `simFx`'s
`MsgsUniq` is not re-established for a new message (nothing in `simFx` fixes the fields a receive line
does not log; a counterexample `σ` for the heartbeat; Q15, recommended: a shape clause in `simFx`, with
amendment A2). Also found (raft-internal, recommended, not done): `"#Hgbeat"`'s heartbeat commit only
bounded (`sendHeartbeat`'s gate), the line needs `min(committed, Match)` exactly; `"#Hgpapp"`'s append
requests lack `Match ≤ Index` (`lineEffect_msgApp`'s `hmatch`). **Not done,
unblocked**: the node lines' facts (`BecomeCandidate`, `Replicate`, `Commit`: `FxPresU`) and the other
send lines' phase steps.

**Q8 stage 1 (slice 17), 2026-11-10 (branch `trace-check-q8s17`): the heartbeat gates at the exact
commit; the append gates with `Match ≤ Index`; each send line's needs checked.** Decided by the agent
(`notes/decisions.md`, "Q8 stage 1 (slice 17)"). Done: (1) `sendHeartbeat`'s gate given `cm =
min(committed, Match)` exactly, carried through `bcastHeartbeat(WithCtx)`, the read-index heartbeats and
`stepLeader`'s `"#Hgbeat"`/`"#Hgrihb"`/`"#Hgrlhb"`; (2) every `MsgApp` gate (`maybeSendAppend`,
`sendAppend`, `bcastAppend`, `"#Hgcast"`, `"Hgxapp"`, `"#Hgpapp"`, `"Hgsapp"`, `"#Hgaapp"`) given the
destination's `Match` at most `mm.index`, from raft's own invariant `Match < Next` added to `PrOk`
outside `StateSnapshot` (where `BecomeSnapshot` may break it); (3) `phaseStepB_msgApp` and `appOk_slice`
(`TracedRaftStepPaths.lean`): the append line's phase step from the gate's facts. **Found, not taken
(the traced bundle's premises, next slice)**: the heartbeat and append lines need the destination a voter
(`to ∈ c.incoming`), which needs `c.learners = ∅` at a traced node (no raft invariant; a premise like
`TrNoSnap`) with `domSet s.progress = c.voters ∪ c.learners` (`ownRaftPhysC`); the append and vote-request
lines need their log term below `2^63` (raft's ghost `TermsLe`, held by the caller's family, not by the
gate or `SimIdleS`). The vote request, self-vote, self-acknowledgement and reply lines need nothing more
from their gates (their messages and states are named). Still blocked on Q15 (every send line's
`FxPres`) and Q14 (receive lines). Checked (branch at its base `98ca21bb96` plus this slice): full `lake build` green (13792 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in `Defs` (`PrOk`'s conjunct, `PrOk.fields`/`maybeUpdate`'s new premises, `PrOk.match_le_prev`) and the ten changed specs' proof files (their gates); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 18a), 2026-11-10 (branch `trace-check-q8s18a`): the local paths that log lines;
`MsgBeat` at a leader and `tickHeartbeat`'s traced corollary proved; `MsgHup` blocked on `hup`'s
non-exclusive result (raft-internal), `MsgProp` on where its records are created.** Decided by the agent
(`notes/decisions.md`, "Q8 stage 1 (slice 18a)"); the receive paths are slice 18b's. Done: (1)
`stepBundle_traced.on` gains `c.learners = ∅` and `domSet s.progress ⊆ c.voters ∪ c.learners` (the
heartbeat's and append's destination a voter); the log-term bound is not a premise (raft's ghost state in
the families gives it, `ownRaftGhost_terms_le`). (2) `TracedPin.lean`: a local path's family `lineF`
(raft's ghost state, `trFam`, the new messages' numbers `OutOk`), `lineF_recv`, `lineF_close`; the
pin/unpin pair `trFam_pin`/`trFam_unpin` (`PinAtG`); `hookGateOpt_mono`, `sendOutGate_one`; `app_lead`
(`fxPres_app`'s `hlead`); `AppSlices`' preservation (`appSlices_mono`, `appSlices_becomeLeader`,
`appSlices_extend`). (3) `TracedRaftStepLocal.lean`: `lineF_heartbeat`, **`stepBundle_traced_beat`**
(`MsgBeat` at a leader), **`raft.tickHeartbeat.traced`** (check-quorum off: no quorum check). **Blocked
(raft-internal, recommended, not done)**: `MsgHup`'s close cannot exclude the candidate family at `s' =
s` (`HupGuard` not exclusive; `hup`'s result `(⌜s' = s⌝ ∗ G0) ∨ G s'.outbox`): `"Hgbc"` premised by the
campaign's conditions and `HupGuard` exclusive; so `tickElection`'s corollary waits too. **Open
(design)**: `MsgProp`'s append requests need records of the proposed entries, which the families' ghost
state (at `s`) lacks; where they are created is to decide. Unblocked, not done: the `BecomeCandidate`,
vote-request and self-vote lines' facts and phase steps; `Commit`, the self-acknowledgement.

**Q8 stage 1 (slice 18b), 2026-11-10 (branch `trace-check-q8s18b`): the receive paths of the traced
types; stale messages, ignored responses and a same-term vote request proved; heartbeats and appends
blocked on the bundle's missing message facts.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1
(slice 18b)"). Done (`TracedRaftStepRecv.lean`): the common pieces of every receive path (`recvLine_pred`:
a receive event's parse matches its message; `recvEvTy_of`; `recvGate_traced`: the receive hook's gate
from `trCapB_hookGateRecv`, framed; `trCapB_pinDir`: the share pinned with its trace directory, so the
token's voters are the capability's; `ownStepGhost_traceOk`: the commit and last index below
`traceNumBound` from the receipts' fit; the step functions' gates at `False` or type-refuted resources),
and three path sets of `stepBundle_traced.onR` (`.on` with two premises found needed, stated as
hypotheses for the coordinator to fold in: `s.role ≠ .preCandidate`, and `TrRecvShape m ents`: a
heartbeat without entries, a heartbeat response not rejecting, a vote request not from its destination):
**`stepBundle_traced_staleRecv`** (a lower-term message of a traced type: the phantom refusal of a
request, `fxPresR_staleReq`, the drop of a response, `fxPresR_staleResp`), **`stepBundle_traced_ignResp`**
(a response a role does not handle at the node's term: `respSrv`, `simFx_resp`, `specInv_respSrv`), and
**`stepBundle_traced_voteReq`** (`MsgVote` at the node's term: the receive line's `HandleRequestVoteRequest`
with raft's decision the specification's, `voteGrant_iff`, `voteEnd_simIdle`; the answer's send line
skipped, `phaseStepB_skip`, `fxPres_skip`, `skipGate_vresp`). **Blocked (bundle statement, recommended:
a premise)**: a follower's or candidate's `MsgHeartbeat`/`MsgApp` raise the commit index in the receive
line's effect, and the receiver's `srvFacts` then need `isCommitted`/`commitIn` at the raised index, which
come only from raft's own message facts (`isMessage`: the heartbeat's `leadFull`/`commitIn`/`isAcked`,
the append's `leadPrefix`/`commitIn`; `commitIn_move`), which `raft.Step.spec` has (`#Hmsg`) and the
bundle does not take: recommended, `stepBundle_traced.on` takes `isMessageC γ (absMsg ty m ents ctx)`
(persistent, from `isRaftMsg`) for a traced type. **Not done, unblocked**: a higher-term message (the
receive line's `UpdateTerm` changes the receiver's term: its `srvFacts`' `commitIn` at the new term, from
raft's ghost; then the preamble's `BecomeFollower` line, skipped by `bfCond`); a candidate's
`MsgVoteResp` without a win or loss (the tally: `SimServerR`'s candidate clause after `recordVote`); the
broadcasts (leader `MsgAppResp`, `MsgHeartbeatResp`, a won `MsgVoteResp`). Checked (branch at `trace-check` `96a2599b67` plus this slice): full `lake build` green (13796 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` unchanged (the new module is not on `etc/api/raft.txt`); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 19b), 2026-11-10 (branch `trace-check-q8s19b`): the bundle's premises folded; a
follower's `MsgHeartbeat` proved; the vote tally blocked on a missing uniqueness invariant (Q17).**
Decided by the coordinator (the premises) and the agent (their form, the rest) (`notes/decisions.md`, "Q8
stage 1 (slice 19b)"). Done: (1) `stepBundle_traced.on` takes slice 18b's `s.role ≠ .preCandidate` and
`TrRecvShape` (`onR` dropped; the shape now also `From ≠ To` for an append request and a heartbeat),
the received message's `isMessageC` (beside its token) and, found needed, `m.Type' = MsgHeartbeat ∨
MsgApp → γ.reBoot ≠ []` (the specification's heartbeat handling needs a commit index past `0`); where
the node API gets each is recorded (raft's `ownRaftPhysC_precand`; `isRaftMsg`'s `SentMsgShape`, to be
extended by the two heartbeat clauses; `isRaftMsg`'s `isMessageC`; the cluster's bootstrap log). (2)
**`stepBundle_traced_folHb`** (`TracedRaftStepRecvHb.lean`): a follower's `MsgHeartbeat` of its term,
the commit raised with the heartbeat's certificates moved to the receiver's log without changing raft's
ghost state (`ownRaftGhost_hbFacts`), the specification server's recorded log identified with raft's
(`log_eq_of_abs`), the response's send line skipped. **Blocked (Q17, recommended (a), an amendment
A3)**: a candidate's `MsgVoteResp` (raft records a voter's first response only, the specification every
granting one; no invariant excludes a second response). **Not done, unblocked** (exact items in the
decisions entry): a candidate's `MsgHeartbeat` (the two-round receipt, `ReturnToFollowerState`, and the
`BecomeFollower` line skipped by `bfCond`, which needs the receive event kept as the last event), a
follower's `MsgApp` (rejected: `hlt0` from the message's facts; the hint is irrelevant, `msgAbs` drops it;
stale: log matching below the commit from the ghost; accepted: the new log's records and certificate and
`QuorumLogF` under a truncation/append, no lemma yet), a higher-term receive (`UpdateTerm`'s first
round, `commitIn` at the new term by `commitIn_agree`, `LeaderComplete` for `specInv_updateTerm`, the
preamble's `BecomeFollower` line skipped), the leader's `MsgAppResp`/`MsgHeartbeatResp`. Checked (branch at `trace-check` `bb336f50f2` plus this slice): full `lake build` green (13797 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s, unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` unchanged (regenerated: no file differs; the changed modules are not on `etc/api/raft.txt`); `etc/api-check.py` 0 errors; `--layout` 0 new; `etc/gen-link.py --raft` unchanged.

**Q8 stage 1 (slice 19a), 2026-11-10 (branch `trace-check-q8s19a`): `hup`'s result exclusive;
`MsgHup` at a follower or candidate and `raft.tickElection.traced` proved; `MsgProp`'s records
decided.** Decided by the coordinator (slice 18a's option (a)) and the agent (the rest)
(`notes/decisions.md`, "Q8 stage 1 (slice 19a)"). `HupCampaigns c id s` names the campaign's
conditions; `HupGuard` is exclusive (`(¬HupCampaigns ∧ s' = s) ∨ (HupCampaigns ∧ ∃ pre …)`, a
pre-campaign only with pre-vote on); `"Hgbc"` (in `hup`'s spec and `hupGates`) is premised by
`HupCampaigns`; untraced, `RawNode`, node and tick statements unchanged. `TracedRaftStepHup.lean`: the
`BecomeCandidate` line (`phaseStepB_becomeCandidate`, `fxPres_timeout`), the vote request and self-vote
(`phaseStepB_campMsg`, `fxPres_plain`), `stepBundle_traced_hup`, `stepBundle_hup_R`,
`raft.tickElection.tracedTriple`/`.traced`; both ticks now have traced corollaries. **`MsgProp` at a
leader, decided, not proved**: the proposal's records are created by the `Replicate` lines' facts
update, `stepClose` taking raft's ghost state back at `s` or the proposal's appended state (raft-
internal; changing `ownLogGhost` would be client-visible, creating the records in `Step` would split the
ghost state it hands the caller). Left: that relaxation, the `Replicate` facts, the self-acknowledgement
(`lineEffect_selfAck`), the appends (`fxPres_app`, `app_lead`). `Commit` is not on `MsgProp`'s path (it
follows the self-acknowledgement's receipt). (The coordinator wrote this paragraph at the merge: the
branch's own plan commit had copied slice 19b's.)

**Q8 stage 1 (slice 21), 2026-11-10 (branch `trace-check-q8s21`): the bootstrap's pieces (the facts at
the bootstrap state, the bootstrap lines' gates, the capability's introduction, the idle relation after
`Bootstrap`) and the received message's premises from `isRaftMsg`; the node API's traced specs not
started, three questions (Q18-Q20).** Decided by the agent (`notes/decisions.md`, "Q8 stage 1 (slice
21)"). The harness (`examples/raft/tracecheck`) runs `raft.Node`s: `StartNode`, the node's `Tick`,
`Ready`, `Advance`, `Propose`, `ApplyConfChange` (the bootstrap entries' changes, committed in the first
`Ready`s), `Step`, `ReportUnreachable`, `Stop` (`Status`, `ProposeConfChange`, `RestartNode` and
`ReportSnapshot` unreached with `DefaultCConfig`), so the traced node API is `node.run` over the traced
`RawNode` functions. Done (raft-internal, `TracedNodeBoot.lean`, `TracedNodeRecv.lean`): `simFx_simInit`
(the facts at `simInit C` from raft's commit invariant: each voter's `srvFacts` with the bootstrap log,
`SpecInv`, `QuorumLogF`, the empty bags); `simIdle_boot` (raft's state after `Bootstrap` idle-related to
the bootstrap server, nothing pending); `nodeEvOf_init_boot`, `ccEvOf_boot` (the `InitState` and
`ApplyConfChange` lines parse as their node's bootstrap lines) and the gates `trCapB_hookGate_boot`,
`_init`, `_ccBoot` (either mode, flag unset); `trCapB_intro` (the capability from `newRaft`'s pieces);
`isRaftMsg_trRecv` (the received message's `isMessageC` and `MsgTrOk`, and `TrRecvShape`'s third
clause). **Not done, with what each needs**: the node holding the capability (a gated conjunct of
`ownRawNode`, `rnTrace`: the capability idle at the struct's state with any flag, `TrNoSnap`, and the
traced configuration's `prevote = cq = false`, no learners; `emp` untraced, so every untraced proof only
threads it), then `RawNode.Step`'s, `Tick`'s, `Ready`'s (`trCap_fire_ready`, the tokens out),
`Advance`'s (the self-addressed tokens back), `Propose`'s, `ApplyConfChange`'s (a booted node's
`ApplyConfChange` line: `lineEffect_applyCC`'s identity under `AccIdle`; no gate yet) traced triples,
`node.run`'s and the `node` API's gated statements (the tokens from `Ready` to `Step`, `recvTokOf`);
`newRaft` and `Bootstrap` traced (`traceConfChangeEvent.spec` is still untraced-only, its unified form
the `_ccBoot` gate's consumer; `newRaft.spec` sets `s.gh.tr := none`); and Q18 (a heartbeat's shape:
recommended in `Msg.TrOk`), Q19 (the bundle and ticks need the booted flag: recommended any flag), Q20
(the frozen `startTrace` lacks the capability's invariant and flag: recommended an amendment).

**Q8 stage 1 (slice 20b), 2026-11-10 (branch `trace-check-q8s20b`): a candidate's heartbeat; a
follower's stale and rejected `MsgApp`; every higher-term receive but an accepted `MsgApp` and the vote
responses.** Decided by the agent (`notes/decisions.md`, "Q8 stage 1 (slice 20b)"). Done (new modules
`TracedRaftStepRecv{Cand,App,AppRej,UT,UTResp,UTHb,UTVote,UTApp}.lean`): **`stepBundle_traced_candHb`**
(a candidate's `MsgHeartbeat` of its term: the two-round receive `ReturnToFollowerState` then the
heartbeat, raft's `BecomeFollower` line skipped by `bfCond`, the receive event kept last:
`recvGate_tracedL`, family `bfR`); **`stepBundle_traced_folAppStale`** (the stale exit; the log matching
below the commit index from raft's commit invariant, `ownRaftGhost_appStaleMatch`);
**`stepBundle_traced_folAppRej`** (the rejected exit; `index 0 → logterm 0` from the request's facts;
the rejection's hint term bounded by a raft-internal strengthening of `findConflictByTerm`'s spec and
`HandleAppResult`'s reject exit, `hintterm ≤ m.LogTerm`); the higher-term receives (`UpdateTerm`'s
first round `lineEffect_ut`, its facts `simFx_ut` with leader completeness `leaderComplete_of` and the
receiver's facts from raft's log `ownRaftGhost_logFacts`, the preamble's `BecomeFollower` skipped by
`bfCond_ut`): **`stepBundle_traced_utResp`** (`MsgAppResp`/`MsgHeartbeatResp`),
**`stepBundle_traced_utHb`** (a higher-term heartbeat carries commit `0`, `ownRaftGhost_hbHigher`),
**`stepBundle_traced_utVote`**, **`stepBundle_traced_utAppSR`** (stale or rejected). **Not done**
(exact items in the decisions entry): an accepted `MsgApp` (follower, candidate, higher term: the new
log's records and certificate, `QuorumLogF` under a truncation or append, the new last index's bound);
a candidate's stale/rejected `MsgApp` (pieces in place); the leader's `MsgAppResp`/`MsgHeartbeatResp`
(not started); the vote responses (Q17, A3). Checked (branch at `trace-check` `0db85c4212` plus this
slice): full `lake build` green (13805 jobs); `etc/tcb-report.py --check` (806 axioms, 4 `sorry`s,
unchanged) and all 53 collections `--reuse --check`, none updated; `interface/` differs in
`raftLog__findConflictByTerm.txt` only (the spec's new `t' ≤ term`; `HandleAppResult` is not in a
listed module's interface); `--check --layout` 0 new; `etc/api-check.py` 0 errors; `etc/gen-link.py
--raft` unchanged.

**Q8 stage 1 (slice 22a), 2026-11-11 (branch `trace-check-q8s22a`): Q19 (a) done; `MsgProp` at a
leader begun, the close's relaxation found to need more than slice 19a recorded.** Decided by the
coordinator (Q19 (a)) and the agent (the rest) (`notes/decisions.md`, "Q8 stage 1 (slice 22a)").
`stepBundle_traced.on` and both ticks' traced triples take the capability with any `booted` flag `bt`
and give it back with some flag (`∃ bt'`); every path's first line already takes any flag; the path
files changed mechanically (`lineF` carries `∃ b`, the path resources take the flag, the receive paths
close through `stepClose_anyB`). `MsgProp`: the self-acknowledgement's phase step
(`phaseStepB_selfAck`, `TracedRaftStepProp.lean`). Found (raft-internal): the protocol's propose state
has the self-acknowledgement queued (`proposed …`, not `propAppended`), the propose ghost update
consumes the proposal's tickets and a receipt `Step` holds (to pass through `"Hgprep"`), and `Step`'s
ghost step splits into a propose part (no later credit needed, a new `ghost_stepProp`) and the
broadcast. Left: those statement changes (`raft.appendEntry.spec`, `stepLeader.spec`, `leaderGates`,
`stepClose`, `gate_close`, `Step`'s `MsgProp` arm, every bundle mechanically), the `Replicate` lines'
phase steps and facts, the self-acknowledgement's facts, the appends' gates, the bundle.

**Q8 stage 1 (slice 22b), 2026-11-11 (branch `trace-check-q8s22b`): a candidate's stale or rejected
`MsgApp` and pending vote response done; three statement questions.** Decided by the agent
(`notes/decisions.md`, "Q8 stage 1 (slice 22b)"). Done: `stepBundle_traced_candAppSR b`
(`TracedRaftStepRecvCandApp.lean`); `stepBundle_traced.onC` (a path reading the configuration) and
`stepBundle_traced_candVoteRespPending` (`TracedRaftStepRecvVoteResp.lean`); a leader's rejected
`MsgAppResp`/`MsgHeartbeatResp` receive line (`phaseStepR_leadResp`, `fxPresR_leadResp`,
`TracedRaftStepRecvLead.lean`). Questions (each with options there): (1) the vote's loss needs `stepClose`
to know whether the step-down's gate ran (recommended: `stepOut`'s `G1` guarded by `¬ Hooked`), its win
the close relaxation slice 19a decided for `MsgProp`; (2) an accepted `MsgApp`'s truncation does not
preserve the frozen `QuorumLogF` from the facts alone (recommended: an inductive strengthening, after a
TLC check); (3) no append gate bounds the message's `RejectHint`, which the send line's `TraceEv.Ok`
reads (recommended: `mm.rejecthint = W64 0` in every append gate's premise, raft-internal). Tasks 3 and 4
wait on (2) and (3).

**Q8 stage 1 (slice 23a), 2026-11-11 (branch `trace-check-q8s23a`): `MsgProp`'s statement changes
done; every append gate's `RejectHint`; the vote's win and loss, and `MsgProp`'s bundle, not started.**
Slice 22a's three additions (taken by the coordinator) and slice 22b's question 3 (a), their form decided
by the agent (`notes/decisions.md`, "Q8 stage 1 (slice 23a)"); all raft-internal. `stepClose` gives raft's
ghost state back at `s` (`CloseAt`: on a traced leader's proposal only if it was not appended) or at the
proposed state (`CloseMid`); the proposal's tickets, entries' data and `appendEntry`'s receipt are lent to
`"Hgprep"` (`StepG.Tp`, set by `ghostIn` to `propLend`; `raft.appendEntry.spec`'s `"Hgrep"` and
`stepLeader.spec`'s `"Hgprep"` take the receipt); `Step`'s `MsgProp` arm steps the broadcast alone from
the proposed state (`stepCD_sendApps`, `ghost_step_md0`) with the whole step's model witness
(`stepOut_of_stepCD_prop`). Every append gate's premise ends with `mm.rejecthint = W64 0`. Every close site
changed mechanically (`stepClose_of_at` with a `CloseAt` proof, then `stepCloseAt`). Left: `ghost_stepProp`
(the family's propose update, no `£`), the `Replicate` lines' phase steps and facts, the
self-acknowledgement's facts, the appends' gates (unblocked now by the `RejectHint` premise), the bundle;
the vote's loss (a guarded `stepOut` for the close) and win (the win's ghost update split, its receipt
through `becomeLeader`), each recorded with its design in the decisions entry.

**Q6's acceptance test (the user's, 2026-11-08):** the gating as Q6 proposes; done only when
every existing closed theorem (`raft_kv_porcupine_safe`, kvreconf's, kvdurable's, the server's)
keeps its statement word for word and stays proved, `etc/tcb-report.py --check` (and its
collections) shows no new axiom or `sorry`, and `interface/` differs only by the gated additions
and the untraced clients' pure fact `γ.raft.reTrace = none`. Order: the gate first (the field,
`cluster_alloc`'s argument, the pure fact), checked against this test, then each traced-only item.

**The verdict and the tokens (the user's, 2026-11-08):** the closed theorem keeps TLC's verdict
(`TraceMatched`: no branching, the invariants on every state explored), and the message tokens keep
both halves: a message is received at most once, and only after its sender's `Ready` line. The
alternative considered (existential acceptance, invariant violations pruning branches, duplication
modelled) would drop layer B's determinism proof but no longer match TLC's verdict. Why the tokens'
at-most-once premise is one etcd meets: rafthttp never resends an application message (a failed
stream write or pipeline post reports the peer unreachable and drops it: `stream.go`'s `msgc` case,
`pipeline.go`'s `handle`), and TCP never delivers a segment twice.

## The corrected model (2026-11-08, the user's request)

Asked: could the stage be resumed against a corrected `etcdraft.tla`, and what would make that worth
something? Done, as evidence for that decision (no proof work): `etc/tla-fixes/`, a ten-patch
series on raft `c51f010` (one per finding, plus 0010) with
(1) each fix judged against Ongaro's thesis and raft's documentation, none code-only
(`notes/tla-fixes-justification.md`); (2) random runs of `RawNode`s with restarts, snapshots,
configuration changes incl. demotion, loss, reordering, cut batches and campaigns, every trace
accepted (upstream's specification rejects half); (3) `MCetcdraft` model-checked with the series,
no violation in bounded runs; (4) mutation testing: ten of eleven buggy rafts rejected, both
harmless controls accepted. Two further findings came out of it:
`issues/raft-tla-restart-config-from-storage.md` (not fixed: a restart from a storage with an older
configuration) and `issues/raft-tla-bootstrap-entries-full-config.md` (fixed by 0010). Resuming
against the series would need the transcriptions (Go, Lean) to follow it, and the harness to keep
the driver's rules (`etc/tla-fixes/README.md`, "Random runs").

**PreVote and CheckQuorum (2026-11-08, the user's request):** patches 0011 (raft's trace logging:
pre-votes and lease-ignored vote requests) and 0012 (the specification, behind constants `PreVote`
and `CheckQuorum`, `FALSE` by default; TLC checks that with both off it takes only the steps of
0010). With them random runs with either or both on are accepted (without them, 20 of 20 and 19 of
20 rejected), model checking with both on finds no violation, and five of six mutants of the new
rules are caught (`etc/tla-fixes/README.md`, "PreVote and CheckQuorum"). So a conformance theorem
can cover etcd's configuration.

**The user's answers on resuming (2026-11-08):** Q5 is settled by the series (0006 is option (b)).
Q6: add the premises the proof needs, gated on a traced cluster so that the existing proofs keep
their statements (to be redrafted against the corrected specification and shown side by side
before they go into Lean). Q7: the user proposes a relational acceptance (a per-line chain of
states witnessing TLC's search, no fuel) in place of the executable `checkTrace`, which would stay
as an untrusted test tool; not yet decided whether to resume Prove against the series.

## Decisions (the user's, 2026-11-08)

- **Fully closed**, as the porcupine examples: `Main` runs the concurrent harness, then the
  checker on the recorded trace, and panics unless the checker accepts; the theorem is adequacy:
  no execution of `initialize'(); Main()` panics.
- **The direct checker** (`CheckTrace`'s search) is the one verified, not porcupine (the trace is
  totally ordered: porcupine's search reduces to it). Porcupine stays a cross-check outside the
  proof.
- **TLC's verdict, invariants included**: the checker accepts only when some behavior of the trace
  specification steps through every line, the search never branches (TLC's `TraceMatched`), no
  evaluation fails, and every state reached satisfies the eight invariants of
  `Traceetcdraft.cfg`.
- **Not tied to the workload**: the facts about raft are proved once, under premises on how the
  application uses raft; only the harness's layer is about its workload.
- **The raft verified is its `with_tla` build** (the trace hooks' bodies), translated from the local
  fork commit `e8f9566` (`etc/fork-patches/`) until it is pushed.

## The gates, delegated (the user's, 2026-11-08)

`notes/spec-first-plan.md`'s order stands (Draft, Review, Test, Probe, Freeze, Prove; no proof
before the freeze), with the user's gates delegated to the agent for this stage:

- **Review** is run by the agent: fresh `spec-reviewer` rounds on the Draft until a round leaves
  nothing first-tier, each repair followed by another round.
- **Freeze**: when Review is clean (and Test and Probe done), the agent freezes: the annotated tag
  `trace-check-frozen` on the frozen commit, recorded here as "frozen by the agent under the
  user's delegation", with the round that cleared it; then Prove.
- **Still the user's**: pushing anything (the fork commit, the branch) or any other action outside
  this repository; a change to the trust base (a new axiom or model assumption, the transcription
  trusted) or to the closed theorem's statement (dropping an invariant, narrowing the workload).
  The agent records such a question in "Questions for the user" below, takes the plan's
  recommendation where it has one (marked "taken by the agent, pending the user's veto"), and
  goes on with the work that does not depend on it; it does not stop for them.
- Every other decision the agent takes is recorded where it is taken, "decided by the agent",
  with the options and the reason (`notes/spec-first-plan.md`, "Who decides").

## Questions for the user

- **Q1 (2026-11-08, S3): a new premise on raft's constructors.** `NewRawNode`, `StartNode`,
  `RestartNode` (and the internal `newRaft`, `setupNode`) take `TraceLoggerOk cv.TraceLogger'` as
  their last premise (the configuration's trace logger satisfies the logger contract; in increment
  1, `TraceLoggerOk tl := tl = nil`), discharged for a nil logger (every client today) by `rfl`.
  Alternatives: a second constructor spec (a spec family, forbidden), or the premise hidden in
  `ConfigValid`. Taken by the agent, pending the user's veto: the premise
  (`notes/trace-validation-hooks.md`). Its consequences (done, 2026-11-08): the examples'
  configuration predicates (`kvreconf`'s `CfgOk`, `kvdurable`'s `kdCfgOk`) gain the conjunct; the
  etcd server's `rnStartCfg` gains the field `traceLogger`, so `bootOk` (`NewServer`'s premise on
  `bootstrap`'s result, a premise of an exported result) says it too: true of the code
  (`raftConfig`, `bootstrap.go`, sets no trace logger).
  Review round 1 of S4 (S6): increment 2 replaces `TraceLoggerOk` by `isTraceLogger γt tl`, an
  `IProp` with a ghost name, so `StartNode`'s premise changes again (inside the triple, `γt` a new
  binder; Q6), while `RestartNode` keeps `TraceLoggerOk` (S4 rounds 10-11); whether to take
  increment 2's shape now is open in `notes/trace-validation-sim.md`.
- **Q3 (2026-11-08, S4 review round 1): two changes to the harness `Main` runs.** Without them the
  closed theorem is false: (F1) the harness sent a `Ready`'s messages before `Advance`, and since
  raft logs the `Ready` only after handing it out (`traceReady` ends `acceptReady`, which runs
  after the hand-off), a receipt could be logged before its sender's `Ready` line, which the trace
  specification cannot follow (witnessed by the reviewer with a sleep in the window); now it sends
  them after `Advance`, which the run loop takes only once `acceptReady` has returned. (F3) Goose's
  semantics ignores delays, so it allows unboundedly many elections, each appending an entry, and
  a batch cut by `MaxSizePerMsg` (1 MiB) carries a commit index past its last entry (gap 5): now
  `MaxSizePerMsg` is unlimited. Both narrow nothing the specification can check (the old send
  order's extra behaviors are the ones it rejects; an unlimited batch is raft's `noLimit`), and
  `Main`'s workload is otherwise unchanged. Alternatives: raft's instrumentation changed to log the
  `Ready` before the hand-off (a fork change beyond the build tags), for F1; none for F3 short of a
  proof bound on elections. Taken by the agent, pending the user's veto
  (`examples/raft/tracecheck/concurrent.go`; the tests pass, 10 seeds, and the reviewer's F1
  witness passes with the change; `nonissues/raft-trace-ready-logged-after-handout.md`).
- **Q4 (2026-11-08, S4 review round 2, N1; decided by the user: (b)): the closed statement is false as planned:
  `LeaderCompletenessInv` is not an invariant of raft, nor of `etcdraft.tla`.** A stale leader (no
  check-quorum: it keeps leading its term until it hears of a later one) lacks an entry committed
  in a later term (`notes/raft-trace-validation.md`, item 7; `gaps_test.go`,
  `TestGap7LeaderCompleteness`; TLC: "Invariant LeaderCompletenessInv is violated"). Message
  delays alone reach it, so no harness excludes it, and `Main` with the invariants checked can
  panic. Options: (a) check the other seven invariants only (the checker's `invariants` list, Go
  and Lean, and the statement's meaning: upstream's `Traceetcdraft.cfg` minus one); (b) correct the
  invariant's guard in both transcriptions (a leader of a term at least the committing server's,
  `currentTerm[l] >= currentTerm[i]`: the transcription then departs from upstream's text there, a
  trust question; the corrected invariant not yet checked on traces or proved); (c) turn
  check-quorum on (a stale leader then steps down; not modelled by `etcdraft.tla`, so it brings
  its own gaps). **Not taken** (no recommendation in the plan; the statement's and the trust
  base's). The agent's recommendation: (b) if the corrected guard survives the traces and a
  review, else (a); either way, report item 7 upstream (the user's: outside this repository).
  Evidence for (b) (2026-11-08, a scratch copy, not committed): with the guard
  `vl.CurrentTerm > entry.Term && vl.CurrentTerm >= s.S[i].CurrentTerm` in the Go transcription,
  `TestGap7LeaderCompleteness`'s trace is accepted and 30 concurrent seeds and the deterministic
  traces still pass; the argument: every committed entry server `i` knows was committed at a term
  at most `currentTerm[i]`, and a leader of a term at least that holds it (leader completeness,
  or it is the committing leader).
  TLC on `etcdraft.tla` itself (2026-11-08, scratch, not committed: upstream's `MCetcdraft` with
  three servers, `MaxTermLimit = 4`, `RequestLimit = 2`, no reconfiguration, each invariant alone):
  **inconclusive**. Breadth-first, 20 minutes reached depth 16 (61 million distinct states) for
  both without a violation; random simulation (depth 80), 20 minutes, about 5.6 million traces
  each, found none for either, **the original included**. So at these bounds TLC does not reach
  item 7's violation (a stale leader needs a partition-like schedule: an election in a later term
  and a commit while the old leader hears nothing), and the run says nothing for (b). A
  conclusive check needs a directed model (the witness's schedule as a constraint, then the
  corrected invariant checked around it) or the proof; the traces' evidence above stands.
  **Decided by the user (2026-11-08): (b)**, with a fallback: if the repaired invariant blocks a
  proof, drop it (option (a)) and document why. Done the same day: both transcriptions check the
  guard `currentTerm[l] > entry.term /\ currentTerm[l] >= currentTerm[i]` (`invariants.go`,
  `Tla/Invariants.lean`), `TestGap7LeaderCompleteness` now asserts the trace accepted (the stale
  leader still there), and `TestAgainstTLC` runs TLC on raft's `tla/` with the same one-line repair
  (`repairedSpec`, `check_test.go`). Evidence gathered for the decision: upstream raft v3.7.0 built
  with `with_tla` and validated by upstream's unmodified `Traceetcdraft` fails on this run (TLC:
  `Invariant LeaderCompletenessInv is violated`, at `main` `c51f010` too); TLC's counterexample,
  replayed against `MCetcdraft` alone from its `Init` with every step a `Next` step, reaches the
  violation (so the specification itself admits it, within `MCetcdraft.cfg`'s bounds), and its
  final state satisfies (b) (so (b) is strictly weaker on reachable states). Upstream has it
  already: etcd-io/raft#549 (open, found from the specification alone, proposing (b) without the
  entry-term condition); our report with the implementation-level test:
  `issues/raft-tla-leader-completeness-stale-leader.md`. Why (b) should hold (a commit is learned
  only in or after its term; every `commitIndex` update checked) and where it is least certain
  (single-server reconfiguration, which `Main` does not do; `etcdraft.tla`'s `BecomeLeader` does
  not set `pendingConfChangeIndex` as raft's `becomeLeader` does): `notes/decisions.md`, "Q4:
  `LeaderCompletenessInv` repaired".
- **Q5 (2026-11-08, S4 review round 2, N2): three voters do not exclude gap 6.** A leader's own
  `MsgVote`, delayed past its first heartbeat to a voter, is refused by raft (`lead != None`) and
  granted by the specification (`TestGap6ThreeVoters`; TLC rejects at the same line), so `Main`
  can panic. Options: (a) the harness's network delivers each link's messages in order (FIFO per
  sender-recipient pair; drops and delays stay, reordering only across links): with three voters a
  voter then hears of a leader only after the leader's `MsgVote`; (b) add raft's `lead` to the
  specification's vote condition (the transcriptions depart from upstream's text: a trust
  question). **Not taken** (no recommendation in the plan; (a) narrows the workload, (b) changes
  the trusted transcription). The agent's recommendation: (a), with the argument proved in layer B
  as premise P9 restated ("a voter learns of its term's leader only after the leader's
  `MsgVote`, or not at all").
  Evidence for (a) (2026-11-08, a scratch copy, not committed): a per-link FIFO `send` (one
  goroutine per link, delays and drops kept) passes 20 concurrent seeds (weak: random runs did not
  reach N2 before either; the argument is what counts).
- **Q6 (2026-11-08, S4 rounds 3-4; to present with increment 2's draft): new client-owned ghost
  on raft's node API, gated on a traced cluster (`γ.raft.reTrace = some γt`).** The simulation needs (1) a token per
  handed-out traced message (`Advance`'s post gives them, `Node.Step` takes one,
  given back on a timeout), (2) a proposal budget (`Propose` takes a credit; the leader's
  inflights then never fill, P5), (3) `isTraceLogger γt …` in the constructors' premise (Q1's
  final shape), (4) since round 5: each message token's position on its link (P9 through the
  FIFO network, if Q5 (a)), and gated premises on the constructors for layer B's other
  premises (the configuration, no `RestartNode`, no `ProposeConfChange`, each `StartNode` with its
  node's piece of the allocation and the allocation's peers), (5) since round 6: an exclusive
  per-link cursor for the tokens' order, a compaction permit never handed out, the budget's gate
  (non-empty data), no `TransferLeadership`/`ReadIndex`/`Campaign`/`ForgetLeader`
  in a traced cluster, (6) since round 7: the allocation law's premises `|peers| ≤ 3` (P9's voter
  count) and a non-`dup` cluster, the compaction permit as a gated conjunct of the storage bound
  `storBnd`, (7) since round 8: the gate a cluster field `reTrace` of raft's names (as `dup`, so
  untraced clients need no witness), and with it, `Ready`'s snapshot empty, (8) since round 9:
  `storBnd` exempting `c = 0` (the gated conjunct `⌜c = 0 ∨ γ.raft.reTrace = none⌝`), `StartNode`
  tying its logger to `reTrace`, `RestartNode` taking an untraced cluster and keeping its
  nil-logger premise, the allocation in three steps (`cluster_alloc` under
  `tr.isSome → |peers| ≤ 3 ∧ ¬dup ∧ boot ≠ []`, conditional since every client shares it, its
  post gaining `γ.raft.reTrace = tr`), raft's `reNoSnap` mode revived as `reTrace.isSome`. Untraced clients (every
  existing one) carry one new pure fact, `⌜γ.raft.reTrace = none⌝`, from a law raft exports; the
  exported `memStorage_isStorage` gains it as a premise. The spec skill makes each the
  user's; **presented side by side with the current specs in `notes/trace-validation-q6.md`**
  (2026-11-08; drafts, not yet in Lean; the design: `notes/trace-validation-sim.md`, "Increment 2").
- **Q7 (2026-11-08, layer C review rounds 1-2, S1): the Lean transcription's per-line fuel.** The
  Lean `stepLine` stops when `lineFuel` runs out (the logs' lengths plus 8); the Go's loop is
  unbounded. They agree only if a line's search never needs more, which rests on a reachability
  invariant of the specification (one leader's append requests in a term agree), itself needing
  persistence reasoning (`Restart`) and holding for any initial roles. Options: (a) S6 proves that
  invariant; (b) both checkers raise an evaluation error when the fuel runs out (the Go gains the
  same counter), so they agree by construction, and layer B shows the fuel suffices on `Main`'s
  traces (S4 already argues each receive line's loop ends); this changes the transcriptions'
  meaning, conservatively (a trace needing more is rejected, where TLC would go on): a trust
  question. (c) (layer C review round 3) a closed-form fuel: the steps that stay on a line (`UpdateTerm`,
  `ReturnToFollowerState`, the two conflict handlers) change only the destination's term, role,
  vote and log, each over finitely many values computable from the line's start, and each round
  adds a new visited state, so a count of those combinations bounds the Go's rounds; S6 then needs a
  local lemma and a counting argument, no reachability invariant, no Go change, no new rejection
  (the transcription is then exactly TLC's search); it still changes `lineFuel`'s definition, which
  `traceAccepts` is written in terms of. **Not taken** (no recommendation in the plan); the agent's
  recommendation: (c), else (b).
- **Q8 (2026-11-09, S5 Draft): the trace mode in raft's node state, and the hook paths' specs.**
  A traced cluster's logger is non-nil, so the hooks fire the simulation's update, which needs
  resources (the node's share, the phase) that only the functions between an entry point and a
  hook can thread. Raft's physical predicate fixes the logger to nil (`ownRaftPhysG`'s `Htl`,
  `TraceLoggerOk`), and every internal spec is stated on it (814 occurrences, 142 files). Options:
  (a) a field `tr : Option GName` in `NState` (the cluster's trace directory, constant, like `cq`):
  `Htl` becomes `TraceLoggerOkS s.tr tl` (nil when `none`, unconstrained when `some`), so every spec
  off the hook paths stays as it is (its `s` carries the mode through `{ s with … }`), and the
  specs of the functions on the hook paths (the call graph from the entry points to the hooks:
  about 35, `notes/trace-validation-sim.md`, "S5: the hook paths") gain one capability
  `trCap s.tr r id ph` in their pre- and postconditions (`emp` when `s.tr = none`), one spec per
  function for both modes; the node invariant ties `s.tr` to `Cluster.trace γ`. `interface/` then
  differs by the field (`Defs.txt`) and those specs' added capability, besides the gated additions:
  not exactly the acceptance test's letter ("only gated additions and the pure fact"), though every
  closed statement is unchanged and untraced clients only meet `trCap none = emp`. (b) An optional
  argument on `ownRaftPhysCV`: the specs off the hook paths are then not mode-polymorphic (hundreds
  of statements to generalize). (c) A second, traced copy of the hook paths' proofs: two specs per
  function, against the hard rule. **Taken by the agent, pending the user's veto: (a)**, with the
  `interface/` diff explained in the commit that makes it.
- **Q9 (2026-11-09, Q8 stage 1): `MessageType.String`'s trust boundary is too weak for the traced
  send and receive hooks.** `makeTracingMessage` names a message's type by `m.GetType().String()`,
  protoc-gen-go's generated method (`protoimpl.X.EnumStringOf` over the file descriptor), which the
  raft v3.7 translation has names-only; its trust-boundary axiom
  (`Proof/go_etcd_io/raft/v3/raftpb/MessageType__String.lean`) says it returns some string
  (`fmt.stringMethodSpec`), all `fmt` needs. The frozen Draft's `MsgEvOf` (hence `SendEvOf`,
  `sendGate`, `recvGate`, and `raft.send.tracedSpec`) needs the name (`msgTypeStr`: `"MsgApp"`, ...),
  which the checker's parse reads. Options: (a) strengthen the axiom: `String` returns the name of
  `MessageType_name` (raftpb's generated table) at the value, at least for the six traced types (a
  trust-base change: the statement of an existing axiom); (b) a trusted model of the method
  (`TrustedCode/`) looking the value up in `MessageType_name`, its docstring arguing that the
  descriptor's names are the table's (a trust-base change of the same size, but a model instead of
  an axiom); (c) translate protobuf's enum `String` path (reflection over the descriptor: large).
  **The user's decision (2026-11-09): (b)**: a trusted model of `MessageType.String` reading
  `MessageType_name` (fallback: the decimal, as `EnumStringOf`), raftpb's package fact holding the
  table, the spec proved over the model, the axiom removed, and a Go test that the descriptor's
  names are the table's. (Before the decision: the agent's recommendation (b), else (a); the node
  events do not depend on it.)
  **Q9 done (2026-11-09, branch `trace-check-q9`):** `MessageType.String` is `trusted`
  (`raftpb.toml`), its model `MessageType.String.impl` (`TrustedCode/go_etcd_io/raft/v3/raftpb.lean`,
  the goose translation of the lookup-else-`strconv.Itoa` body, with the faithfulness argument);
  raftpb's package fact holds `MessageType_name ↦□ m ∗ m ↦$□ raftpb.msgTypeNames` (proved in raft's
  hand-written `Init.lean`: raftpb is outside `etc/gen-init.py`, as raft's other packages); the spec
  is exact (`raftpb.msgTypeString t`, `MsgTypeName.lean`) and proved, the axiom gone;
  `fmt.stringMethodSpec_of_wp` gives rafthttp the weak form; `msgTypeString_traced`
  (`TracedMsgType.lean`) gives `msgTypeStr ty` for the six traced types, for the send and receive
  hooks; the Go test `examples/raft/tracecheck/msgtype_string_test.go`. Trust base: the axiom out,
  the model in, the server's results on `strconv.Itoa`'s axiom (`notes/decisions.md`, "Q9").
- **Q21 (2026-11-11, Q8 stage 1 slice 22b): an accepted append's truncation and the frozen
  `QuorumLogF`.** A receiver at the request's term may hold, by coincidence, a prefix a quorum
  committed at a higher term, and truncate it; `QuorumLogF` (a clause of the frozen `simFx`) stays
  true of reachable states (the committing quorum never truncates it), but it does not record who
  committed or at which term, so it cannot be re-proved after the truncation from the facts at hand
  (in a three-node cluster the servers lacking the prefix can go from one to two, a quorum)
  (`notes/decisions.md`, "Q8 stage 1 (slice 22b)"). Options: (a) an inductive strengthening of the
  clause (the committing quorum's term recorded, so a truncating receiver is shown not to be in it),
  checked against the specification first; (b) a weaker `QuorumLogF` that the simulation still
  needs (to check: who reads it); (c) facts from raft's ghost state passed into the line's `FxPres`
  (the frozen laws see only `σ`). **Taken by the coordinator (the freeze being delegated to it),
  pending the user's veto: (a)**, as amendment A5 (checked against the specification first, a review
  round, then the re-freeze `trace-check-frozen-a5`).
- **Q20 (2026-11-10, Q8 stage 1 slice 21): the frozen `StartNode.gatedSpec` does not give the
  capability.** `TracedApiDraft`'s `startTrace` hands `StartNode` the simulation's invariant as
  `inv (simN N) (simInv vs tn (fun _ => True))` and the node's share `simNode`, but `trCapB` (frozen,
  `TracedCap.lean`) holds `inv (simNS γ.raft) (simInv C tn (simFx γ.raft C))` (another namespace, the
  facts `simFx`), the node's `booted` flag `simBoot tn id false none`, and `raftLogInv`; a weaker
  invariant cannot be strengthened inside `StartNode`, and the flag is the invariant's (`Bt`), so
  `StartNode`'s traced proof cannot build the capability from `startTrace`. Options: (a) amend
  `startTrace` (frozen tag `trace-check-frozen-a2`) to the capability's pieces: `inv (simNS γ.raft)
  (simInv vs tn (simFx γ.raft vs))` and `simBoot tn cv.ID' false none` beside `simNode` (`Main`'s
  allocation, S7, creates both; `simFx_simInit` gives the facts at the start); (b) keep `startTrace`
  and give `StartNode` the capability itself, `trCapB` needing the struct's logger field, which does
  not exist before `newRaft` (not possible); (c) `StartNode` allocates the invariant itself (one per
  node: the cluster needs one shared). **Recommended: (a)**, with the next amendment (A3's review
  round, or its own) (`notes/decisions.md`, "Q8 stage 1 (slice 21)").
  **Taken by the coordinator (the freeze being delegated to it), pending the user's veto: (a)**, as
  amendment A4 (its own review round, then the re-freeze `trace-check-frozen-a4`).
- **Q19 (2026-11-10, Q8 stage 1 slice 21): an unbooted node's `Step` and ticks.** `stepBundle_traced.on`
  (`TracedRaftStep.lean`) and the ticks' traced corollaries (`raft.tickElection.tracedTriple`,
  `raft.tickHeartbeat.traced`) take the capability with its `booted` flag set (`trCapB … true …`), but
  `node.run` may step a message or tick before the node's first non-bootstrap line (its first `Ready`):
  its `select` takes `recvc`/`tickc` as soon as `readyc`, and another node can have campaigned by then.
  Before that line the flag is unset (`trCapB … false …`), and no law sets it without a line. Options:
  (a) the bundle and the ticks' corollaries take the capability with any flag (`∃ b`, `trCap`), which
  the laws they use already accept: a receive line goes through `trCap_fire_recv` (any flag), a
  `BecomeCandidate` through `trCap_fire_any` (not bootstrap-named), and a path's first line is one of
  these (a leader's `MsgBeat` and `MsgProp` paths are of a booted node: a leader has logged
  `BecomeLeader`); raft-internal, not frozen; (b) the node API supplies `b = true` (impossible as the
  code is: nothing orders the first `Ready` before the first receipt or tick); (c) the harness waits for
  each node's first `Ready` before starting the network and the ticker (a harness change, weaker
  workload). **Recommended: (a)** (`notes/decisions.md`, "Q8 stage 1 (slice 21)").
  **Taken by the coordinator (raft-internal): (a)**, after slice 20b lands (it edits the path files).
- **Q18 (2026-11-10, Q8 stage 1 slice 21, slice 19b's finding): a received heartbeat's shape.**
  `stepBundle_traced.on`'s `TrRecvShape` asks a heartbeat without entries and a heartbeat response not
  rejecting; the node API has of a received message its `isRaftMsg` (`ApiVocab.lean`, importable),
  whose `SentMsgShape` gives the third clause (`isRaftMsg_trRecv`) but not these two, and neither does
  `isMessage` (`Protocol/GhostState.lean`, importable: its heartbeat clauses say nothing of the entries
  or the rejection). Raft never sends otherwise (`bcastHeartbeat` attaches no entries,
  `handleHeartbeat` never rejects). Options: (a) the two clauses in `SentMsgShape` (client-visible:
  every client's `isRaftMsg`, every send site's proof obligation, which raft meets); (b) the two
  clauses in `Msg.TrOk` (`Protocol/Model.lean`), the traced numbers clause, which a traced message
  already carries in `isMessageC` (`MsgTrOk`, gated on the cluster's trace mode: vacuous for every
  untraced client) and which raft establishes where it queues a message (slice 10's `OutTr`): the
  shape becomes a traced-only fact; (c) the clauses in `isMessage`'s heartbeat and heartbeat-response
  arms (client-visible, ungated). **Recommended: (b)**: gated, and on the path the traced numbers
  already take (`notes/decisions.md`, "Q8 stage 1 (slice 21)").
  **Taken by the coordinator, pending the user's veto: (b)** (gated: vacuous for every untraced client).
- **Q17 (2026-11-10, Q8 stage 1 slice 19b): a candidate's vote responses, a voter's first only.**
  Raft's tally records a voter's first response of a term only (`recordVote`); the specification's
  `HandleRequestVoteResponse` adds a voter to `votesGranted` on every granting response, so a voter that
  rejected and then granted would make them diverge (`sim_recordVote` needs `s.votes !! m.From' =
  none`). Raft never sends that (one `MsgVote` per peer per campaign, one answer per request,
  at-most-once delivery), but nothing in the frozen `simFx` or the bundle states it, so a candidate's
  `MsgVoteResp` (pending, won or lost) is not provable. Options: (a) a pure clause of `simFx`
  (`VoteRespUniq`: while `i` is a candidate of `T`, no vote response of term `T` to `i` is in flight
  from a server of `i`'s `votesResponded`, and at most one from any other), with its preservation by the
  specification's actions; (b) a premise of the bundle (`s.votes !! m.From' = none` for a candidate's
  `MsgVoteResp`), which the node API cannot supply; (c) layer B's tokens (their at-most-once half
  covers one message, not two equal-content ones). **Recommended: (a)**, in an amendment A3 (with a
  review round) (`notes/decisions.md`, "Q8
  stage 1 (slice 19b)").
  **Taken by the coordinator (the freeze being delegated to it), pending the user's veto: (a)**, as
  amendment A3 (a review round, then the re-freeze `trace-check-frozen-a3`).
  **(a) found false, A3 not made (2026-11-10, branch `trace-check-a3`)**: a lower-term vote request's
  phantom refusal (Q14) is of the receiver's current term, so a reachable state has a candidate's
  voter's phantom refusal and its real grant in flight together; and no fact of `simFx` (a function of
  `σ`) can tell the phantom from raft's messages, so none makes the tally step provable (counterexample
  run and argument: `notes/decisions.md`, "Amendment A3 (Q17)"). New options, each beyond `simFx`: (d)
  relax `SimServerR`'s candidate tally to raft's granting voters ⊆ the specification's `votesGranted` ⊆
  `votesResponded` = raft's voters (no invariant needed; a few lemmas); (e) `simInv`'s `Fx` given the
  phantom lists, the clause over raft's messages only (every law changes); (f) a fact on raft's
  refusals (rejected: raft alone cannot prove it). **Recommended: (d)**, as a re-scoped A3. For the user
  (or the coordinator, if the delegation covers `SimServerR`).
  **Taken by the coordinator (the freeze being delegated to it), pending the user's veto: (d), as
  amendment A3.** **Done** on branch `trace-check-a3` (`TallyGranted`; `notes/decisions.md`, "Amendment A3 (Q17)").
- **Q16 (2026-11-10, amendment A2's reviews a2-r3, a2-r4): an `"app"` append request's entries,
  unpinned for `MsgsUniq`.** A receive line logs an append request's entry count only
  (`Line.isAppendEntriesRequest`), so after an `"app"` send line with entries `MsgsUniq` needs every
  in-flight request from the same leader, term, previous entry, commit and count to carry the same
  entries. `MsgsShape` (A2) leaves the entries free (they are content); `msgFacts` gives only
  `isLeader` and `logRecs`, and `MsgOk` ties only the current-term entries to the leader's log, so two
  term-`T` requests with the same previous entry may carry different earlier-term entries (a leader
  catching up a lagging follower sends such entries). A request with no entries is covered
  (`ContentLogged`: heartbeats, probes, commit-only appends). Blocked: every `"app"` send line with
  entries: the `MsgProp` path's appends, and the appends sent while handling `MsgAppResp`/`MsgVoteResp`
  (catch-up, a won election's appends). Options: (a) amend `msgFacts` (frozen) for an append request
  with the leader's term-log prefix, `∃ bL l, leadPrefix γ src (W64 m.term) bL l ∗ ⌜the entries are l's
  slice after prevLogIndex⌝`; two requests of one term then agree by `leadPrefix_base`,
  `leadPrefix_agree` and the records' agreement (`isEntryR`); to check: `sendAppend`'s caller holds
  `leadPrefix` of its log; (b) strengthen `MsgOk`/`SpecInv` (pure): an append request from the current
  leader of its term carries exactly that leader's log slice, of every term (it holds when sent, the
  specification's `appendEntries` takes `subSeqM v.log`, and a leader's log only grows in its term; no
  ghost state); `SpecInv` is frozen too through `simFx`; (c) prove the agreement from the existing facts
  (a2-r4: very probably fails); (d) leave the `"app"` lines to a later amendment. **Recommended: (b)**
  (pure, the smallest), else (a). Not taken here: beyond the coordinator's Q15 decision.
  **Taken by the coordinator (the freeze being delegated to it), pending the user's veto: (b), folded
  into amendment A2.** **Done** on branch `trace-check-a2`: `simFx`'s clause `AppSlices` (while a server
  leads term `T`, its in-flight term-`T` append requests are slices of its log), checked inductive
  with `CandS` by reading the transcription (no preservation lemmas yet); `fxPres_app` (`notes/decisions.md`, "Amendment A2 (Q14, Q15, Q16)").
- **Q15 (2026-11-10, Q8 stage 1 slice 16): the frozen `simFx`'s `MsgsUniq` is not kept by a send
  line.** `FxPres` asks `simFx` after the line for every `σ` with `simFx`; after a send the new message
  must be the only in-flight message a receive line matches with it, but a line logs only some fields
  and `simFx` fixes none of the others, so an in-flight message differing from the new one only in an
  unlogged field (a heartbeat's `prevLogIndex`; an append request's `matchIndex`; ...) is consistent
  with `simFx` and breaks `MsgsUniq` (`notes/decisions.md`, "Q8 stage 1 (slice 16)"). Every send line,
  so every path that sends (the local ones with lines, and the receive paths' replies), is blocked.
  Options: (a) a shape clause in `simFx` (every in-flight message has the specification constructors'
  values in the fields its type's line does not log: the notes' `MsgsDet`, "the other fields
  constant"), carried by the laws' proofs; (b) `FxPres` given the simulation's bag relation (each
  in-flight message raft's `msgAbs` or a phantom); (c) `MsgsUniq` on the logged fields only (breaks
  `LineEffect`'s single match). **Recommended: (a)**, folded into amendment A2 (same files, one review
  round, one re-freeze). Not taken: a frozen definition.
  **Taken by the coordinator (the freeze being delegated to it), pending the user's veto: (a)**, folded
  into amendment A2 before its re-freeze (one review round covering Q14 and Q15). **Done** on branch
  `trace-check-a2` (`MsgsShape`, `canonMsg`; `fxPres_heartbeat`).
- **Q14 (2026-11-10, Q8 stage 1 slice 15): a receive line's phantom replies, unpinned in the frozen
  `FxPresR`.** `FxPresR` (`TracedCap.lean`, frozen at `trace-check-frozen-a1`) asks the specification
  state's facts after the line for every result `(a', P', Pph)` its `LineEffect` admits; the phases pin
  `toC a'` and `P'`, nothing pins the phantoms `Pph`, and `LineEffect` cannot be instantiated inside
  `FxPresR` to pin them (no bag `Nodup`/count there; the result's `violated` circular). So no receive
  line's gate can be built and every path of a traced type is blocked (`notes/decisions.md`, "Q8 stage
  1 (slice 15)"). Options: (a) the phantoms a function `ph : Etcdraft.Server → List Etcdraft.Msg` of the
  receiving server, a parameter of `PhaseStepR`, `FxPresR` and `trCap_fire_recv.statement` (`Pph := ph
  a`; the existing `phantomOf` gives it); (b) `FxPresR` given the bag's premises and a chain-determinism
  lemma; (c) `Pph` an argument of `Φ'`. **Recommended: (a)** (the smallest change; the law's proof
  passes `ph a` through unchanged). Not taken: a frozen statement.
  **Taken by the coordinator (the freeze being delegated to it), pending the user's veto: (a)**, as
  amendment A2 of the frozen Draft: the amendment on a branch, a spec-reviewer round on it, then a
  re-freeze (tag `trace-check-frozen-a2`); meanwhile the local paths that log lines go on (they use no
  receive line).
- **Q13 (2026-11-09, layer B's exports): amending the frozen laws' event premise.** `mainPure` needs
  per-event facts (`ScopeOk`, `NumsBelow K`, `ConfsWithin 3`, `BootLogsOk`, an event count) that `simInv`
  cannot keep: the frozen `trCap_fire*` laws are generic in their events, four of them admit a
  `ChangeConf`/`MsgSnap`/`InitState` line, none bounds numbers or counts ("Layer B's exports"). Options:
  (a) amend the Draft: in the seven laws, `∀ e, E e → TraceEv.Ascii e` becomes `∀ e, E e → TraceEv.Ok K e`
  (ASCII, in scope, numbers below `K`, three-voter configurations, a bootstrap log of at most three
  entries), a ghost event counter the laws increment, and `simInv` keeping each; the hooks' traced
  specs then take `Ok` of their events, discharged at the call sites from raft's ghost (the time receipts
  for `K`); a review round on the amendment, then a re-freeze (tag `trace-check-frozen-a1`); (b) keep the
  laws and prove the facts at the end from raft's run some other way (no such source in layer B).
  **Taken by the coordinator (the freeze being delegated to it), pending the user's veto: (a)**, after
  slice 5 lands (it edits the same files).
  **Q13 (a) done (2026-11-09, branch `trace-check-q13`), save one blocker (below).** The facts
  `mainPure` takes of the events moved to raft (`TraceSim.lean`: `TraceEv.InScope`, `NumsBelow`,
  `ConfsWithin`, `ScopeOk`, `BootLogsOk`), with `TraceEv.Ok n e := Ascii ∧ InScope ∧ NumsBelow
  traceNumBound ∧ ConfsWithin n` (`traceNumBound = 2^61`) and, for the bootstrap law,
  `TraceEv.OkBoot n e := Ascii ∧ NumsBelow traceNumBound ∧ ConfsWithin n ∧ logSize < 2^40` (not in
  scope: `InitState` is a bootstrap line). The seven laws (`TracedCap.lean`) take `∀ e, E e →
  TraceEv.Ok (elements c.incoming).length e` (`OkBoot` for `trCap_fire_boot`; `trCap_fire_bf` gained
  the premise); `simInv`'s last clause is `SimEvents C.length L` (ASCII, `ScopeOk`, `BootLogsOk`, the
  numbers, the configuration lists), kept by `simEvents_snoc`/`simEvents_snoc_boot`; the Draft's traced
  statements on the capability (`traceCommit`, `raft.maybeCommit`, `raft.send`) and the derived
  `raft.becomeCandidate/becomeFollower/maybeCommit.traced` take the premise when traced
  (`s.gh.tr.isSome →`); `nodeEvOf_ok`/`nodeEvOf_okBoot` discharge it for a node event from its state's
  numbers. Decided by the agent against the plan's wording: **no `K` parameter** (the laws' bound is
  `traceNumBound` itself; a caller with a smaller bound weakens it), **the configuration bound from
  raft's configuration** (`(elements c.incoming).length`, the voters `C` by `trCapB`'s permutation, not
  a literal 3, which nothing supplied: review round 1's F2), **no event counter** (`L.length` is the
  count; it is bounded by the run's steps, through the recorder that holds `traceAuth`, not by the
  simulation: left to layer D and the adequacy theorem), and `OkBoot`'s log bound is the consumer's
  `2^40`, not the bootstrap's `≤ 3`. `simInv_end` (`TraceSimEnd.lean`) now gives `SimEvents C.length L`,
  and `tracecheck/MainSim.lean` (`mainPure_of_sim`, `simInv_main`) gives all of `mainPure`'s
  conclusion from `simInv`, the recorder's `traceAuth`, the bootstrap facts (layer B's bootstrap clause,
  owed), `|C| < numBound` and `L.length < numBound` (adequacy). `TraceSimEnd`, `TraceSimGhost`,
  `TraceSimBag`, `TraceSimLemmas` are now importable (`etc/api/raft.txt`). Reviews:
  `notes/trace-validation-reviews/q13-r*.md`. **Blocker (review round 1's F1): `MsgEvOf` leaves the
  traced message's `rejectHint` free**, so no `SendEvOf` event can be shown `TraceEv.Ok` (which bounds
  it, as `Event.Bounded` does): `raft.send.tracedSpec`'s new premise and every send or receive law use
  are undischargeable until `MsgEvOf` gains `tm.rejectHint = m.rejecthint` (raft writes it,
  `state_trace.go`; `absMsg` carries it). The repair touches `TracedMsg.lean` (`msgEvOf_traceMsgOf`, one
  `rfl`) and `raft__send.lean` (`msgEvOf_absMsg_from`, one hypothesis), the files of the agent working on
  raft's Go-level specs, so it was not made here; the re-freeze waits for it. **Owed by the Prove
  phase:** (F3) the traced cluster's receipt bound such that raft's terms and indices stay below
  `traceNumBound` (about `receiptBound GF + |C| < 2^61`, stated at `cluster_alloc`'s traced premise,
  replacing `notes/trace-validation-sim.md`'s `2^62 − 2`); (F4) a received message's numbers (a
  receive line's event is of the message), from raft's message facts or from a `simInv` clause on
  the bags (every message in them was logged by a send line already bounded).
  Review round 2 (`q13-r2.md`): F1 still open (as above); F2, the bootstrap lines' capability: `trCapB`
  takes the cluster's configuration while raft's grows from empty during `Bootstrap`, and
  `raft.becomeFollower.traced`/`trCapB_hookGate_bf` use one `c` for both (a gap of the frozen Draft,
  predating Q13: its `b = false` precondition is unsatisfiable at `Bootstrap`'s `becomeFollower`); the
  amendment's part is repaired (`nodeEvOf_ok`/`nodeEvOf_okBoot` at a free bound `n`, `ccEvOf_okBoot`,
  `TraceEv.ok_mono`/`okBoot_mono`), the routing (the capability's configuration apart from the
  struct's) left to the bootstrap clause's work; F3 (`simInv_main` restated `newTrace`'s success)
  repaired: the success is a hypothesis, listed as owed; F4 the interfaces, regenerated.
  Review round 3 (`q13-r3.md`): A = F1, open (the blocker); B, `raft.maybeCommit.tracedSpec`'s `hΛ` at
  the pre-commit state while Go logs `Commit` after it (predating Q13, and now disagreeing with the new
  premise at the outcome): repaired, `hΛ` at the outcome as `raft.maybeCommit.traced` states it; C = F2's
  routing, also at `newRaft`'s `becomeFollower`, open (noted on `raft.becomeFollower.traced`). Second
  tier done: `ccEvOf_ok`, the bootstrap lemmas' redundant number premise. The receipt bound (F3) has a
  source: `readyFits` states `receiptBound GF + bootLen ≤ 2^61` (`InvNode.lean`); owed is the law turning
  it into bounds below `traceNumBound` at `raft.Step`'s handlers. Open second tier (left for the Prove
  phase or the user): literal `2^40`/`2^61` beside `bootLogBound`/`numBound` (`TraceSim` does not import
  `Rep`), unnamed event indices, the pure premises outside the triples, the repeated outcome state in the
  `maybeCommit` statements, `SimIdle`'s `2^63` beside `traceNumBound`, and the API widening (a sealed module
  exposing only `simInv_end` would be smaller).
  Review round 4 (`q13-r4.md`): no new first-tier finding; A (the blocker) and C (predating Q13) open as
  above. Repaired: the Draft `raft.maybeCommit.tracedSpec` gives `⌜maybeCommitOut c s b N⌝` (N1), the
  headers list the new lemmas and the blocker (N2). Note for F4: once `MsgEvOf` pins `rejectHint`, a
  receive line's premise also needs the received message's `rejectHint` bounded (its source, raft's
  message facts or a `simInv` clause on the bags, unchecked).
  **Amendment A1 ready to freeze (2026-11-10, branch `trace-check-a1`).** The re-freeze's two repairs:
  (1) `MsgEvOf` gains `tm.rejectHint = m.rejecthint` (every field `makeTracingMessage` writes is pinned
  but `Vote`, some decimal), with `Msg.NumsBelow` and `sendEvOf_ok` (one lemma for send and receive
  events, `sendEvt_inScope`/`recvEvt_inScope`); (2) the bootstrap capability's configuration: the
  capability's `c` is always the voters', raft's apart from it while it grows from empty in `newRaft`
  and `Bootstrap`; no law or Draft statement changed (`trCap_fire_boot`'s events were already free),
  the gate `trCapB_hookGate_bf` and `raft.becomeFollower.traced` take the capability's `cC` apart from
  raft's `c` (`b = true → cC = c`, `b = false → c.outgoing = ∅`) (`notes/decisions.md`, "Amendment
  A1"). Also q13-r4's N3 (`ccEvOf_numsBelow`/`_confsWithin`), the stale "vacuous until Q8's logger
  clause" note, `TraceEv.ok_mono`/`okBoot_mono` dropped (unused). Reviews: `a1-r1.md` (no first tier;
  repaired: `Msg.NumsBelow`, docstrings, the open bootstrap gates named), `a1-r2.md` (no first tier;
  repaired: the received numbers' carrier named, raft's `isMessage` with a trace-gated conjunct,
  docstrings). Left (second tier, the Prove phase's or the user's): the carrier itself and the receipt
  bound (F3, F4); the bootstrap routing (an `InitState`/`ApplyConfChange` parse lemma, an either-mode
  `ApplyConfChange` gate with `cC` apart, an intro law for `trCapB` in `newRaft`); literal `2^40`/`2^61`,
  unnamed event indices, pure premises outside the triples (grown by `hcC`, `hout`), the repeated
  outcome state, `SimIdle`'s `2^63`, the API widening, `SendEvOf`'s vote unpinned. Full build green;
  every TCB collection unchanged; the coordinator can tag the branch's head `trace-check-frozen-a1`.
- **Q12 (2026-11-09, `Main`'s pure obligations): the checker's `numBound` against the step bound.**
  `numBound = 2^40` (`etcdraft/Rep.lean`, a constant of the proof, not of the Go) bounds the trace's
  numbers (`Event.Bounded`) and its length; raft's terms, indices and event count grow with the steps,
  and the statement's step bound is `n < 2^61` ("as the kv examples' unless the proof needs another",
  the user's, 2026-11-08). Options: (a) raise `numBound` (and, if the reached states' margin
  `numBound + len + 1` then exceeds the actions' internal `2^62` bound, raise that bound, also the
  proof's: the Go's integers are `int64`), so the statement keeps `n < 2^61`; (b) lower the step bound
  to about `2^40`. **Taken by the coordinator, pending the user's veto: (a)**: the closed statement
  keeps the bound the user set, and only proof-internal constants move. Done in S7.
  **Q12 done (2026-11-09, branch `trace-check-layerb-exp`): `numBound = 2^61`, no action's bound
  raised, no Go changed.** The margin was the proof's, not the Go's: `TraceInit`'s numbers are the
  events', below `numBound`, so it has the reachability invariant at `numBound - 1` (not `numBound`),
  and a state at line `l` at `numBound - 2 + l` (`Trace.Valid.init_inv`, `Trace.Valid.reach_inv`;
  the sent `AppendEntries`' premise `numBound - 1 ≤ K`); with `l ≤ len + 1 ≤ numBound` the bound is
  at most `2 * numBound - 2 = 2^62 - 2`, so a log's `len + 1 < 2^62` and the actions' `2^62` stand
  (`2^61` is the largest `numBound` they allow; raising them would need `0 ≤ b` in place of
  `-2^62 < b` in `AppendEntriesInRangeToPeer`'s range, whose Go computes `b - 1`, `e - 1` and
  `SubSeq`'s differences, for no gain). So the statement's `n < 2^61` steps give every term, index
  and the event count below `numBound` (`mainPure`'s `K ≤ 2^61`). **Found: the allocation.**
  `numBound` also bounded the one Go allocation sized by a trace number, `NewTraceWith`'s
  `make([]Entry, lb.ev.Log)` of a node's last bootstrap line (review round 1 of layer C, S2: gc
  refuses above `maxAlloc = 2^48` bytes, an `Entry` 80 bytes; Goose's `make` does not, so no proof
  needed it). Kept apart: `bootLogBound = 2^40` and `NewTrace`'s (and `NewTraceWith`'s) new premise
  conjunct `Event.BootLogsOk evs` (every bootstrap-named event whose node, by its parsed id, has
  logged only bootstrap-named events before it has `log < 2^40`: a superset of the lines
  `bootstrapOf` flags), unused by the proofs, there so that the spec claims no `make` Go would
  refuse. `mainPure` gives it from a new hypothesis on raft's events, `BootLogsOk L` (an event logged
  while its node is `Unbooted` has `logSize < 2^40`; `bootLogsOk_snoc`, `bootLogsOk_events`), one
  more fact layer B is to export (raft's bootstrap lines: `logSize ≤ |C|`).
- **Q11 (2026-11-09, Q8 stage 1 slice 4): a ghost record of the just-queued message.** `raft.send`
  queues the message before its trace hook runs, so at the hook raft's queues own it, and
  `ownRaftPhysCV` keeps the queues existential (the abstract outbox up to permutation, no pointers):
  no lemma can lend the message at pointer `m` back out (slice 4's paragraph). Options: (a) a ghost
  field `NGhost.lq` (the last queued message), set by `send` before the hook and reset before it
  returns, with a membership clause in `ownRaftPhysCV`, the queue-draining closures recording
  `lq = none` in the `RawNode` predicates as stage 0 recorded the trace mode (`Defs.txt` gains the
  field, as Q8 (a) added `NGhost.tr`; no closed statement changes); (b) keep the queued messages'
  points-to in `ownRaftPhysCV` with their pointers (a larger change to every queue lemma). **Taken by
  the coordinator, pending the user's veto: (a)**, the smaller change of the same kind as Q8 (a).
  **(a) done (2026-11-09, branch `trace-check-q8s5`)**, as a stack `NGhost.lq : List (Loc × MsgSt)`
  rather than an `Option` (decided by the agent): `send` must give back its caller's record (its spec,
  and the Draft's frozen `raft.send.tracedSpec`, are for any `s`), which an overwritten `Option` loses;
  the `RawNode` predicates record `lq = []` (`notes/decisions.md`, "Q8 stage 1 (slice 5)").
- **Q10 (2026-11-09, layer C: `CheckTrace`): the premise `CheckTrace.spec` takes.** `CheckTrace.spec`
  (precondition `traceRO t tr` only) could not be proved from its callees' specs, which take the Lean
  evaluation to succeed, the line in scope and the state bounded (layer C, "`trace.go`'s search proved;
  `CheckTrace` blocked": evaluation errors on valid traces, out-of-scope lines `NewTrace` accepts, bounds
  that need a reachability invariant, one of them, the configurations' sizes, not even derivable from
  `Event.Bounded`). Options: (a) panic-aware specs of every callee that can raise an `EvalError` (Goose
  models `recover`: `wp_with_defer_recover`), specs of the seven out-of-scope actions, a reachability
  bound with `Event.Bounded` strengthened; (a') a pure premise `Trace.CheckTraceOk tr invariants` (the
  spec's conclusion unchanged) that `Main` discharges of raft's trace, kept as close to the trace as the
  proof allows. **Taken by the agent, pending the user's veto: (a')** (the delegating session's
  decision): `CheckOk.lean`, "`CheckTrace` proved under `Trace.CheckTraceOk`" in layer C below, and
  `notes/decisions.md`, "Q10: `CheckTrace`'s premise". The evaluation can fail on in-scope bounded
  traces (the one-line `InitState` with `commit 1` on an empty log), so that part stays a premise;
  `Main` gets it from layer B's run (`Trace.RunRel.noEvalError`).
- **Q2 (2026-11-08, S3): raft's results rest on `strconv.FormatUint`'s axiom.**
  `traceChangeConfEvent` formats the change's ids (`strconv.FormatUint`) before its nil check, so
  the translated raft calls it even without a logger, and raft's linked results now rest on
  `Spec/strconv/FormatUint.lean`'s trust-boundary axiom (already the server's). The plan's "Trust
  base" lists `strconv.FormatUint` among the standard-library specs: taken by the agent as that
  recommendation, pending the user's veto (`etc/tcb-collections/raft.txt` updated, and `kv`, `kvdurable`, `kvreconf`, whose results reach raft's; the server's collections already had it). The
  alternative, an early `if r.traceLogger == nil { return }` in the fork, changes raft's code beyond
  the build tags.

## The statement

`raft_tracecheck_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Results.lean`,
the shape of `raft_kv_porcupine_safe`): every execution of `kvProgram`'s analogue -- the package's
initialization, then `Main()` -- from a fresh state, of fewer than `2^k` steps, has no stuck
thread and no panic.

`Main()`: start a cluster as `RunConcurrent(DefaultCConfig(seed))` does (three voters, proposals,
drops, delays and reordering, isolations; no restart, compaction or configuration change); stop it;
convert its events (raft's `TracingEvent`s, in memory, no JSON) to the checker's; run `CheckTrace`;
panic unless `TLCOK`. The seed is arbitrary (`primitive.RandomUint64`, which the proof treats as
any value: the theorem covers every seed); the step bound as the kv examples' (`n < 2^61`) unless
the proof needs another (the user's, 2026-11-08).

`Results.lean` also states, as a corollary of the checker's spec, that the trace of every
execution is accepted by `TraceAccepts`, the Lean transcription of `Traceetcdraft.tla`'s
`TraceSpec` with TLC's `TraceMatched` and the invariants.

## Trust base: one transcription of the TLA+, either one (the user's, 2026-11-08)

What the result says about raft rests on one transcription of `etcdraft.tla` and
`Traceetcdraft.tla` deciding what the TLA+ decides -- either one, not both:

- the **closed theorem** mentions only the Go program (`Main`, with the Go checker in it) and
  Goose's semantics: its meaning rests on the Go checker's faithfulness to the TLA+; the Lean
  transcription is a device inside the proof, and a mistake in it would leave the theorem as true
  and as meaningful;
- the **corollary** is stated with the Lean `TraceAccepts`: its meaning rests on the Lean
  transcription's faithfulness, the Go checker being a verified implementation of it.

Layer C proves the two equal on the traces `CheckTrace.spec`'s premise `Trace.CheckTraceOk` admits
(Q10, 2026-11-09: the lines in scope, the events' configuration lists bounded, no evaluation error; the
reached states' bounds follow, `Trace.Valid.reach_searchOk`; raft's traces are expected to be in that
class, which `Main` is to show): there `CheckTrace` accepts exactly when
`TraceAccepts` holds. So the evidence for either is evidence for both on that class: the Go
transcription's three-way comparison with TLC (the state spaces under four bounds, clean, mutated and
full-featured traces, verdicts and failing lines) and the independent review
(`notes/raft-trace-validation.md`) count for the Lean one on that class (all three parts); the full-featured traces (`ChangeConf`, restarts, snapshots) and the evaluation-error cases
are outside what the proof transfers. "Faithful" is the one question: that the transcription computes what the
TLA+ says (not that raft or the harness are right: those are verified).

The rest of the trust base:

- Goose and Perennial (as everything here); the standard-library specs the code uses
  (`strconv.FormatUint`, `time.Sleep`, `sync`, maps).
- The equivalence of the `with_tla` build verified and the no-op build etcd ships (no logger: the
  hooks return at once), argued, not proved.

## The layers

### A. The trace hooks and the logger (raft)

Each of the eleven hooks (`Spec/go_etcd_io/raft/v3/trace*.lean`, now "a no-op") gets a spec:
reading `r.traceLogger`; nil: no-op; otherwise the logger's `TraceEvent` called with the event of
the raft state at that point (a pure function of the abstract state: term, vote, commit, role, log
length, configuration, the message's fields). The logger is a `TraceLogger` interface value whose
spec the raft invariant carries (as other callbacks' specs are carried): a logically atomic update
`TraceEvent(ev)` whose linearization point appends `ev` to the trace. Callers' proofs change only
where the raft invariant changes (the logger field and its spec). Existing results: no logger.
`traceReceiveMessage`'s `time.Sleep(1ms)`: Perennial's spec.

### B. The simulation (raft, workload-agnostic)

A global ghost state holds the trace so far and the trace specification's state `σ` (the Lean
`etcdraft` state). At each event's linearization point (in the logger, under its lock), with
every node's raft ghost state (the existing protocol ghost, `StepR`'s `PState`s, which an invariant
relates to `σ`): `StepLine σ line` has exactly one successor `σ'` (no branching), `σ'` satisfies
the invariants, and the relation holds again. The relation `R(raft ghost, σ)`:

- per node: term, vote, role, log, commit index, configuration; `matchIndex` against the leader's
  progress `Match`; `votesResponded`/`votesGranted` against the vote tally; `durableState` against
  what the last `Ready` handed out;
- the message bags: `pendingMessages` the messages raft has queued (logged as sent) and not yet
  handed out in a `Ready`; `messages` those handed out and not yet received (dropped ones stay:
  the specification's network keeps them), against the protocol ghost's message knowledge.

Premises (the application's use of raft, discharged by layer D): no restart; no compaction (so
raft never sends a snapshot: a fact about raft's code, that it sends one only for entries missing
from storage); configuration changes only those the specification models (none, for the first
harness); the bootstrap (`StartNode` of every voter) before anything else, so the trace's
bootstrap lines are its first segment and `TraceInit` is determined by it.

Determinism (no branching) is part of the step: each line selects one specification action and
one message. A received message: two messages in the bag matching the line are equal (the fields
the line does not log are determined: a heartbeat response's `mmatchIndex` is 0, a rejection's 0).

The invariants: from the existing safety results (leader completeness, log matching, election
safety, `Protocol/Facts`), restated on `σ` through `R`; `MoreUpToDateCorrectInv`,
`QuorumLogInv`, `CommittedIsDurableInv` may need more.

**Layer B's exports (2026-11-09, branch `trace-check-layerb-exp`): the run exported; the per-event
facts blocked by the frozen laws.** Done: `simInv_end` (`TraceSimEnd.lean`: `traceAuth tn.tr L ∗
simInv C tn Fx ⊢ traceAuth tn.tr L ∗ simInv C tn Fx ∗ ⌜∃ σ, SimRun C L σ ∧ σ.server = confAbs C ∧
∀ x ∈ L, TraceEv.Ascii x⌝`, the trace the simulation ran is the recorder's) and `simRun_runAccepted`
(`mainPure`'s `RunAccepted L`, unfolded, from `SimRun` and the bootstrap facts `newTrace` succeeding,
`t.init = simInit C`, `t.server = t.initSrv = confAbs C`, which layer B's bootstrap clause still owes).
**Not done: `ScopeOk L`, `NumsBelow K`, `ConfsWithin |C|`, `BootLogsOk L` and the event count as
`simInv` clauses**, because no `trCap_fire*` law can keep them: the laws are generic in the event
predicate `E` and, frozen (tag `trace-check-frozen`), take of it only what their phase steps say and
`∀ e, E e → TraceEv.Ascii e`. Per law: `trCap_fire_ready` (`NodeEvOf (W64 8)`, `Ready`) and
`trCap_fire_bf` (`NodeEvOf (W64 2)`, `BecomeFollower`) give `InScope`; `trCap_fire_boot` gives the
unbooted disjunct of `EvScopeOk`; but `trCap_fire`, `trCap_fire_any`, `trCap_fire_booted` and
`trCap_fire_recv` allow a `ChangeConf` line, a `SendAppendEntriesRequest` of a `MsgSnap`, and (the
last three, past the node's segment: `PhaseStepB` excludes only `BecomeFollower`) an `InitState`, since
their `LineEffect` only asks for a run of the line (the specification has those actions); P1-P3 hold
of raft's hooks (their `NodeEvOf`/`SendEvOf`/`CCEvOf` name the events; `sendEvt` of a snapshot is
`none`), not of the laws. No law bounds an event's numbers, its configuration lists (`trCap_fire_ready`'s
`NodeEvOf` is at any configuration `cfg`) or a bootstrap line's log size, and nothing counts the
events. So these facts must reach `simInv` through the laws' premises, a change to the frozen
statements (the user's): replacing, in the seven laws, `∀ e, E e → TraceEv.Ascii e` by `∀ e, E e →
TraceEv.Ok e` with `TraceEv.Ok e := Ascii ∧ InScope ∧ NumsBelow K ∧ ConfsWithin 3 ∧ uint.nat e.logSize
≤ 3` (the boot law: `InScope` replaced by the unbooted disjunct, which it has), `K` a constant of the
adequacy theorem whose source in the hooks is raft's time receipts (`budgetInv` for terms,
`isEntryR_receipt` for indices, `notes/trace-validation-sim.md`, "Increment 2": the receipt bound
then at most `2^61 - 1`, not `2^62 - 2`); the event count needs a ghost counter the laws increment,
bounded by the adequacy theorem's step bound (one step at least per event), for which raft's laws have
no resource either. With the premise, each law's re-proof is one more conjunct in its `simInv` update
(`scopeOk_snoc`, `bootLogsOk_snoc`, and `∀`-snoc for the others, as `ascii_snoc`). The export to `Main`
also needs `TraceSimGhost` and `TraceSimEnd` importable (`etc/api/raft.txt`), and with them their
public imports `TraceSimBag` and `TraceSimLemmas`: deferred to `Main`'s proof, the first importer
(`MainPure` takes `RunAccepted` as a hypothesis).

### C. The checker (Go, verified against the Lean transcription)

The transcription is split for the proof: the core (`etcdraft`: the specification, the trace
semantics on in-memory events, `CheckTrace`) in Goose's subset without `fmt`, `strings.Builder`,
`encoding/json`, `sort.Slice` (structural equality or a hand-written encoding for the view's
keys, sorted slices by `slices.Sort` or insertion); NDJSON reading and the porcupine model in
packages of their own, not translated. Its spec: `CheckTrace(events)` returns `TLCOK` exactly when
`TraceAccepts(events)` (sound and complete; the evaluation errors are failures), as planned; as proved
(Q10, 2026-11-09), on the traces `Trace.CheckTraceOk` admits (lines in scope, the events' configuration
lists bounded, no evaluation error), which raft's traces are expected to be (`Main`'s S7 obligation). Size: the Go is
about 1,500 lines; the proof is mostly the actions' functional correctness against their Lean
counterparts, and the search's.

**`types.go`'s leaves proved (2026-11-09, branch `trace-check-layerc-types`).** Specs and complete
proofs (no `sorry`, no axiom), each against its `Tla/Types.lean` definition: `NewSet` (`SetIds.mk`),
`Set`'s `Union`, `Add`, `Minus`, `Remove`, `Equal`; `Value.Equal`, `Entry.Equal`, `EntriesEqual`,
`IsPrefix`, `SubSeq`, `LastTerm`, `(*Msg).Equal`; `Bag`'s `find`, `Count`, `Len`, `Domain`, `add`,
`sub`, `With`, `Without`, `Filter`, `Plus`, `Minus`, `Equal`. Results the Go builds are fresh and
returned read-only like the inputs (`setRO`, `logRO`, `bagRO`; `msgsRO` for `Domain`, added to
`Rep.lean`, with `logRO_subslice`). Premises the Go needs and the transcription leaves implicit:
- **a bag's messages distinct** (`add`, `sub`, `With`, `Without`, `Plus`, `Minus`): the Go updates
  the first item holding `m`, the Lean (`Bag.add`/`Bag.sub`) every one; `Bag`'s docstring says the
  messages are distinct and `add`/`sub` keep them so (`Bag.add_nodup`, `Bag.sub_nodup`), but
  `bagRO` does not carry it: S6's invariant must (or `bagRO` take it, as `stateRO` took `Nodup`);
- **counts within `int`**: `add` (`count m + n < 2^63`), `With` (`+ 1`), `Plus` (the two bags' total
  counts below `2^63`);
- **`SubSeq` defined** (`subSeq s m n = some r`): where TLC fails the Go panics with an `EvalError`,
  which a triple cannot state; `subSeqM`'s caller checks the same condition.
No disagreement between the Go and the transcription was found.

**`spec.go`'s state functions and the workload's actions proved (2026-11-09, branch
`trace-check-layerc-spec`).** Specs and complete proofs (no `sorry`, no axiom), each against its
`Tla/Spec.lean` definition: `Config.Equal`, `Durable.equal`, `Server.equal`, `State.Equal`,
`durableOf`; on a clone being built (`stateOwn`): `send`, `discard`, `reply`, `commitTo`,
`persistState`, `becomeFollowerOfTerm`, `replicate`; read-only: `pendingFrom`, `IsJointConfig`,
`GetLearners`, `CurrentLeaders`, `HasNoConflict`; `nonNil`; the actions `RequestVote`,
`AppendEntriesInRangeToPeer`, `AppendEntries`, `Heartbeat`, `AppendEntriesToSelf`, `BecomeLeader`,
`ClientRequest`, `AdvanceCommitIndex`, `Ready`, `StepDownToFollower`, `UpdateTerm`,
`DropStaleResponse`, `HandleRequestVoteRequest`, `HandleRequestVoteResponse`,
`HandleAppendEntriesResponse`, `RejectAppendEntriesRequest`, `ReturnToFollowerState`,
`AppendEntriesAlreadyDone`, `ConflictAppendEntriesRequest`, `NoConflictAppendEntriesRequest`,
`AcceptAppendEntriesRequest`, `HandleAppendEntriesRequest`, `Receive`. An action returns a new
`stateRO` (or nil), except the five sub-actions of `HandleAppendEntriesRequest` (`Reject...`,
`ReturnToFollowerState`, `AppendEntriesAlreadyDone`, `Conflict...`, `NoConflict...`) and
`AcceptAppendEntriesRequest`, which return the clone owned (`∃ M, stateOwn`): the Go then writes
it (`t.mut(i).Lead = j` on every successor of a current-term request), so a frozen result would not
do. Additions to `Rep.lean`/`Own.lean`: `Bag.Ok`, the role and subtype `strRel` constants,
`decide_strRel`, `msgTypeW_decide`, `logRO_nil`, `serverOwn_intro`, `stateOwnHole_close_upd`,
`ownSlice_fullSlice_len` (a general slice fact, a candidate for Perennial), `wp_max_int`/`wp_min_int`,
`optOwn`/`optOwnS`, `stateOwn_not_null`/`stateRO_not_null`, `statesOwn_persist`, and the proof
tactics `read_server`, `lookup_server`, `read_msg`, `mut_open`, `close_copy`/`close_copy'`.
Premises the Go needs and the transcription leaves implicit (S6's loop invariant must carry them):
- **the bags `Bag.Ok`**: messages distinct and every count below `2^63 - 1`, for an action that
  sends or replies (`Bag.With`/`Without`'s premises; `discard` needs only distinctness); `Ready`
  needs the two bags' total counts below `2^63` (`Bag.Plus`);
- **lengths and indices far from overflow**: the logs, an append request's entries and a
  configuration below `2^62` entries (`HasNoConflict`'s `len(log) + 1`, `IsQuorum`'s premise in
  `AdvanceCommitIndex`, `BecomeLeader`'s granted votes); an append request's `prevLogIndex` in
  `[0, 2^62 - 1)`; `AppendEntriesInRangeToPeer`'s range ends in `(-2^62, 2^62)`; `Timeout`'s term
  (already);
- **`HasNoConflict`'s index at least 1**: at `index ≤ 0` the Go reads `log[index - 1]`, out of
  range (a Go panic, not an `EvalError`), where the Lean reads `log[0]` (`(index + k - 1).toNat`).
  Unreachable from the actions (`index = prevLogIndex + 1`, `prevLogIndex ≥ 0` is round 3's T3), so
  not a disagreement on the reachable states, but the two differ there;
- **`AppendEntriesInRangeToPeer` where the Lean evaluates** (`= .ok o`): the Go's `SubSeq` panics
  where TLC fails; the other `EvalM` actions proved here never fail where enabled, which their specs
  state (`.error _ => False`).
Left out, as the task allowed: snapshots (`HandleSnapshotRequest`, `SendSnapshot`; `Accept...`,
`HandleAppendEntriesRequest` and `Receive` take `m.subtype ≠ "snapshot"`), pre-vote
(`PreTimeout`, `RequestPreVote`, `HandlePreVote*`, `IgnoreInLease`; `Receive` takes the message
not a pre-vote one), restarts (`Restart`), configuration changes (`applyConfigUpdate`,
`reconfigure`, `AddNewServer`, `AddLearner`, `DeleteServer`, `ApplySimpleConfChange`),
`DuplicateMessage`, `DropMessage`, the `Next*` relations, `Init`. No disagreement between the Go and
the transcription was found on the functions proved.
**`invariants.go` proved, but for two (2026-11-09, branch `trace-check-layerc-inv`).** Specs and
complete proofs of `State.Committed`, `MessageTermsLtCurrentTerm`, `LogInv`, `MoreThanOneLeaderInv`,
`maxIndexOfTerm`, `ElectionSafetyInv`, `LogMatchingInv`, `QuorumLogInv`, `MoreUpToDateCorrectInv`,
`CommittedIsDurableInv`, each returning its `Tla/Invariants.lean` definition (read-only, `stateRO`);
the loops' shared laws in `StateRead.lean` (`servers_at`, `all`/`allM` loop steps). Premises the
caller (S6's loop invariant) supplies: the `EvalM` ones (`Committed`, `LogInv`, `QuorumLogInv`,
`MoreUpToDateCorrectInv`) take `… = .ok b`, as `SubSeq`; every server's log shorter than `2^63 - 1`
(`maxIndexOfTerm`, `ElectionSafetyInv`, `LogMatchingInv`: the Go's index runs to the length plus
one); every server's configuration smaller than `2^62` (`QuorumLogInv`, `IsQuorum`'s). Skipped:
`LeaderCompletenessInv` (it calls `CurrentLeaders`, `spec.go`'s, whose spec is on
`trace-check-layerc-spec`) and so `Violated` (also needs the package fact to give `Invariants`'
closures, `Base.lean`'s `True` until S6). No disagreement between the Go and the transcription.
**`invariants.go` done (2026-11-09, branch `trace-check-layerc-inv2`).** `LeaderCompletenessInv`
returns `State.leaderCompletenessInv` where it evaluates (`… = .ok b`; logs shorter than `2^63 - 1`,
the index loop's `len(Committed(i)) + 1`); its loops named in its proof file (`lcServer`, `lcIdx`,
`lcLeader`). `Violated` returns a Go string `strRel`-related to `(State.violated st).getD ""`
where it evaluates (`= .ok r`), under the premises of the invariants it calls (logs below
`2^63 - 1`, configurations below `2^62`, required whether or not an earlier invariant already
failed). Its loop reads the package fact, no longer `True`: `etcdraftInit` (`Base.lean`),
`Invariants ↦□ sl ∗ sl ↦*□ invariantsV`, the seven named structs of the translation's func literals
(`Closures.lean`, generated as porcupine-dag's: `gen_closures`, `TC_CLOSURES`); the package is now
a root of `etc/gen-init.py` (`SPECIAL[TC_PKG]`), whose generated `etcdraft/Init.lean` proves its
initializer gives the fact (the tables' map literals and `EmptyBag` run, not in the fact). No
axiom added. Each closure's spec is a lemma of `State__Violated.lean` (`wp_invHolds`, from the
seven methods' specs). The Go and the transcription agree, the error case included: the Go panics
in `Violated` where `State.violated` is an `EvalError`, and the transcription's fold stops at the
first violation as the Go's `return` does. (A tooling note: `etc/lean-check.py`'s incremental
re-checks of the `LeaderCompletenessInv` proof reported kernel "application type mismatch" errors on
`omega`'s auxiliary lemmas that a fresh check and `lake build` do not.)
**`trace.go` proved, but for the functions over unspecified callees and `NewTrace` (2026-11-09, branch
`trace-check-layerc-trace`).** Specs and complete proofs (no `sorry`, no axiom), each against its
`Tla/Trace.lean` definition: `parseID`, `toSet`, `isMessageEvent`, `traceError`, `Trace.Len`, `Trace.Event`,
`Trace.Init`, `TState.Equal`, `indexOf` (the first index `findIdx?`, or `-1`), `logline`, `loglineIsEvent`,
`loglineIsNodeEvent`, `loglineIsMessageEvent`, `line.msgType`, `line.isAppendEntriesRequest`,
`isAppendEntriesResponse`, `isRequestVoteRequest`, `isRequestVoteResponse`, `line.stateMatches`,
`line.confChange`, `validatePreStates`, `validatePostStates`, `oneMoreMessage`, `oneLessMessage`,
`newPending` (over a closure's spec: a method value, or a closure proved in place),
`validateAfterAppendEntries`, the actions `becomeLeaderIfLogged`, `clientRequestIfLogged`,
`advanceCommitIndexIfLogged`, `appendEntriesIfLogged`, `heartbeatIfLogged`, `appendEntriesToSelfIfLogged`,
`timeoutIfLogged`, `readyIfLogged`, `stepDownToFollowerIfLogged`, `isBecomeFollowerInUpdateTermOrReturnToFollower`,
`skipUnusedLogline`, and `receive`. The package fact (`Base.lean`) now holds the three tables
(`RaftMsgType`, `RaftMsgSubtype`, `ReceiveMessageTraceNames`) at their literals, which S6's
initialization proof must establish; `TraceRead.lean` reads them as the transcription's functions and
adds `tstateRO` (a `TState`), `linePtrRO`, `statesOut`/`tstatesOut` (fresh successor slices) and the
proof tactics (`open_trace`, `open_lineP`, `ret_nil`, `ret_single`); a local `go.NotInterface go.string`
(`Role.String()` on a constant; `notes/perennial-changes.md`). Premises `CheckTrace`'s loop invariant
must supply: a position `1 ≤ l` (and `l ≤ len` where the Go reads the line before checking), the
callee actions' premises (servers of the state, `Bag.Ok`, bounds), `appendEntriesIfLogged`/
`heartbeatIfLogged` where the Lean evaluates (`= .ok sts`), and for `receive` every message of the
state meeting `State.Receive`'s premises (no pre-vote message or snapshot, `prevLogIndex` in
`[0, 2^62 - 1)`, entries and the destination's log below `2^62`). No `int` premise beyond those: the
Go's `b != ev.Index+1` and `e != b+ev.Entries` wrap only away from the small `b`, `e`
(`add_eq_iff_small`), and `oneMoreMessage`'s `before+1` only past any count. Left: the functions whose
callees `spec.go` does not specify (`requestVoteIfLogged`: `RequestPreVote`; `preTimeoutIfLogged`,
`ignoreInLeaseIfLogged`, `sendSnapshotIfLogged`, `changeConfIfLogged`, `applySimpleConfChangeIfLogged`,
`restartIfLogged`), so `nonReceive` and `Next`; `StepLine` (`Violated`); `TraceError.Error` (no
transcription); and `NewTraceWith`/`NewTrace` (not started: its closures, the `last` map and the
bootstrap loops against `newTraceWith`'s `mapM`s; compared by reading, no disagreement found:
the same checks in an order that changes only which error, `TraceServer`'s ids in another order
before `SetIds.mk`). No disagreement between the Go and the transcription.
**`trace.go`'s search proved; `CheckTrace` blocked (2026-11-09, branch `trace-check-layerc-top`).** Specs
and complete proofs (no `sorry`, no axiom) of the remaining `IfLogged` actions, `nonReceive`, `Next` and
`StepLine`. The actions outside the workload, as the task allowed (the choice): pre-vote and check-quorum
by their flag, which `NewTrace` sets off and every action keeps: `RequestPreVote`, `PreTimeout` and
`IgnoreInLease` specified where the flag is off (`nil`), so `requestVoteIfLogged`, `preTimeoutIfLogged`
and `ignoreInLeaseIfLogged` take `ts.s.preVote = false`/`checkQuorum = false`; snapshots, configuration
changes and restarts by the line (P2, P3, P1 of `notes/trace-validation-sim.md`): `sendSnapshotIfLogged`
at a line whose message is not a `MsgSnap`, `changeConfIfLogged` at a line not a `ChangeConf`,
`restartIfLogged` at a line not an `InitState` (no successor), so `SendSnapshot`, `AddNewServer`,
`AddLearner`, `DeleteServer`, `reconfigure`, `Restart` and `HandleSnapshotRequest` stay without spec.
`applySimpleConfChangeIfLogged` is proved in full (the workload's `ApplyConfChange` lines after the
bootstrap, `AccIdle`), over new specs of `ApplySimpleConfChange` (where the Lean evaluates; its log below
`2^62`, the reconfiguration count below `2^63 - 1`; its `for range` deleting from `MatchIndex` through
`wp_map_for_range_mut_keys`) and `applyConfigUpdate`. `StepOk.lean` gathers the premises: `State.ActOk`
(the flags off, the pending bag `Bag.Ok`, the bags' total counts below `2^63`, the reconfiguration count,
every server's log below `2^62 - 1`, granted votes and configuration below `2^62`, term below `2^63 - 1`,
progress in `[0, 2^62 - 1)`), `Line.InScope` (no `ChangeConf`, `InitState` or `MsgSnap` send),
`State.MsgsOk` (`receive`'s), `TState.NextOk` (a position, the trace's servers, those, `InScope` where
the line is not a bootstrap line), `Trace.LineReach` (the states `StepLine`'s search expands: `ts` and
the same-line successors of expanded states), `Trace.StepLineOk` (every expanded state `NextOk`, every
reached state `State.ViolOk` when checked); and the search's steps as named functions (`stepInnerF`,
`stepOuterF`, `stepRound_eq` by `rfl`) with their laws. Specs: `nonReceive` (`NextOk`'s parts at a
non-bootstrap line, `tr.nonReceive ts = .ok sts`), `Next` (`ts.NextOk tr ∧ tr.next ts = .ok tss`),
`StepLine` (`tr.StepLineOk ts invariants` and no `StepLineRel ts invariants (.error e)`; it returns the
`StepLineRel` result, `Branched`/`Violation` related, `Bad` unconstrained; partial correctness, its loop
needs no fuel). `TraceError.Error` is not specified: no function of the checker or `Main` calls it
(`Main` only tests `err != nil`). `Result.TLCOK` was done. `NewTraceWith` and `NewTrace` proved
(`NewTrace.spec` unchanged): `NewTraceWith`'s spec is `NewTrace`'s for any flags, its post the heap part of
`traceRO` (`traceHeapRO`, `TraceBuild.lean`, with `traceRO_of_heap`), `NewTrace` adding `Trace.Valid`;
`ParseRole` specified (`RET #s`). The differences read as harmless are proved so (`TraceBuild.lean`):
`SetIds.mk` depends only on membership (`SetIds.mk_congr`: the Go collects the servers interleaved),
the per-server bootstrap ranges OR-ed are `bootstrapOf`'s flags (`bootFlags_*`), the Go's
`bootstrapConfs` filter on the global flag and `nid = i` is the server's own flag (`global_flag`), the
checks' order changes only which error. No disagreement. Not done: `CheckTrace`.

`CheckTrace`'s loop invariant, line `l` with frontier `F` (Lean `frontier`, Go slice of `TState`s) and
result so far `r`: `1 ≤ l ≤ len + 1`; `∀ r', tr.CheckFromRel inv (len + 1 - l) l F r r' →
CheckTraceRel tr inv r'` (as `RunRel.from_init`); `F` deduplicated (`memEq`); every `ts ∈ F` at line
`l` with `tr.StepLineOk ts inv` and no `StepLineRel ts inv (.error _)`; and the Go's `r.Branched` the
Lean's. Its premises are not maintainable from what `CheckTrace.spec` assumes (`traceRO t tr`, so
`Trace.Valid tr` only), for three reasons, each with a counterexample:
- **evaluation errors**: `CheckTrace.spec` covers the traces whose search fails (`CheckTraceRel`'s
  `evalError` results), where the Go panics with an `EvalError` and recovers; every callee's spec takes
  `= .ok` (or `.error _ => False`), since a Hoare triple names a returned value. Counterexample: the
  one-line trace `InitState` of node `"1"`, `log 0`, `commit 1`, `conf [["1"], []]` is `Valid` and
  `checkTrace … true`'s initial `violated` is an `EvalError` (`LogInv`'s `Committed`, `SubSeq(log, 1, 1)`
  of an empty log): `Violated`'s spec does not apply. Proving the spec needs panic-aware specs (a
  postcondition at `PanicV` of the `EvalError`) of `Violated`, `SubSeq`, the `EvalM` invariants and
  actions, `Next`, `nonReceive`, `StepLine`; or a premise that the search does not fail (`∀ r',
  CheckTraceRel tr inv r' → r'.evalError = none`, which `Main`'s accepted run gives).
- **lines outside the workload**: a `Valid` trace may hold a `ChangeConf`, a non-bootstrap
  `InitState` or a `MsgSnap` send (`NewTrace` accepts them); `nonReceive`'s `Line.InScope` fails there.
  Needs either a premise on the trace (every non-bootstrap line `InScope`: layer B's P1-P3 give it of the
  workload's trace) or specs of the seven actions left out, and then `HandleSnapshotRequest` in
  `Receive`'s.
- **bounds**: `StepLineOk`'s bounds hold of every reachable state only through an invariant of the
  whole specification (logs, terms, counts and progress grow by at most a bounded amount per step, from
  the trace's `numBound`): a pure proof over every action, not done. One bound has no such proof:
  the configurations' sizes below `2^62` (`IsQuorum`'s), which come from the events' `conf` lists, which
  `Event.Bounded` does not bound (a `Valid` trace whose bootstrap line lists `2^62` distinct ids is not
  excluded in the model); `Event.Bounded` would need the lists below `numBound`.
So `CheckTrace` is not proved. The options for the user: (a) a premise `CheckTrace.spec` takes, stating
what the search needs (no evaluation error, the search's states `StepLineOk`, the lines in scope), which
`Main`'s proof discharges from layer B (the run's states are raft's, bounded by the time receipts); or
(b) the panic-aware callee specs, the seven actions and the reachability bound, with `Event.Bounded`
strengthened.

**`CheckTrace` proved under `Trace.CheckTraceOk` (2026-11-09, branch `trace-check-checktrace`; Q10 (a'),
pending the user's veto).** `CheckTrace.spec` takes one more, pure, premise, its conclusion unchanged:
`Trace.CheckTraceOk tr invariants` (`CheckOk.lean`), the conjunction of
- `tr.LinesInScope`: every line outside the bootstrap `Line.InScope` (no `ChangeConf`, no `InitState`,
  no `MsgSnap` sent), a property of the trace alone;
- `∀ ts, tr.Reach ts → ts.s.SearchOk`: every state of the trace specification reachable from
  `TraceInit` (`Trace.Reach`, closed under `Trace.next`'s successors: a superset of what the search
  looks at) meets the actions' bounds (`State.Bounds`, `State.ActOk` but its flags) and the messages'
  (`State.MsgsOk`);
- `∀ res, CheckTraceRel tr invariants res → res.evalError = none`: the search raises no evaluation
  error (the Go would panic with an `EvalError` and recover).
Proved (no `sorry`, no axiom): `CheckTrace.wp_proof` over the specs of `Trace.Init`, `Trace.Len`,
`Trace.StepLine`, `indexOf`, `State.Violated` (the loop invariant above; the Go's running `r.Branched` is
`brOf`, the line's branching so far; the `invariants` branch split without substituting the flag, so the
search's proof is written once); and the pure lemmas that reduce `StepLine`'s premises to the three parts:
every reached state has the trace's servers and `PreVote`, `CheckQuorum` off (`Trace.Valid.reach_frame`,
`Frame.lean`: every action builds its state with `{ st with … }`, `State.Frame` per action and per
`IfLogged` action, `Trace.next_frame`), a reached state's `l ≥ 1` (`Trace.Reach.l_pos`, from `Trace.next_l`), the states `StepLine` expands
reached (`Trace.LineReach.reach`), so `Trace.StepLineOk` of every reached state
(`Trace.CheckTraceOk.stepLineOk`, with `State.ActOk.violOk`: `Violated`'s bounds are among the actions');
the states a line's search returns reached and at the next line (`Trace.StepLineRel.reach`), a
violation's name never `""` (`Trace.StepLineRel.violation_ne`); `StepLoop`, `CheckLineRel`, `CheckFromRel`
and `CheckTraceRel` deterministic (`*.det`), so a run through every line is the search's only result
(`Trace.RunRel.checkTraceRel_eq`) and has no evaluation error (`Trace.RunRel.noEvalError`).
One difference between the Go and the transcription found, harmless: on an evaluation error, the Go's
result keeps `r.Branched` as the line's earlier frontier states set it (`Result{..., Branched: r.Branched}`
in the deferred function), where `CheckFromRel.error` keeps the branching at the line's start; both are
failures (`TLCOK` false), and the premise excludes the case.

**`Main`'s remaining obligation (S7)**, for the trace `tr` that `NewTrace` returns on its events (item 2
superseded by "Part 2 proved" below, 2026-11-09: it is now `tr.ConfsBounded`, the events' configuration
lists below `numBound`):
1. `tr.LinesInScope`: layer B's P1-P3 (no restart, no configuration change after the bootstrap, no
   snapshot sent: raft sends one only for entries missing from storage, and the harness never compacts);
2. `∀ ts, tr.Reach ts → ts.s.SearchOk`: an invariant of the trace specification, over every action
   `Trace.next` can take from a reached state (not only the run's states: the search also expands a
   receive line's intermediate states and the successors it then discards), proved by induction on
   `Trace.Reach` (the trace's servers and the flags off are already proved, `Trace.Valid.reach_frame`,
   and give the invariant its frame): the bags' messages distinct
   (`Bag.add_nodup`), no pre-vote message and no snapshot (none sent: the flags off, and the `MsgSnap` lines
   excluded by part 1), `prevLogIndex ≥ 0`, and the numbers below their bounds (logs, entries, terms,
   granted votes, configurations, progress, the bags' counts, `reconfigCount`), each bounded by the
   trace's numbers (`numBound`, the bootstrap's logs and configurations) plus a count of the lines so
   far. One input is not yet in `Trace.Valid`: the configurations' sizes come from the events' `conf`
   lists, which `Event.Bounded` does not bound; `Main` has them of raft's events (three voters), so the
   invariant takes them as a premise on the events (or `Event.Bounded` gains them);
3. `∀ res, CheckTraceRel tr true res → res.evalError = none`: `Trace.RunRel.noEvalError` of the run
   layer B's simulation carries (`Trace.RunRel tr tr.len ts`), which `Main` needs anyway for `TLCOK`.
Part 2 is the one pure proof left, workload-agnostic but over every action of `Tla/Spec.lean`; it
belongs to the checker package (`Trace.Valid.reach_searchOk`, `notes/decisions.md`, Q10, "Deferred"),
which then drops it from `CheckTraceOk`, leaving `Main` the configuration lists' bound in `NewTrace`'s
premise. `Main` builds the premise with `Trace.RunRel.checkTraceOk`. The `TraceAccepts` corollary rests
on layer B's run (`Trace.RunRel.accepts`) and the Lean transcription; with `CheckTrace.spec`, the Go
checker's verdict agrees.

**Review round 2 (2026-11-09, fresh `spec-reviewer`): no first-tier finding.** Second tier repaired:
the notes' claims that raft's traces are in the class qualified (part 2 open), part 2's owner stated
(the checker, above), the corollary's basis corrected, an intro law `Trace.RunRel.checkTraceOk`. Third
tier: "no configuration change" now "no `ChangeConf`"; `State.Bounds` duplicating `ActOk`'s body,
`MsgsOk`'s last conjunct redundant under `Bounds`, the names: left (`ActOk` is in the frozen callees'
statements).

**Review of the changed `CheckTrace.spec` (2026-11-09, `spec-reviewer`, fresh).** Round 1: the
post fits `Main` (with `RunRel`, `checkTraceRel_eq` pins the result to `{ ok := true }`), the spec is
true of `check.go` on every outcome, part 3 and `Trace.Reach` are the right shapes. First tier, both
repaired: (T1-1) this plan still claimed `CheckTrace` and `TraceAccepts` equal on every trace (the
"Trust base" paragraph and layer C's spec sentence): now qualified, the proof transfers the Go
checker's evidence to the Lean transcription only on the class `CheckTraceOk` admits; (T1-2)
`CheckOk.lean`'s header said part 2 follows for bounded events (it needs the configurations' lists
bounded too) and the spec's header called part 2 "bounded" only: both say what part 2 holds. Second
tier: (T2-1) part 2 exports the checker's overflow margins to `Main`; it should be a lemma of the
checker package, `Trace.Valid` (with `Event.Bounded` covering the configurations' lists) and
`LinesInScope` giving it. Taken in part: the conjuncts provable now are proved and left the premise
(the servers and the flags, `Frame.lean`; `SearchOk` is now `State.Bounds ∧ State.MsgsOk`); the rest
stays a premise until the invariant is proved, since a `sorry` in its place is not allowed in a
committed state: when it is, `CheckTraceOk` loses part 2 and `Event.Bounded` gains the lists' bounds
(the lemma `Trace.Valid.reach_searchOk` then states it). (T2-2) `LinesInScope` has no law from the
events `Main` holds (the bootstrap flags are `bootstrapOf`'s): left to S7, where layer B's form of
P1-P3 decides the law's shape. Third tier: `Trace.Reach`'s docstring (a superset of what the search
looks at), `State.MsgsOk`'s (its bag conjunct), `TraceAccepts evs false false`: repaired; part 3
unnamed: left.

**Part 2 proved: the reached states bounded (2026-11-09, branch `trace-check-reach`).**
`Trace.Valid.reach_searchOk : tr.Valid → tr.LinesInScope → tr.ConfsBounded → ∀ ts, tr.Reach ts →
ts.s.SearchOk` (`Reach.lean`, no `sorry`, no axiom), by induction on `Trace.Reach` over every action
`Trace.next` takes. The invariant `State.Inv K`: every server's log, term, commit index, progress and
configuration size within `K` (commit and progress also `≥ 0`), its log's configuration entries' sizes
within `K`, its granted votes a sorted list of servers; both bags without duplicates, counts positive,
their total count within `K`; every message of either bag of the workload's kinds (no pre-vote message,
no snapshot), from a server, its copied fields (`term`, `prevLogIndex + len(entries)`, `commitIndex`,
`matchIndex`, its entries' configurations) within `K`; the reconfiguration count within `K`. A step that
stays at its line (every successor `receive` gives: a reply moves one message from `messages` to
`pendingMessages`, the logs and terms a receiver takes come from the message) keeps `K`; one to the
next line (a send, a client request, a timeout, a configuration applied) needs at most `K + 1`, so a
state at line `l` has it at `numBound + l` (`Trace.Valid.reach_inv`; `l ≤ len + 1`). The granted votes
are bounded by the servers (`Nodup.length_le_of_subset`; `tr.server.length ≤ 2 * len`, from
`newTraceWith`), not by a count of steps, since a vote response is tallied at its line without the
proof tracking which receive successors step. The lines out of scope are used only where an action
would break the invariant or needs more state: a `MsgSnap` sent (a snapshot message), a restart (the
durable state), a `ChangeConf` (`sendSnapshotIfLogged_nil`, `restartIfLogged_nil`,
`changeConfIfLogged_nil`); the sent `AppendEntries`' `prevLogIndex` is bounded by the line's event
(`Event.Bounded`). **The one bound the trace did not give, the configurations' sizes** (`IsQuorum`'s
`len * 2`), comes from the events' configuration lists: a line's `conf` incoming list (the configuration a
bootstrap line records) and a configuration change's `newconf` (a bootstrap `ApplyConfChange`'s), from
which `newTraceWith` builds the initial configurations and the bootstrap log's configuration entries,
the only configurations an in-scope trace ever applies. Route taken (the least invasive sound one):
`Event.Bounded` is `NewTrace`'s premise, not something its Go code establishes (it reads the lists
without a bound), so strengthening it would change `NewTrace.spec`; instead the bound is a
trace-level conjunct of `CheckTraceOk`, `Trace.ConfsBounded` (`∀ ln ∈ tr.lines, ln.ev.ConfsBounded`:
both lists shorter than `numBound`), stated on the trace's lines' events, which `Main` discharges from
raft's three voters (the lines' events are the events it passed `NewTrace`). No action's bound is false:
nothing stays a premise beyond the lists. So `CheckTraceOk` is now `tr.LinesInScope ∧ tr.ConfsBounded ∧
(no evaluation error)` (weaker: part 2 `∀ ts, tr.Reach ts → ts.s.SearchOk` follows from `Trace.Valid` and
the first two); `CheckTrace.spec`'s conclusion is unchanged, its proof takes part 2 from the lemma
(`Trace.CheckTraceOk.nextOk`, `.actOk`), and `Trace.RunRel.checkTraceOk` takes `tr.ConfsBounded` in
place of the reached states' bounds. `Main`'s S7 obligation 2 is now only `tr.ConfsBounded`.

**Review of the weakened `CheckTrace.spec` (2026-11-09, fresh `spec-reviewer`, at `8e14d2ceca`): no
first-tier finding** (the triple true of `check.go`, its post what `Main` inspects, the premise only
weaker, the proof using each part as stated). Second tier: (S-1) part 2 would sit better on `NewTrace`'s
premise, carried by `Trace.Valid`, since `Event.Bounded` already bounds fields only the search needs
(the messages' numbers): taken in its minimum form, the law `Trace.confsBounded_of_newTrace` (events
bounded ⇒ the trace's lines bounded), so `Main` needs no internal lemma; the placement kept, as the
delegating session's instruction for this branch (strengthen `Event.Bounded`/`Trace.Valid` only for what
`NewTrace`'s code establishes; otherwise a trace-level conjunct of `CheckTraceOk`) and to leave
`NewTrace.spec` unchanged: the user may move it (one conjunct in `Event.Bounded`, `hcb` dropped from
`reach_searchOk`). (S-2) `LinesInScope` still has no law from the events (round 2's T2-2): left to S7,
as before. Third tier repaired: the spec header says part 3 is a premise on the search's own runs and
what the Go returns then, that only the incoming `conf` list is bounded (`Event.ConfsBounded`'s
docstring, which also says every line is bounded though only bootstrap lines feed configurations),
`RunRel.checkTraceOk`'s reference reworded, `Rep.lean`'s header names the new bound; Q10's veto status
unchanged.
Acceptance (after merging `trace-check` at `452d95929b`): full `lake build` green, `etc/tcb-report.py --check`
(baseline unchanged: 806 axioms, 4 `sorry`s), `etc/gen-init.py --check`.

**`Main`'s pure obligations, proved (2026-11-09, branch `trace-check-mainpure`).** Everything `Main`
supplies to `NewTrace` and `CheckTrace` is one pure lemma, `TraceCheck.mainPure`
(`tracecheck/MainPure.lean`, no `sorry`, no axiom), from facts about raft's events `L : List TraceEv`
stated in raft's values: `RunAccepted L` (`newTrace (L.map evConv) = .ok t` and `t.RunRel t.len ts`),
`ScopeOk L`, `∀ e ∈ L, e.NumsBelow K` with `K ≤ 2^40`, `L.length < numBound`, `∀ e ∈ L, e.ConfsWithin n`
with `n < numBound`; it gives `NewTrace`'s premises on `L.map evConv` (`Event.Bounded`, the length),
`newTrace`'s success, `t.CheckTraceOk true`, the search's only result `{ ok := true }` and
`TraceAccepts`. The parts: (1) **the lines in scope** (round 2's T2-2, the weakened spec's review S-2),
`linesInScope_of_scopeOk`: `ScopeOk L` says each event, after those before it, is in scope
(`TraceEv.InScope`: no `ChangeConf`, no `InitState`, no `MsgSnap` sent) or is bootstrap-named while its
node is `Unbooted` (has logged only bootstrap-named lines: `¬ TraceSim.booted`), and such a line is
flagged by `bootstrapOf` whatever follows it (`bootstrapOf_unbooted`: its node's first bootstrap-named
line is at or before it, its first other line after it); every line's node is a server
(`newTraceWith_nid_mem`). `ScopeOk` is kept event by event (`scopeOk_nil`, `scopeOk_snoc`), as `simInv`'s
ASCII clause is: P1 makes `InitState` its node's first event (at `StartNode`), P3 rules out `ChangeConf`
(the bootstrap's changes are logged `ApplyConfChange`, in scope), P2 a `MsgSnap`. No event raft logs in
the workload breaks scope. (2) `confsBounded_of_events` (through `Trace.confsBounded_of_newTrace`).
(3) `Trace.RunRel.checkTraceOk`/`noEvalError` of the run (existing). (4) `evConv_bounded`. The ASCII
premise needs no pure lemma (`ConvertEvents.spec` takes `simInv`'s clause). **What layer B must export**
(at the end of the run, from `simInv`): `RunAccepted L` (`TraceSimEnd.lean`'s `simRun_runRel` gives it
from `SimRun` once the whole trace's initial state and servers are the voters', `t.init = simInit C`,
`t.server = t.initSrv = confAbs C`, which layer B's bootstrap clause owes, and from `newTrace`'s
success, also owed); `ScopeOk L`, `NumsBelow`, `ConfsWithin |C|` as `simInv` clauses per event; and the
event count. `TraceSimGhost`/`TraceSimEnd` are not importable outside raft (`etc/api/raft.txt` lists
`InvTrace`, `TraceSim`), so the export is an API addition. **Found: the step bound.** `numBound` is
`2^40`, so `Event.Bounded` needs every term and index, and `NewTrace` the number of events, below `2^40`;
the plan's step bound `n < 2^61` does not give that (Goose's semantics allows unboundedly many elections:
terms and the event count grow with the steps). So either `Main`'s adequacy bound (and the time-receipt
bound layer B uses) is at most about `2^40`, or the checker's `numBound` is raised (the reached states'
margin `numBound + len + 1` must stay below the actions' `2^62`): the user's choice for S7.

### D. The harness and Main (the workload)

The concurrent harness (`concurrent.go`, its Goose translation needs no change): each replica a
`raft.Node` with its application goroutine, the network's goroutines, the drivers, the locked
recorder. Its proof uses the node API's specs (`StartNode`, `Node.Step`, `Ready`, `Advance`,
`Tick`, `Propose`, `Status`, `Stop`, `ReportUnreachable`) and discharges layer B's premises (it
never restarts, compacts or proposes a configuration change). The recorder's lock invariant holds
layer B's ghost state: its `TraceEvent` is the logger spec's linearization point. `Main`'s proof:
the checker's spec and layer B's invariant at the end (the whole trace accepted).

## Order of work

1. **S1 the Go for the proof**: the package split (C), the core rewritten without `fmt` and
   friends, a `Main` for the closed program, `etc/goose.py` projects for the harness and the core;
   the differential tests kept as the regression check.
2. **S2 the Lean transcription**: pure definitions, read side by side with the TLA+ text. Not a
   trust question (above): a Lean definition differing from the Go makes the checker's proof (S6)
   fail. An executable version run against TLC would only find such a difference earlier;
   optional.
3. **S3 the hooks' and logger's specs** (A): the `spec` skill's process; the eleven proofs; raft's
   invariant carries the logger; raft and its dependents rebuilt.
4. **S4 the simulation on paper** (B): `R`, each hook's correspondence, determinism, the invariants'
   mapping; reviewed; this plan amended and frozen.
5. **S5 the simulation in Lean** (B).
6. **S6 the checker's proof** (C).
7. **S7 the harness, `Main`, adequacy** (D), `Results.lean`, `etc/tcb-report.py` collection.

S1, S2 and S3 are independent of each other. S4 needs S2's definitions (and S3's event function).

## Probe set (named 2026-11-08, `notes/spec-first-plan.md`, "Probe": an easy and a hard proof per package)

- Layer C (package `etcdraft`, the checker): **easy** `Result.TLCOK` (done 2026-11-08, about ten
  minutes; no spec problem found); **hard** `(*State).Timeout`, chosen by its invariant: the
  search's copy-on-write discipline (a state built by an action is a `clone`, its changed server a
  `mut` copy, everything else shared and read-only), the invariant every action's spec rests on and
  no review checks; its path: `Set.Has` (done), `State.GetConfig` (done), `Server.copy` (done; `serverOwn`, `Own.lean`), `State.clone` (done; `stateOwn`), `State.mut` (done; `stateOwnHole` and its closing law, which
  needs the server list without duplicates: a fact S6's invariant carries),
  then `Timeout` (a mutable representation of a fresh clone and copy, persisted once
  written). **Done 2026-11-08**, the whole path in about a working day (the five callees and
  `Timeout`, no `sorry`; `Timeout` itself about two hours). Spec problems found by the proofs, all
  in layer C's representation (round 4 then found one in a triple, `mut`'s, below):
  1. the server list must be duplicate-free for `mut`'s closing law (`stateOwnHole_close`):
     first a premise of `Timeout`'s spec, now (round 4, S1) a conjunct of `stateRO`, `stateOwn`
     and `stateOwnHole` (`State.Server` is never written; `newTrace` builds it with `SetIds.mk`,
     duplicate-free by `SetIds.mk_nodup`, `Rep.lean`);
  2. strings: Perennial's `stringToGoString` goes through `String.toUTF8`, which no proof can
     evaluate on a constant (`"StateFollower"`), so a role comparison in the Go could not be
     decided; the predicates now relate a Go string to a Lean string by `strRel` (ASCII, a byte per
     character; `Rep.lean`), injective (`strRel_inj`) and decidable on constants. A premise
     follows on `NewTrace`'s events: their strings ASCII (raft's names and ids are);
     `notes/decisions.md`, "Layer C's strings: `strRel`, ASCII";
  3. term bounds: `Timeout`'s `CurrentTerm + 1` must not overflow; its spec takes
     `currentTerm < 2^63 - 1` (round 4, S2: first `numOk`, stronger than the Go needs). S6's
     loop invariant must give it at each action, and round 3's "every number below
     `(lines + 2) · numBound`" does not (nothing bounds the lines below `2^40`; round 5, S1). It
     carries instead: every server's term, durable term and message term below `numBound`. This
     holds: the initial terms are the events', bounded; the only increment is `Timeout`'s
     (`spec.go:245`), whose successor `timeoutIfLogged` keeps only when its term is the line's
     event term (`trace.go:623-625`); every other term is copied from a server's.
  Also learned (proof mode, not spec): a struct literal spanning lines must start its fields on a
  line of their own (Lean's `checkColGe`), `W64 1` and `go!"..."` need parentheses inside a
  record update, and a persisting update at a return needs `iapply wp_fupd` before the last
  `wp_auto`.

**Review round 4 (`notes/trace-validation-reviews/c-r4.md`), on the Probe's changes:** one
first-tier finding, repaired: `State.mut.spec` required server `i` not yet copied, which the Go
breaks (`reconfigure` and `ApplySimpleConfChange` call `mut(i)` twice on one clone); the premise
is gone, the proof freezes the old copy first (`serverOwn_persist`). Second tier, repaired: S1
(duplicate-freedom into the predicates, above), S2 (the term bound, above), S4 (the law
`strRel_eq_iff`: Go `==` on related strings is Lean `=`, which every role or subtype comparison
uses). Left to later stages: S3 (layer B: `MessageType.String()`'s spec, when strengthened, states
its value as a `go!` literal, not through `stringToGoString`, so `strRel` holds by `decide`), S4's
second half (`durableOf` on a copy being written, with `persistState`'s proof in S6). The
`strRel` switch itself was found sound and `NewTrace`/`CheckTrace` still say what they should
(modulo Q7). **Round 5 (`c-r5.md`): nothing first-tier**; the repairs checked (the sixteen `mut`
call sites, duplicate-freedom kept by every action and given to `NewTrace` by `SetIds.mk_nodup`);
its S1 (the term bound S6 carries) and T3/T4 (this plan's wording, the docstrings) repaired in the
notes. Layer C's Review is clean modulo Q7.
  `CheckTrace`'s own loop waits on Q7.
- Layer A/B (raft's hooks, increment 2): waits on Q6's statements (the plan of S4: one hook with its
  phase through `send`'s callers).

## Draft: layer C's specs drafted (2026-11-08), in Review

The checker's spec, independent of Q4-Q6 (Q4 changes only the invariants' list both
transcriptions check): `Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/etcdraft/`
`NewTrace.lean` (`NewTrace(events)` returns an error exactly when `newTrace` refuses, else a
read-only trace holding `newTrace`'s) and `CheckTrace.lean` (`CheckTrace(t, invariants)`'s
result holds `checkTrace`'s, on the fields it records), over the representation predicates of
`Proof/.../tracecheck/etcdraft/Rep.lean` (persistent: a trace and its initial state are never
written; canonical where the Go compares by value) and the package fact of `Base.lean` (`True` in
the Draft, strengthened by S6's proofs). Premises: the events' numbers in `[0, numBound)`,
`numBound = 2^40` (`Event.Bounded`), and fewer than `numBound` events. Decided by the agent: one persistent predicate per
Go value rather than ownership (nothing the specs relate is written after `NewTrace`), and the
result related on the fields the Lean `Result` has (the Go's debugging fields unconstrained).

Review round 1 (`notes/trace-validation-reviews/c-r1.md`): `CheckTrace.spec` was false (F1: it
accepted traces `NewTrace` never builds, on which the Go panics: `traceRO` now carries
`Trace.Valid`, `NewTrace` establishes it; F2: the Lean transcription set `branched` at a
violation where the Go returns first: `stepRound` and `checkFrom` now follow the Go's order, a
debugging field only, `tlcOK` unchanged; the Lean and Go checkers agree again on five traces, the
two invariant-violation witnesses included). Also: the trace's numbers bounded by `numBound =
2^40` (S2: the Go's `make` of a bootstrap log), `matchIndex` related at every id (S3), a spec for
`Result.TLCOK` (S4), the predicates' `Persistent` instances (S5), pure premises inside the
triples. Open for S6 (S1): `lineFuel` (the logs' lengths in the state the line starts from, plus 8) bounds the Go's unbounded
per-line loop only given that the append requests matching one line carry the same entries, a
reachability invariant of the specification; S6 states it or replaces the fuel by a counting
bound. Sealing the predicates behind laws (T2) is left to S6 too.

Review round 2 (`notes/trace-validation-reviews/c-r2.md`): one first-tier gap, `stateRO` did not
say the server map's keys are exactly the servers (a configuration may name a node outside
`Server`, and the Go decides by lookup): added. Round 1's repairs, the Lean change included,
checked (15 traces and a crafted one agree). `lineFuel` (S1) is Q7.

**Review round 3 (`notes/trace-validation-reviews/c-r3.md`): nothing first-tier; layer C's Review is
clean modulo Q7** (`CheckTrace.spec` holds given that the fuel suffices). Its option (c) for Q7 is
added there. Facts S6's loop invariant must carry (round 3's T3): every message's `prevLogIndex ≥
0`, every `matchIndex ≥ 0`, the state's server set the trace's with the map's keys exactly it,
every number below `(lines + 2) · numBound`. Branching is still untested by a run (T4: two
snapshots of one index sent with different commit indices would build a witness).

## Draft: S2 done (2026-11-08)

The Lean transcription, `Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/etcdraft/Tla/`
(`Types`, `Spec`, `Invariants`, `Trace`, `Check`; namespace `Perennial.EtcdGrove.Etcdraft`): all of
`etcdraft.tla` (every action, the five next-state relations, the invariants) and `Traceetcdraft.tla`
(the trace's constants, the `IfLogged` actions, `TraceNext`, `stepLine`), and `checkTrace`,
`Result.tlcOK`, `traceAccepts` (the corollary's statement), mirroring the Go function by function.
Decided by the agent (the options and the reasons, `notes/spec-first-plan.md`, "Who decides"):

- numbers `Int` (TLA+'s), not 64-bit words: the statement's meaning stays TLA+'s, and the
  checker's proof (S6) carries the bounds the Go's `int` needs (the workload's terms and indices);
- servers `Nat`, sets sorted duplicate-free lists, the bag a list of messages with counts, as the
  Go's: `=` on values is derived structural equality, decidable, so the definitions run, and S6
  relates like to like;
- where TLC fails evaluating, `EvalM := Except EvalError` (the Go panics and `CheckTrace`
  recovers);
- `stepLine`'s loop takes fuel (`lineFuel`: the steps one line can take), which Lean's termination
  needs and the Go's loop does not; S6 shows the fuel is never exhausted.

Checked by running it (`#eval`, through `cmd/leanexport`, which writes a trace as a Lean file): on
16 traces (the five clean seeds, the four mutants, five full-configuration traces, two concurrent
ones) its verdict and failing line equal the Go checker's (and so TLC's), and on the
evaluation-error witness (a commit index past the log) it fails with the same error. Not part of
the trust argument (the plan's "Trust base"): S6's proof is what ties it to the Go.

## Draft: S4 drafted (2026-11-08), Review clean (round 11); the freeze blocked on Q4, Q5, Q6

`notes/trace-validation-sim.md`: the abstraction `α` (a server's variables, the messages, the bags
as new ghost state with a token per message in flight), the relation's phases (idle, handling a
received message), determinism line by line, the invariants (two routes), the premises P1-P7 and
increment 2 of the hooks' specs. Found while drafting it: a fifth place where `etcdraft.tla` does
not fit raft (an append request's commit index, `notes/raft-trace-validation.md`, item 5),
witnessed with `MaxInflightMsgs: 1`, not reached by `DefaultCConfig`: premise P5, discharged by the
harness's configuration, the statement unchanged. Review round 1 (a fresh `spec-reviewer`,
`notes/trace-validation-reviews/s4-r1.md`): four first-tier findings, two of them making the closed
theorem false with the harness as it was (Q3), a sixth gap (`notes/raft-trace-validation.md`, item
6: a voter that knows its term's leader; at most three voters, P9), the bags' phantom replies;
revision 2 of the note answers each. Round 2 (`notes/trace-validation-reviews/s4-r2.md`): two
first-tier findings that make the closed theorem false with `DefaultCConfig` (Q4: upstream's
`LeaderCompletenessInv` is not an invariant of raft; Q5: gap 6 with three voters), both the user's;
second-tier ones on the contract and the invariants' facts, answered by revision 3. The Review
cannot clear, so no freeze, until Q4 and Q5 are decided. Round 3 (`notes/trace-validation-reviews/s4-r3.md`): the logger
contract must hand over the event (A1), and `MoreUpToDateCorrectInv` is not raft's either (A2:
`notes/raft-trace-validation.md` item 8, TLC confirms; five voters and cut batches, so not reached
by `Main`: P5 strengthened, the statement unaffected); second tier on the invariants' facts, the
bootstrap, `Advance`'s stopped branch, the phase threaded through raft's internal functions, the
tokens' key; revision 4 answers each. Round 4 (`notes/trace-validation-reviews/s4-r4.md`): no further behavior the
specification cannot follow (with Q4's guard and Q5's FIFO network); the inflight bound is a
workload bound raft cannot see (a proposal budget: Q6), the bootstrap mode replaced by a per-node
flag, the invariants' clauses and routes corrected; revision 5. Round 5 (`notes/trace-validation-reviews/s4-r5.md`): none
either; the tokens need their link position for P9, layer B's other premises must enter through
gated API premises (both Q6), `QuorumLogInv` is not raft's (a copy of raft's `histsOk`); revision 6. Round 6 (`notes/trace-validation-reviews/s4-r6.md`): none either;
two more API gaps (P2's compaction, the tokens' order needs an exclusive cursor), both Q6; the
reviewer saw nothing else blocking a freeze once Q4-Q6 are decided; revision 7. Round 7 (`notes/trace-validation-reviews/s4-r7.md`): one
first-tier finding, P9's voter count with no channel into raft (a premise of the allocation, Q6);
second tier on the storage bound, the cursor's ownership, `QuorumLogInv`'s clauses; nothing else
blocking once Q4-Q6 are decided; revision 8. Round 8 (`notes/trace-validation-reviews/s4-r8.md`): round 7's
repairs right; one first-tier gap (`Ready`'s snapshot under the gate: Q6), second tier on the gate's
place, the inherited commit, the leader's own `Match`, the hand-off clause; revision 9. Round 9 (`notes/trace-validation-reviews/s4-r9.md`): two
one-sentence first-tier gaps (`storBnd`'s `c = 0`; the gate half moved to `reTrace`), the
allocation's order, untraced clients' pure fact, `reNoSnap`; revision 10. Round 10 (`notes/trace-validation-reviews/s4-r10.md`): one
first-tier clause (`RestartNode` keeps its nil logger), the permit `⌜False⌝`, `memStorage_isStorage`'s
premise, what reviving `reNoSnap` touches; revision 11. The reviewer saw nothing first-tier left
once that clause is in. **Round 11 (`notes/trace-validation-reviews/s4-r11.md`): nothing
first-tier; the Review is clean.** Its second-tier points (`RestartNode`'s premise named
consistently, the allocation's premises conditional on a traced cluster) and third tier are in
revision 12. What remains before the freeze is the user's: Q4 and Q5 (the closed statement is false
until they are decided) and Q6 (the node-API changes, to present side by side with the current
specs; Q5's choice decides whether the per-link cursor is among them). Test and Probe come with
increment 2's statements.

## Draft: S3 increment 1 done (2026-11-08)

The hooks' design, its open points (the call sites, the update's ghost: settled with S4) and
Q1: `notes/trace-validation-hooks.md`. Increment 1, the nil-logger half, is in: the thirteen specs
(the eleven hooks, `traceEvent`, `traceNodeEvent`) and proofs, the field and `TraceLoggerOk` in
raft's invariant, the call sites, the constructors' premise (Q1) and its clients; raft's build
green again (`notes/decisions.md`, "The trace hooks' specs, increment 1: no logger"). Increment 2,
the logger's contract, waits for S4 (what the hook hands the logger, the update's ghost).

## Draft: S1 done (2026-11-08)

- `examples/raft/tracecheck` is a Go module of its own (`go.mod` replaces raft by the local fork
  checkout `.lake/raft-trace`, until the fork commit is pushed: then its pseudo-version and an entry
  of `etc/goose.py`'s `GO_MOD_PINS`); project `tracecheck` of `etc/goose.py` translates its packages
  `.` (the concurrent harness and `Main`) and `./etcdraft` (the checker core) into the main tree.
  Both translations build (`lake build` of their Code and GeneratedProof modules, 2026-11-08).
- The checker core (`etcdraft`) uses on its proved paths only slices, maps, structural equality
  and panics (`EvalError`, recovered in `CheckTrace`): no `fmt`, `strings`, `sort` or hashing (those
  only in `String`/`Error` methods); a hand-written decimal parser for ids; typed `TraceError`s.
  The NDJSON reader moved to `etcdraft/ndjson`, the porcupine model (and a canonical state key, for
  porcupine's hashing and the state-space test) to `etcdraft/pmodel`; neither is translated.
- `Main` (`main.go`): `RunConcurrent(DefaultCConfig())`, then
  `ConvertEvents` (raft's events to the checker's, in memory, as the NDJSON path reads them:
  `TestConvertMatchesNDJSON`), `NewTrace`, `CheckTrace(tr, true).TLCOK()`, panic otherwise.
  `TestMainRuns` runs it.
- The harness's files Goose sees (`concurrent.go`, `main.go`: `with_tla || goose`) draw their
  random choices from `primitive.RandomUint64` (as the other harnesses: `below`, as
  `examples/raft/kvreconf`'s), so the configuration has no seed, and use no `encoding/json`
  (Perennial models neither it nor `math/rand/v2`); the deterministic driver and `WriteNDJSON`
  (`sim.go`, seeded `math/rand/v2`) are `with_tla && !goose`, the tests `with_tla`.
- Not yet: the generated initializers (`etc/gen-init.py`; the checker's done, layer C) and links of the two packages, which come
  with their specs (the rest of Draft).

## Risks

- **`TraceInit` reads the whole trace** (`TraceServer`, the bootstrap lines up to each server's
  first other line): handled by the bootstrap premise (the bootstrap segment comes first and
  determines it); a server added later (configuration changes) would need more.
- **Determinism** may fail for a line the analysis missed (two matching messages differing in an
  unlogged field); none of the recorded traces branches.
- **The invariants**' mapping: `MoreUpToDateCorrectInv` (every pair of servers' logs) and
  `QuorumLogInv` are strong; if one does not follow from the existing results, the plan is
  amended (prove it at the protocol level, or the user's decision to drop it).
- **`matchIndex` vs `Progress.Match`**: they agree while no member is removed and re-added (the
  fourth gap of `notes/raft-trace-validation.md`); to check on paper for every place raft resets a
  progress (`becomeLeader`, `ResetState`).
- **The fork commit unpushed**: the branch cannot land until it is.

## Settled questions (the user's, 2026-11-08)

- The seed: arbitrary (`primitive.RandomUint64`); the step bound as the kv examples'.
- The TLC comparison (needs Java and the TLA+ tools) stays a local check (`TestAgainstTLC` skips
  without `TLA_TOOLS`), not in CI.

## The phases of this stage (`notes/spec-first-plan.md`)

- **Scope**: this plan (settled 2026-11-08).
- **Draft**: every statement written, proofs `sorry`, links generated, the glue proved: S1 (the Go
  the specs are of), S2 (the definitions they are written in), S3 (the hooks' and logger's specs,
  with the glue in raft's callers), and the statements of layers B, C and D (the simulation
  invariant and step lemma, `CheckTrace`'s spec, the harness's functions' and `Main`'s specs, the
  closed theorem). S4's paper sketch is part of Draft (it is what B's statements are written
  from).
- **Review**: fresh `spec-reviewer` rounds on the Draft (the specs, the invariant, the closed
  statement), until nothing first-tier is left; the questions batched to the user.
- **Test**: the specs against runs (the harness's traces, the hooks' events against the
  transcription's states).
- **Probe**: an easy proof (a hook) and a hard one (a step of the simulation: a received append).
- **Freeze**: the user's; the tag `trace-check-frozen`.
- **Prove**: S5, S6, S7 and the rest.

**Amendment A1 frozen (2026-11-10).** The coordinator tagged `trace-check-frozen-a1` at the merge of
`trace-check-a1` (the Draft with Q13's event premise, `MsgEvOf`'s `rejectHint`, the bootstrap
capability's configuration apart from raft's); reviews q13-r1..r4, a1-r1, a1-r2, the last two with
nothing first-tier. The Prove phase continues against it: next, `raft.Step`'s traced arms and the
capability forms of `appendEntry`/`becomeLeader` (the term log and the entry records), with the
owed items a1-r2 lists (a received message's numbers through a trace-gated conjunct of raft's
`isMessage`, the receipt bound, the bootstrap routing gates).

**Amendment A2 (2026-11-10, branch `trace-check-a2`; Q14 (a), Q15 (a), Q16 (b), pending the user's
veto).** (Q14) `PhaseStepR`, `FxPresR` and `trCap_fire_recv.statement` take the phantoms as a function
`ph` of the receiving server before the line (`P' ++ ph a`); checked first against `State.receive`: the
only replies raft does not send (pre-vote, check-quorum off) are the refusals of lower-term requests,
`phantomOf a m`. (Q15) `simFx` gains `MsgsShape` (every message in flight canonical in the fields its
line does not log), checked first to hold of every message the specification, raft (`msgAbs`), the
phantoms and the bootstrap can put in flight. (Q16) `simFx` gains `AppSlices` (a leader's in-flight
append requests of its term are slices of its log), checked by reading to be inductive with `CandS`:
requests come only from a leader's log, a leader's log only grows while it leads, and at `BecomeLeader`
a candidate has none of its term out. The laws and the gate re-proved, nothing else
frozen changed (`notes/decisions.md`, "Amendment A2 (Q14, Q15, Q16)"). Sufficiency
(`TracedRecvPhantom.lean`, `TracedRaftStepPaths.lean`): `fxPresR_staleReq` (a lower-term request's
receive line), `fxPres_heartbeat` and `fxPres_heartbeat_pin` (a heartbeat's send line, at the pinned
phases of `phaseStepB_heartbeat_pin`, `id ∈ C0` from `trCapB_pinMem`), `fxPres_app` (an `"app"` send
line with entries), proved. Left: `simFx` at the initial state (raft's bootstrap ghost, layer B's
allocation); the heartbeat gate's exact commit (slice 17); `AppSlices`' preservation lemmas for the
callers' lines (`Replicate`, `BecomeLeader`, step-downs, a follower's receives); an `"app"` counterpart
of `heartbeat_lead` for `fxPres_app`'s `hlead`; a `trFam`/`PinAt` pin-and-unpin pair for the path
proofs. Reviews `a2-r1.md` … `a2-r6.md`.

**Amendment A3 (2026-11-10, branch `trace-check-a3`; Q17 (a), then (d), pending the user's veto).**
First, (a) not made:
Checked first in the transcription, the clause `VoteRespUniq` of `simFx` is false in a reachable
state: a lower-term `MsgVote`, which raft ignores, gets the specification's phantom refusal at the
receiver's current term (Q14's `phantomOf`), so a voter's phantom refusal and its real grant to the
same candidate's term can be in flight together (a three-voter run, `notes/decisions.md`, "Amendment A3
(Q17)"). No fact of `simFx` repairs it: `simFx` reads only `σ`, where the phantom and a real refusal are
the same message, and a received refusal carries no raft fact, so a refusal's receive line cannot rule
out the grant still in flight, after which the grant's line diverges. Nothing changed in Lean; no review
round (no amended statement). Q17 re-opened with options (d) (relax `SimServerR`'s candidate tally,
recommended), (e) (`Fx` given the phantom lists) and (f) (rejected).
Then (d), taken by the coordinator: `SimServerR`'s candidate tally relaxed to `votesResponded` = raft's
voters and `TallyGranted` (raft's granting voters ⊆ `votesGranted` ⊆ `votesResponded`), nothing else
frozen changed. Checked first that nothing reads the equality: in the specification `votesGranted` gates
only `BecomeLeader` (fired by raft's line; `tallyGranted_quorum`), pre-vote's `Timeout` (off) and
`CandS`; no line's state check, invariant, layer C or acceptance file reads it. Re-proved: `sim_recordVote`
for any response, the campaign's empty tally (`tallyGranted_empty`, also in slice 19a's
`simServerR_becomeCandidate`). Sufficiency (`TracedRecvVoteResp.lean`): the receive line of a
candidate's `MsgVoteResp` of its term, granting or refusing, known voter or not, up to raft's state
after `recordVote` (`poll`'s three outcomes branch from there): `phaseStepR_voteRespCand`,
`fxPresR_voteRespCand`, `specInv_respCand`. Left: the bundle's `MsgVoteResp` path (the election
pending, won, lost); for the won branch, `tallyGranted_quorum`'s `hc` (every voter raft heard from is
configured: nothing in `SimServerR` or `msgAbs` gives it; from the message's origin, `isMessageC` or the
ghost state), which raft's `VoteWon` needs anyway (`TallyVotes` counts configured voters only).
Reviews `a3-r1.md`, `a3-r2.md` (no first-tier finding left).
