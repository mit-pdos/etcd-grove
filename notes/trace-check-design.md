# Trace-check: the design pass, from the closed theorem down to the proved pieces (2026-11-11, revision 3)

The user approved this pass (2026-11-11) under `notes/spec-first-plan.md`'s *Design before plumbing*:
before more threading, the whole chain is written as text, each statement with what it is proved
from and why that suffices, for review. Nothing here is threaded or proved. Every Lean
statement below is a text sketch, **not typechecked** (no Lean was run). Old → new is given wherever
a statement exists today. Revision 0: branch `trace-check-design`, from `trace-check` at `c2325abf53`.
Revision 1: branch `trace-check-design2`, from `trace-check` at `886be91e1b`, after the review round
`notes/trace-validation-reviews/design-r1.md` (first tier F1-F3, second tier S1-S12).
Revision 2: branch `trace-check-design3`, from `trace-check` at `2a0b56856b`, after the review round
`notes/trace-validation-reviews/design-r2.md` (first tier A1-A6, second tier B1-B7).
Revision 3: branch `trace-check-design4`, from `trace-check` at `344537cee1`, after the review round
`notes/trace-validation-reviews/design-r3.md` (first tier N1-N3, second tier S1-S8).
Probe A (2026-11-11): branch `trace-check-probeA`, from `trace-check` at `31058ad33c`: §8's Probe A as a
Lean proof (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/ProbeA.lean`); its
corrections, P1-P5, in the section below.

Reading order: §1 is the only part the user reviews (settled: Q32 and Q38 decided by the user). §2-§6
are the agent's (intermediate statements, recorded per "The gates, delegated"). §7 is the whole chain
as one table. §8 is the probe to run after review. §9 lists the links that are not argued, the order
of work that keeps every existing result proved, and the decisions.

Vocabulary used throughout: `TrNetTy t` (`MsgApp`, `MsgAppResp`, `MsgVote`, `MsgVoteResp`,
`MsgHeartbeat`, `MsgHeartbeatResp`), `AckTy` (`MsgStorageAppendResp`, `MsgStorageApplyResp`),
`recvTokOf` (`TracedRecvTok.lean`), `trTok` (today `TracedNodeApi.lean`; revision 1 moves it to
`InvNode.lean`, §3.1), the capability `trCapB` (`TracedCap.lean`), `rnTrace` (`InvRawnode.lean`).

---

## Probe A (2026-11-11): what the probe changed

§8's Probe A, run as a Lean proof (`tracecheck/ProbeA.lean`, built; no axiom, no `sorry`; the
statements not in Lean yet are hypotheses of its lemmas). Every post supplied the next pre but at the
points below; each is fixed in the text here (`notes/decisions.md`, "Probe A (harness glue)").

- **P1 (first tier: A6's `ConfChangeV2` arm does not compose).** `node.ApplyConfChange.spec` and
  `confPolicy_decide` need `Membership.applyChange (.v2 ConfChangeV2M.empty) m = some m'`;
  `committed_emptyV2_joint` gives only `m.isJoint`, and `Membership.applyChange` is sealed with laws of
  simple memberships only (`InvNode.lean:902-933`, "nothing is said of joint configurations"). **Fix:**
  a new raft API law, `Membership.applyChange_leaveJoint : m.Valid → m.isJoint → ∃ m',
  Membership.applyChange (.v2 ConfChangeV2M.empty) m = some m'` (raft-internal proof: `memApply`,
  `ccApplyM_leaveJoint` (`ConfchangeApiImpl.lean:109`), `leaveJointM`'s definedness at a valid joint
  state); `m.Valid` from `confAt_valid`. The probe takes it as the hypothesis `LeaveJoint`
  (`probeA_confV2`). §2.3, §7, §9 updated. It goes in step 1's landing (an API addition that re-opens
  nothing).
- **P2 (`readyGotT`'s claim is out of scope).** "`readyGotT` = `readyGot` ∗ `readyToksClaim n γ N ms`"
  leaves `ms` unbound: `readyGot` binds it inside its existentials. **Fix:** the claim is `readyGotT`'s
  last conjunct *inside* them, at `readyRest`'s `ms` (the list `rd.Messages'` points to), where today's
  `readyGotT` places the tokens (§3.1, §2.3). The probe's `readyGotC`; `probeA_readySplit` reads the one
  `ms` off it.
- **P3 (`tcOpsInv`'s parameter).** Revision 2's clause names `boot`: `tcOpsInv γ boot` (§2.2).
- **P4 (`tc_confShaped` is more than the arms need; a simplification).** Neither arm needs `ConfShaped`
  (`ccTransOk`) or the move of kvreconf's `confShaped_of_ops` to `ConfRule.lean`. The `ConfChangeV2` arm
  needs only `e.isEmptyV2` (`tcOps_emptyV2`, no position argument: a non-empty type-`2` entry would be a
  requested one, so in `boot`, of type `1`, or past it, of type `0`). The `ConfChange` arm needs only that
  the position is a bootstrap one (`tcOps_v1_boot`: `opsOf (boot ++ x) = boot ++ opsOf x`, so past
  `boot` the requested entries are a prefix of `ops.drop |boot|`), where `BootLogFacts` gives the voter's
  `AddNode` and `Membership.applyChange_addVoter` the step at the voters' simple membership. Both are
  harness-local, over raft's exported `opsOf`, `ownCommittedOps_lb_prefix` and `isCommittedLogLb_agree`.
  `tc_confShaped` and the move are struck (§2.2, §2.3, §7). Also: the client-visible filler is
  `LogEntry.isFiller` (`NodeApiVocab.lean:47`, type `0` only), not the protocol's `Filler`.
- **P5 (glue the design did not name).** `ClonePb`'s `eqv` carries only "no responses if the original
  had none". The original's empty responses come from `sentMsg_shape` (`SentMsgShape`'s last conjunct),
  and `stepIn_intro`'s `snapLocalMsg` from `snapLocalMsg_noDir` at `harness_alloc`'s
  `γ.snapLoc = fun _ => none` (§2.3's last row; `clone_st`, `probeA_cloneStep`).

**Held as written:** the allocation (`harness_alloc`, then `tcOpsInv`, `confPolicy_alloc`, `tcSnapsInv`;
`startTraceC_intro` into `StartNode.tracedSpec`'s precondition); the snapshot refutation; A5's instance
(`node.Advance.spec_of_traced` proved from `readyToksClaim_nil` and `node.Advance.tracedSpec`); *enter*'s
`readyMsgs` with `Advance`'s tokens into `send`'s per-message precondition at one `q.st`; `ClonePb` into
`stepIn_intro` with `trTok` and `node.Step.spec`; `trTok_type` through the clone's type; the thread
tokens (`netJoin.wp_Add`, `wp_fork_tok_self`, `netJoin.wp_Done`; `wp_fork_tok_body` for `app`); and
`startDone` ×3 into `runOver_intro`.

---

## Revision 3 (2026-11-11): what each finding of `design-r3.md` changed

All raft-internal; the direction of N1-N3 and of the second-tier fixes taken by the coordinator as the
review suggests, their form here by the agent. §1 is unchanged. Each claim below was re-checked against
the Lean the review cites (file and line given where it is used).

**First tier.**
- **N1 (clause 1(a) not re-established).** Taken: the flag is monotone in the bundle's end resource.
  `stepBundle_traced.statement`'s (and `.on`/`.onG`/`.onA`'s) `Gout` becomes
  `Gout s' := (∃ bt', ⌜bt = true → bt' = true⌝ ∗ trCapB … bt' …) ∗ ⌜OutTyStep s s'⌝`, in the same 27
  path files and 4 consumers as A2's `OutTyStep` (one more conjunct per close: a path that logs a line
  closes at `true`, one that logs nothing at `bt`). `stepClose_anyB` (`TracedRaftStep.lean:146`) takes
  the flag `bt` and gives the implication (trivially: it closes at `true`). `raft.Step.tracedTriple`'s
  post carries it. The tick specs' text does not change (`raft__tickElection`/`raft__tickHeartbeat`
  take the caller's `Gout` as a parameter, `Spec/…/raft__tickElection.lean:59`); `RawNode.Tick.traced`
  instantiates it with the monotone form, and their no-step branch (`R.G`) keeps the flag. Clause 1(a)'s
  maintenance restated (§3.2 item 1, §3.3, §3.7): a triple that steps keeps 1(a) because `delivered` is
  unchanged and, if it was non-empty, the pre's flag was `true`, so the post's is. Rejected: a
  persistent "booted" witness minted at the `Ready` line (new ghost state for one clause).
- **N2 (lemma (ii)'s source).** The review is right: the driver's `ca` is the last applied *conf*
  index, and `RawNode.Advance.spec`'s post bounds `ca` only from above. The source is `StepR.advance`'s
  `cidx := max r.cidx a` (`Protocol/StepR.lean:416`). **`RawNode.Advance.spec`'s post gains, as a
  separate pure conjunct, `rs.slent = none → rs.mode.isDyn = true → ca = max rs.capplied
  rs.delivered.length`** (no snapshot loan, dynamic mode). Proof (in `RawNode__Advance.lean`, at the
  `iapply HΦ $$ %s1.term %ca` site, :2026): `ownStepGhost_rinv` (:457) on the final ghost gives
  `RInv`'s `applied_cidx`, `uint.nat s1.logst.applied ≤ ca` (the ghost's `cidx` is `ca`,
  `rs.mode.toG ⟨ca, …⟩`); `s1.logst.applied = s.logst.applying = rs.delivered.length` (`Hge` and the
  loop's `applied ≤ applying`, `Hdlen`); with the existing `%Hca` (`rs.capplied ≤ ca ≤ max rs.capplied
  rs.delivered.length`) that is the equality. Its one caller pattern (`node__run.lean`'s `advancec`
  arm, through `runCfg_advance`) names one more conjunct. It is re-proved, not `sorry`ed, in step 2
  (§9), which re-opens `RawNode__Advance.lean` anyway for `raft.Step.spec`'s new `MsgTransferLeader`
  premise. Clause 1(e) is gated on `rs.mode.isDyn = true` (every node of the node API is dynamic:
  `StartNode.lean:319`, `HdynOk`). Lemma (ii)'s text (§3.4 item 3) and Probe B item 5 (§8) reworded:
  the source is the configuration index `RawNode.Advance` installs, not the driver's view.
- **N3 (the order of work).** `raft.Step.spec`'s `lt` premise moves to step 3, with clause 1(b) that
  supplies it, and is restricted (S3) to `m.Type' = MsgAppResp → s.gh.tr ≠ none → s.lt = W64 0`.
  **Found while checking the review's split:** keeping the rest of the physical half in step 2 does not
  build either. `sendTimeoutNow` is `r.send(…MsgTimeoutNow…)` (`raft.go:2058-2060`), so
  `raft.send.spec`'s strengthened premise needs `raft.sendTimeoutNow.spec`'s premise `s.gh.tr = none`,
  which `stepLeader` can discharge at its `MsgAppResp` call (`raft.go:1590`) only from `lt = 0`. So the
  **whole physical half lands in step 3** (§3.6, §9); nothing in step 2 reads it. Step 2 holds N1's
  flag implication and A2's `OutTyStep` (with the 27 path files), S2's `OutOk`, G3 (a), lemma (i),
  `TrNoSnap`'s form and N2's strengthened `RawNode.Advance.spec`. Step 3's re-open list gains
  `RawNode.Step.traced`
  (`TracedRawNode.lean:140`), `RawNode.Ready.traced` (`TracedRawNodeReady.lean:89`, which establishes
  1(a) as `acceptReady` does) and `RawNode.ReportUnreachable.traced` (`TracedRawNodeRep.lean:58`), and
  `raft.Step.traced` (`TracedRaftStepBundle.lean:612`) for the `lt` premise. Each landing's build is
  checked in §9 against what it changes.

**Second tier.**
- **S1 (A1's masks; `SndPending`).** `rtkN := nroot.@"raft_rtk"` (fixed, as `advN`, `tickN`,
  `budgetN` in `InvNodeChan.lean`: `isNodeChan γn id n` takes no `N`), its slots' `trTok` bodies over
  `γn.raft.reTrace` rather than a `Cluster`. `readyc` is a Perennial handshake (`inv nroot`): the key is
  allocated in a **`|={⊤}=>` prefix of `run`'s send AU**, a variant `handshake_send_au_fupd` of
  `handshake_send_au_upd` (`InvNodeChan.lean:1429`, which takes `|==>`) with `|={⊤}=>` in its place,
  sound since `sendAu` begins with `|={⊤,∅}=>`; the prefix runs only at the commit (a waiting sender's
  `sendAu` is run by the receiver's thread at the rendezvous), so a `select` firing another case
  allocates nothing. `advancec` (`inv advN`) opens `rtkInv` inside at `⊤ ∖ ↑advN` (`rtkN` is disjoint
  from `advN`). A1's sentence corrected: the driver's *offer* can be made while `pend = true`; its
  logical `SndPending` is entered by `run` at the rendezvous (which runs the driver's `sendAu` and its
  own `recvAu` in one step), where `pend = false` (§3.2 items 2-4).
- **S2 (L1 closed).** The carrier exists: the families' `⌜OutOk s o⌝` (`TracedPin.lean:40`),
  extended at each send by `outOk_snoc` (8 sites, listed in §3.6). `OutOk`'s right disjunct becomes
  `x.TrOk ∧ (TrScope s → TrOutMsg x)`; each `outOk_snoc` site proves `TrOutMsg` from the message type
  it already matches, and `lineF_untraced` (the read-index response, the one untraced send) proves the
  guarded conjunct by refuting `TrScope s` with the pending read it answers. `OutTyStep` at the close is
  the new `outTyStep_of_outOk` with `TrScope s'` from `StepEnd`. §3.6 names it; L1 is closed (§9).
  (The guard `TrScope s →` is this revision's form: the review's unguarded `TrOutMsg x` would leave
  `lineF_untraced` without a hypothesis to refute.)
- **S3.** The `lt` premise restricted to `MsgAppResp` (above): the tick specs and `MsgHup`/`MsgBeat`/
  `MsgProp`/`MsgUnreachable` callers are untouched by it.
- **S4 (G3 (a) by `ev2Rec`).** Taken. An empty `ConfChangeV2` past the bootstrap log is excluded by the
  per-entry record every non-boot entry already carries (`isEntryR`'s `ev2Rec`,
  `Protocol/Ghost.lean:1598`): the fold of the log before it is joint, while by induction on positions
  the conf entries before it are the bootstrap `AddNode`s, whose fold is simple. The term logs' gated
  clause is kept only for non-empty conf entries, which `appliedTo`'s automatic leave never mints, so
  (a) no longer needs (b) and the joint invariant becomes an order: (a), then (b) from it (§3.4 item 4).
- **S5.** 1(d) is `c.autoLeave = false` only; `c.outgoing = ∅` is `trCapB`'s
  (`TracedCap.lean:1085`).
- **S6.** §4's source of "no snapshot in a `Ready`" corrected: no `MsgSnap` is ever stepped at a
  traced node (`TrNetTy`, `netP`'s gate), not `TrNoSnap`.
- **S7.** `readyToksClaim`'s docstring also states its departure from "No disjunction of alternative
  specs" (§3.1). **S8.** §3.4 states the convention once (positions 0-based, indices 1-based); §2.3
  says "type 1 is never a filler" (`Filler`, `Ghost.lean:1177`).
- **§5.3** rewritten to A8 as frozen (tag `trace-check-frozen-a8`): A8.2's statements are the mono
  list's (`bootDone tn i := ∃ k, monoListIdxOwn tn.dn k i`, `simInv`'s `∃ Dn : List w64`,
  `monoListAuthOwn tn.dn 1 Dn` and `∀ i ∈ Dn, BootDone C L i`, `bootDn_snoc`), A8.1's the deletion of
  `bootInit`, A8.4's proof through `newTrace_simInit`.

**Re-checked.** §7's rows for N1-N3 and S1-S6; §8's Probe B items 3 and 5; §9's order, landing by
landing, for what each changes and what it must re-prove.

---

## Revision 2 (2026-11-11): what each finding of `design-r2.md` changed

The six first-tier items are raft-internal; their direction was decided by the coordinator (an
intermediate statement each), their form here by the agent. §1 is unchanged.

**First tier.**
- **A1 (the escrow, the driver sending first).** The review is right: in `SndPending` `run` holds no
  fragment of the driver's key, so it cannot give "key `j` deposited". Of the two fixes, **(b) a
  persistent allocation bound** is taken (simpler: every payload that crosses `advancec` stays
  persistent, and `run` never touches the driver's exclusive element or the tokens). `NodeNames` gains
  `al`; `rtkInv` gains `monoNatAuth γn.al a` (the keys allocated); the claim carries
  `monoNatLb γn.al (j + 1)`, minted with the key at the `readyc` commit; the driver's `SndPending`
  payload carries that lower bound; `run`, meeting it with `np` in hand, reads `j + 1 ≤ a` and answers
  `monoNatLb γn.dep (j + 1)`. Both hand-off orders are argued against `node.go`'s `run` (§3.2 item 4);
  the rendezvous is added to Probe B item 3 with the payload (§8). Rejected: (a), the element in the
  payload (an exclusive resource across the rendezvous, and `run` then hands out tokens).
- **A2 (L1, the outbox's types).** The derivation option is struck. The smallest addition is in
  **`stepBundle_traced.statement`'s post**, not in `stepClose`'s definition: the caller's end resource
  `Gout s'` (today `∃ bt', trCapB …`) gains `⌜OutTyStep s s'⌝`, a pure fact each path proves at its close
  from the messages it queued; `raft.Step`'s code proof is untouched (it returns `Gout s'` as it is),
  and `raft.Step.tracedTriple`'s post carries it to `rnTrace`. The path files re-opened are listed in
  §3.6 (the 30c assembly's paths: planned work). §3.6's exclusion of `MsgSnap` now cites `TrNoSnap` at
  `maybeSendAppend` and `raft.send`'s traced premise, not `ReplSends`. **Found while designing it:** the
  abstract outbox cannot see every handed-out message: a message whose type has no abstraction
  (`msgAbs … none`, dropped by `absList`) is invisible to any outbox conjunct, and `XfOk`'s
  `SentMsgShape` admits two such types raft queues, `MsgTimeoutNow` and a forwarded
  `MsgTransferLeader`. So `OutTyStep` has a physical half: `raft.send.spec`'s traced premise excludes
  untyped messages, `XfOk` records it of the queues, and `raft.Step.spec` gains the two traced premises
  its `sendTimeoutNow` and forwarding branches need (§3.6, "The physical half").
- **A3 (G3).** Restated as a joint invariant, with `appliedTo`'s automatic leave among the sources:
  (a) no entry past the bootstrap log is a configuration entry, cluster-wide, owned by the term logs'
  authority (where every entry of every log is minted), gated on the trace; (b) no node's configuration
  is joint, per node, a new clause 1(d) of `rnTrace`. (a) is kept because a traced leader mints only
  normal entries (`raft.Step.spec`'s existing traced premise on `MsgProp`, `becomeLeader`'s empty normal
  entry), the automatic leave being excluded by (b) through `raft.Step.spec`'s existing `autoLeave`
  premise; (b) is kept because the `confc` arm applies only a committed entry, a bootstrap `AddNode` by
  (a). The registry route is dropped (it cannot see an empty `ConfChangeV2`, a filler). §3.4 item 4.
  29n's leader line lemma stays the fallback.
- **A4 (L5, `TrNoSnap`).** Taken: **(a), the update form**,
  `TrNoSnap tr ls := □ (⌜tr ≠ none⌝ -∗ (⌜prev.index ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False)`.
  Its two uses (`raft__maybeSendAppend.lean`'s snapshot fallbacks) are WP steps of a plain triple at
  `⊤`, so `iapply` becomes `imod`; the other mentions pass `TrNoSnap` through by name. `setupNode` builds
  it from the client's `isStorage γ K st` (its `Hbound` at the gated `storBnd`), before the conversion to
  raft's `raftBnd`, which therefore needs no gate. Rejected: (b), a pure "never compacted" fact in the
  storage key's names (a change to MemoryStorage's ghost state for one premise). L5 is closed (§5.2).
- **A5 (one proved triple for `node.Advance`).** `node.Advance.tracedSpec` is the one proof;
  `node.Advance.spec` (text unchanged) is its instance at `ms = []`, by the law
  `readyToksClaim_nil : ⊢ readyToksClaim n γ N []`, the claim being `⌜ms = []⌝ ∨ (the escrow element)`
  at a traced cluster and `True` at another. The left disjunct is the claim-less driver of F3: its
  request records `none`. No client changes (§3.1).
- **A6 (`handleReady`'s `ConfChangeV2` arm).** Handled as kvreconf's `Replica__applyEntry`, from facts the
  client sees: the committed entry decodes (`tc_confShaped`, from a new pure clause of `tcOpsInv` and
  kvreconf's `confShaped_of_ops` argument: past the bootstrap log the harness's committed requested
  entries are normal, and an empty `ConfChangeV2` decodes by the existing `ccDecodeV2_nil`), so
  `proto.Unmarshal` returns no error and the `panic` is not reached; `confPolicy_decide` then
  `node.ApplyConfChange.spec`, the membership step given by raft's exported `committed_emptyV2_joint`
  (an empty `ConfChangeV2` is committed only where the configuration in force is joint). Not dead in the
  proof, though it is in every run (G3).

**Second tier.**
- **B1 (the order of work).** Steps 1 and 2 are **one landing** (the gates with their client-side
  premises and every call site). `rnTrace`'s new clauses stay off proved theorems until their facts are
  proved: a landing of their facts first (L1's per-path `OutTyStep` and its physical half, lemmas (i),
  (ii), G3 (a), `TrNoSnap`'s form), then a landing adding the clauses with every re-opened triple
  re-proved in it. A8.1's `simInit` readers are re-proved in A8's own landing (done on branch
  `trace-check-a8`: every reader re-proved, no `sorry`; §5.3). `node.run.gated_of`'s hypotheses are
  then only `hAdv` and `hCC`, every other link being a theorem before it is stated (§9).
- **B2 (L3 and `storBnd`'s clients).** Three client lemmas unfold `storBnd` (`kvJ_bnd`, `kvrJ_bnd`,
  `kdJ_bnd`) and the server reaches it through raft's `memStorage_isStorage` (`NodeStart.lean:322`).
  Raft exports `storBnd_intro_untraced` and `storBnd_zero`; the three lemmas are re-proved through them
  (no unfold, as PRINCIPLES asks), `memStorage_isStorage` gains the untraced premise (Q6 item 8). L3
  gains 4 call sites in 4 files (§9).
- **B3 (lemma (ii)).** Written in the short form: `uint.nat s.logst.applied ≤ rs.capplied`, a new
  clause 1(e) of `rnTrace` (traced only), established at `RawNode.Advance` (`advRS` sets `capplied := ca`); at the `confc` arm
  `DynCCPre` gives `rs.capplied ≤ k` (§3.4 item 3).
- **B4 (`pbMessage`'s import).** `PbMessage.lean` moves from rafthttp's proof tree to raft's, beside
  `InvPbMsg` (its body uses only `InvProto` and `InvPbMsg`; the `Net` import goes), listed in
  `etc/api/raft.txt`; rafthttp's importers import the new module. The harness then depends on raft and
  protobuf only (§2.3).
- **B5 (`app`'s thread token).** `RunConcurrent` forks each `app` with `wp_fork_tok_body`
  (`Lifting.lean`), handing it the fresh token; `app` keeps one token in its loop invariant, deposits it
  at each `c.net.Add(1)` and gets a fresh one at each `go` (`wp_fork_tok_self`), and returns it at exit
  (§2.2, §6; checked in Probe A).
- **B6 (masks; the escrow's namespaces).** `rtkN := N.@"rtk"`, a sibling of the `readyc` and
  `advancec` channels' namespaces; `rtkInv` is opened inside a channel AU at `⊤ ∖ ↑(that channel's
  namespace)`, by whichever thread executes the commit (§3.2 item 2).
- **B7 (`acceptReady`).** `acceptReady` frames 1(c) and 1(d) (it moves `applying`, not `applied`, and
  keeps the role and the configuration), establishes 1(a) by the `Ready` line, and empties the outbox
  (1(b) trivially); its re-opening is for `readyTok`'s body and those (§3.3).
- `ThreadBoundLe.weaken`'s instance argument is instance-implicit: §2.1 now writes
  `haveI := ThreadBoundLe.of_eq HT; ThreadBoundLe.weaken (n + 2) Hn`.

**Re-checked.** §7's provenance column, row by row against the changes above; §8's probes (Probe B
item 3 with the allocation bound; Probe A with `app`'s token, the `ConfChangeV2` arm, the moved
`pbMessage`). Aligned with amendment A8 as implemented (branch `trace-check-a8`, §5.3): a mono list
for the witnesses, not a ghost map; `bootInit` deleted, `newTrace_simInit`; `HarnessEnd`'s `bootEnd`
a theorem.

---

## Revision 1 (2026-11-11): what each finding of `design-r1.md` changed

**First tier.**
- **F1 (the step bound; the thread bound).** Taken: Q38 (a), **decided by the user (Q38,
  2026-11-11)**. §1.2's `Hn` is `n + 2 ≤ 2 ^ 31` (was `n + 4 ≤ 2 ^ 61`); §1.3 gains
  `[ThreadBoundLe GF (2 ^ 31)]`; `RunConcurrent.spec`, `Main.spec` and `tcMainSpec` take the instance
  (§2.1); `tracecheck_adequate_of` derives it (`ThreadBoundLe.of_eq HT`, weakened by `Hn`) and the old
  `receiptBound GF + 3 ≤ 2^61` from `HN` (§2.1). `isNetJoin` no longer carries a pure bound: `netJoin.wp_Add`
  reads the instance (§6). The chain is checked end to end in §6 ("The thread bound, end to end"). L4
  (revision 0's) is closed.
- **F2 (`node.Step`).** Taken: the review's fix. One proved spec, `node.Step.spec`, text unchanged. The
  gate moves into `stepIn`'s sealed body (`stepP`'s traced `netP`/`fwdP` need the token and the type);
  `stepIn_intro` gains the premise `trTok γ st`, which untraced clients discharge with
  `trTok_untraced γ st h`. `node.Step.tracedSpec` becomes a corollary (`stepIn_intro` + `node.Step.spec`).
  The four call sites of `stepIn_intro` each hold `h` already, but kv's (one new conjunct in kv's own
  `kvPeerOk`) (§3.1, "F2's call sites"). Found while checking: `node.ProposeConfChange` builds `stepIn`
  internally (not through `stepIn_intro`) for a conf-change `MsgProp`, so under the gated `stepIn` its
  refusal premise is **needed**, not redundant (S10's second point does not hold).
- **F3 (`node.Advance`).** Choice: **a fresh claim per `Ready`, `run` needing nothing back**, which
  changes no client; `node.Advance.spec` keeps its text and is proved for every `γ`. The review's
  sketch of it was not sound as written: a claim named by a fresh ghost name agrees with nothing the
  deposit names, and a driver can keep a stale claim (from a `Ready` it advanced with
  `node.Advance.spec`). Revision 1 makes it exact with a per-node escrow (`rtkInv`) at fixed names and an
  exclusive "no deposit pending" token that `run` lends at the rendezvous (§3.2 items 2-4), and argues it
  against `node.go`'s `run` (`advancec` is armed only in the `readyc` arm after `acceptReady`). The
  alternative (`Cluster.trace γ = none →` on `node.Advance.spec`, "both halves back") is the fallback,
  costed in L3.

**Second tier.**
- **S1.** §2.2's conf-change proposer row corrected: `time.Now()` (`concurrent.go:206`) and
  `time.Time.Add` are called once, before the loop; only the loop's `time.Now().Before` and `Status`
  are short-circuited. §6 ("What the closed theorem rests on") lists every existing axiom the closed
  theorem rests on once `RunConcurrent` is proved: raft's node-API path's fifteen (`etc/tcb-collections/raft.txt`'s
  baseline, `strconv.Itoa` among them), the harness's own `proto.ClonePb.wp_proof` (revision 0 wrongly said
  "`proto.Clone` as kvreconf": kvreconf copies messages by hand), and Perennial's trusted `time.Now`. None
  is new.
- **S2.** A8.2 uses the existing `bootEvAt_unique` (`TraceSimBootSeg.lean:218`); no copy.
- **S3.** `startDone γ i` stays sealed; the end law `Cluster.traceSim_bootEnd` and `HarnessEnd`'s
  `runOver_intro` take `□ [∗list] i ∈ vs, startDone γ i` with `traceDir γd tn` and
  `Cluster.trace γ = some γd`, and do the `traceDir` agreement inside (A8.4).
- **S4.** §5.2's statements written at the voters' configuration `cC` (not raft's `c`, empty at
  positions 0-2), with the phase `Φvs C _ _ := C = vs`, so that `Λ2`/`Λend` written at the caller's `vs`
  discharge `trCapB_bootDone`'s `hΛ`.
- **S5/S9.** §3.3 lists every proved triple a new `rnTrace` clause re-opens; §9 "Order of work" puts
  every gate in with its `none` arm equal to today's body, so the untraced proofs (all of today's
  results) are re-proved by rewriting the gate and no `sorry` goes under an existing result; the traced
  `node.run` is a separate theorem with the ★ arms as hypotheses until they are proved; `node.run.spec`'s
  premise is dropped only then (its untraced statement kept as an instance).
- **S6.** §3.4 restates the leader obstacle: `AccIdle` says nothing of the role; at a leader
  `switchToConfig` also logs `Commit` (`maybeCommit`) and sends (`bcastAppend`), which
  `trCapB_hookGate_applyCC` (phase `SimIdle`) covers neither.
- **S7.** §3.4 states the exclusion's lemmas: the bootstrap log prefix, the `confc`-arm lemma, and a
  third found here (no conf entry past the bootstrap log at a traced cluster, G3). L2 updated.
- **S8.** `tracecheck.BootFacts` renamed `tracecheck.BootLogFacts`.
- **S10.** L3 counted (§9): the refused calls, `Step` (through `stepIn_intro`) and, in the fallback only,
  `Advance`. `ReportSnapshot` keeps its refusal premise (other clients at a traced cluster could call it;
  the harness's call is dead by `trTok_type`); `ProposeConfChange` keeps its premise (F2 above).
- **S11.** A8.2's list of `simInv` re-establishers gains `trCapB_perm` (`TracedFamilies.lean`, `L`
  unchanged, the clause carries trivially) and `Cluster.traceSimInv_alloc` (the empty `Dn`); the
  readers (`TraceSimEnd`'s `simInv_end`, `simInv_end_boot`) only drop the conjunct.
- **S12.** §2.2 names the harness's invariants: `tcOpsInv` (`ownCommittedOps`, outside `N`, building
  `Propose`'s AU per call) and the shared decision authority as raft's own client library
  `confPolicy` (`ConfPolicy.lean`, `confPolicy_alloc`/`confPolicy_decide`, as kv's `kvRule`), and
  `tcSnapsInv` (`ownSnapsMade γ []`). `handleReady`'s snapshot branch is refuted from client-visible facts
  (`readySnap`'s `snapshotCert`, `snapshotCert_made`, `snapMade_elem` against `ownSnapsMade γ []`), not
  `TrNoSnap`. `γ.rtk` is per node (`NodeNames` fields, §3.2). `readyToksClaim`'s docstring states the
  departure from "no identification handles" with the alternative. A8.1 keeps `bootInit_eq` as a lemma
  (propositional, not definitional).

**Re-checked.** L1 (the outbox's types, against `rawnode.go`'s `readyWithoutAccept`/`acceptReady`: the
handed-out messages are `r.msgs` and the non-self `msgsAfterAppend`), L2 (three lemmas now), L3
(counted), §7's provenance column, §8's probe (to the revised chain). New in this revision: **L5**, the
source of `rnTrace`'s `TrNoSnap` at `setupNode` (Q6 item 8's gated `storBnd`, not in revision 0).

---

## 1. The closed statements (THE USER REVIEWS ONLY THIS SECTION; settled)

Both go in `Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Results.lean`. They replace
`raft_tracecheck_safe_of` (which takes `TcOpen`) once `RunConcurrent.spec` is proved.

### 1.1 The premise bundle (Q32, the user's decision, 2026-11-11)

Modelled on `etcd_putget.BootFacts` and `etcd_putget.premises` (`examples/etcd/putget/Defs.lean`).
New file `Proof/.../tracecheck/Defs.lean`:

```lean
/-- The bootstrap log `StartNode` builds for the peers `1, 2, 3` (each `Peer{ID: i}`, `Context`
nil), as Go computes it: three conf-change entries of term 1 whose data is the marshalled
`ConfChange{Type: AddNode, NodeID: i}` (the node API's `BootLog`). Named apart from layer B's
`TraceCheck.BootFacts C L` (`MainSim.lean`, over `newTrace`). -/
abbrev tracecheck.BootLogFacts (boot : List LogEntry) : Prop :=
  BootLog [W64 1, W64 2, W64 3] [[], [], []] boot

/-- **`Main`'s named premise** (Q32): `proto.Marshal`'s contract at the bootstrap log's conf
changes. Each of the three `StartNode`s marshals `AddNode i`, and the call returns the bytes of
`boot`'s `i`-th entry (`bootMarshal`, persistent). Raft's proof needs the three voters' logs to be one
committed log. `proto.MarshalConfChange.spec` gives only bytes that decode to the change. -/
abbrev tracecheck.premises (boot : List LogEntry) : IProp GF :=
  bootMarshal [W64 1, W64 2, W64 3] [[], [], []] (LogEntry.toEntries boot 0)
```

No axiom changes (Q32: "follow the etcd examples"). The bundle holds `bootMarshal` only.

### 1.2 `raft_tracecheck_safe` (the closed theorem)

```lean
theorem raft_tracecheck_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel]
    (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot)
    (Hprem : ∀ hG : HeapGS .hasLC tcGF,
      ⊢ tracecheck.premises (GF := tcGF) (hG := heapWith hG lctx) boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n + 2 ≤ 2 ^ 31) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([tracecheckProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

**What changes from `raft_tracecheck_safe_of`'s statement:** `hopen : TcOpen` is gone. Three
binders are added: `boot`, `Hbf` and `Hprem` (Q32). The step bound is `n + 2 ≤ 2^31` (**decided by
the user (Q38, 2026-11-11)**; was `n + 4 ≤ 2^61`). In plain terms: the harness starts one goroutine per
message and counts them in a `sync.WaitGroup`, which panics past `2^31`; the proof bounds the
goroutines by the run's length, so the theorem covers runs of fewer than about `2^31` steps (it
implies the old `n + 4 ≤ 2^61`; `etcd_putget_safe` has `n + 2 ≤ 2^28`). Everything else is word for
word: the program, the three conclusions and the instance context. `tracecheckProgram` is the
package's initialization, then `Main()`; `Main` runs `RunConcurrent(DefaultCConfig())`,
`ConvertEvents`, `NewTrace`, and `CheckTrace(tr, true)`, and panics unless `TLCOK`.

### 1.3 `raft_tracecheck_accepts` (the corollary: every run's trace satisfies `TraceAccepts`)

`TraceAccepts` is unchanged (`etcdraft/Tla/Check.lean`):
`TraceAccepts events pv cq := ∃ t, newTraceWith events pv cq = .ok t ∧ ∃ res, CheckTraceRel t true res ∧ res.tlcOK = true`.

```lean
theorem raft_tracecheck_accepts [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [ThreadBoundLe GF (2 ^ 31)]
    (Hrb : receiptBound GF + 3 ≤ 2 ^ 61) (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
        context.isClosedchanInit ∗ tracecheck.premises boot }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent))
        (Val #defaultCConfig))
    {{ (c : Loc), RET (PairV #c #interface.nil);
        WP (App (Val (c @!! go.GoType.PointerType Cluster.ty @!! go!"Events")) (Val #()))
          {{ v, ∃ (sl : GoSlice) (L : List TraceEv), ⌜v = #sl⌝ ∗ traceEventsRep sl L ∗
                ⌜Etcdraft.TraceAccepts (L.map TraceSim.evConv) false false⌝ }} }}
```

The composition of `RunConcurrent.spec` (§2.1) with the proved `tracecheck_Events_traceAccepts`, at
`defaultCConfig` (so the closed statement does not expose `Workload`). The form is **approved by the
user (Q38, 2026-11-11)**; the instance `[ThreadBoundLe GF (2 ^ 31)]` is Q38 (a).

**Nothing else in the chain below is the user's.** The trust base is unchanged: no axiom is added.
§6 lists the existing axioms the closed theorem will rest on.

---

## 2. `RunConcurrent` and the harness: what each piece uses from the node API

### 2.1 The harness's own statements (layer D, the agent's)

- **`Workload`** (`Spec/.../tracecheck/RunConcurrent.lean`). Old: three voters, no extra node, no
  configuration change, no snapshot, `0 ≤ MaxDelay < 2^62`. **New** (Q35 (a)): add
  `0 < sint.Z cfg.Tick'`. `time.NewTicker` panics otherwise. `DefaultCConfig`'s 10ms meets it.
- **`RunConcurrent.spec`**. Old:
  `receiptBound GF + 3 ≤ 2^61 → ∀ cfg, Workload cfg → {{ isPkgInit ∗ context.isClosedchanInit }} RunConcurrent #cfg {{ c, RET (c, nil); runOver c }}`.
  **New**: `∀ [ThreadBoundLe GF (2 ^ 31)], receiptBound GF + 3 ≤ 2^61 → ∀ boot, tracecheck.BootLogFacts boot → ∀ cfg, Workload cfg →`
  with `tracecheck.premises boot` added to the precondition. `runOver c` is unchanged.
- **`Main.spec`**. **New**: `∀ [ThreadBoundLe GF (2 ^ 31)], receiptBound GF + 3 ≤ 2^61 → ∀ boot,
  tracecheck.BootLogFacts boot → {{ isPkgInit ∗ context.isClosedchanInit ∗ tracecheck.premises boot }} Main #() {{ RET #(); True }}`.
  `Main.wp_proof` passes the three through to `RunConcurrent`.
- **`tcMainSpec`** (`Adequacy.lean`): `∀ [hG] [go.Semantics] [Assumptions], TraceCheck.Main.spec`
  at `tcGF` (the new binders inside `Main.spec`).
- **`tracecheck_adequate_of`** gains `boot`, `Hbf`, `Hprem` and `Hn : n + 2 ≤ 2^31` (was `n + 4 ≤ 2^61`).
  Its proof takes `HT : threadBound GF = n + 2` from `init_adequate` (ignored today, `fun hG HN _`),
  makes `haveI := ThreadBoundLe.of_eq HT; haveI : ThreadBoundLe tcGF (2 ^ 31) :=
  ThreadBoundLe.weaken (n + 2) Hn` (`weaken`'s instance argument is instance-implicit, so it is not
  passed positionally; revision 2), or `⟨by rw [HT]; omega⟩`, as `cache/Results.lean`, `Hbound : receiptBound tcGF + 3 ≤ 2^61` by
  `rw [HN]; omega` from `n + 4 ≤ 2^31 + 2 ≤ 2^61`, and `ihave #Hprem' := Hprem hG` as
  `etcd_putget_adequate` does.
- **`TcOpen`** is deleted once `RunConcurrent.wp_proof` exists. `Results.lean` then states §1.

### 2.2 `RunConcurrent`'s body (`concurrent.go`), call by call

The harness's own invariants (named here, S12), allocated after `harness_alloc`, all outside `N`
(raft's namespace):
- **`tcOpsInv γ boot := inv tcOpsN (∃ ops, ownCommittedOps γ ops ∗ ⌜boot <+: ops ∧ ∀ op ∈ ops.drop boot.length, op.type = W32 0⌝)`**
  (Probe A, P3: the clause names `boot`), from `harness_alloc`'s
  `ownCommittedOps γ boot`. `γ.dup = false`, so `node.Propose.spec` takes one non-persistent AU per
  call, `AU <{ ∃∃ ops, ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅ <{ ∀∀ t, ownCommittedOps γ (ops ++ [⟨t, 0, data⟩]), COMM True }>`;
  the proposer builds it from `tcOpsInv` (open, take, close with the appended list). **Revision 2
  (A6):** the invariant also holds the pure clause `boot <+: ops ∧ ∀ op ∈ ops.drop boot.length,
  op.type = W32 0` (the requested entries past the bootstrap log are the proposer's normal ones); kept by
  each proposal (type `0`). `handleReady` reads it through two harness-local laws, each opening
  `tcOpsInv` and using `ownCommittedOps_lb_prefix` (Probe A, P4: in place of revision 2's
  `tc_confShaped` and the move of kvreconf's `confShaped_of_ops`, which the arms do not need):
  `tcOps_emptyV2 : tcOpsInv γ boot -∗ isCommittedLogLb γ l ={E}=∗ ⌜∀ e ∈ l, e.type = W32 2 → e.isEmptyV2⌝`
  (a non-empty type-`2` entry is no filler, so a requested entry, so in `boot`, type `1`, or past it,
  type `0`) and `tcOps_v1_boot : tcOpsInv γ boot -∗ isCommittedLogLb γ boot -∗ isCommittedLogLb γ l ={E}=∗
  ⌜∀ k e, l[k]? = some e → e.type = W32 1 → k < |boot|⌝` (`boot` has no filler and no empty
  `ConfChangeV2`, so `opsOf (boot ++ x) = boot ++ opsOf x`, and past `boot` the requested entries are a
  prefix of `ops.drop |boot|`; with `isCommittedLogLb_agree`). Nothing else of the run reads the
  committed operations.
- **`confPolicy γ tcConfN tcRule`**, from `harness_alloc`'s `ownConfDecisions γ ∅` by `confPolicy_alloc`
  (`ConfPolicy.lean`, raft's client library, the one kv uses), with `tcRule := fun _ _ e => ccDecode e`
  (kv's `kvRule`). Persistent, so the three `app`s share it: each `handleReady` obtains
  `confDecided γ k (.apply o')` for a committed conf entry by `confPolicy_decide` (the recorded decision
  if another `app` decided position `k` first, the same at every caller), with `confAt γ k m` from
  `harness_alloc`'s `confAt γ 0 …` and each `ApplyConfChange`'s post, as kv's `applyConf`.
- **`tcSnapsInv γ := inv tcSnapsN (ownSnapsMade γ [])`**, from `harness_alloc`'s `ownSnapsMade γ []`.
  The harness never makes a snapshot (`SnapshotEvery = 0`); `handleReady` opens it to refute a
  snapshot `Ready` (§2.3).

| Go | Statement used | Old → new | What the proof needs from it |
|---|---|---|---|
| `&Cluster{…}`, `&SyncRecorder{}`, `make(chan struct{})` | Goose allocation; the recorder's lock (`isSyncRecorder`, S7 part 1) | unchanged | the trace's two halves: `traceFrag γt []` to the names, `traceAuth` under the lock |
| (ghost) | `harness_alloc` (`HarnessAlloc.lean`): `traceNames_alloc`, `cluster_alloc_traced`, `Cluster.traceSim_alloc`; then `tcOpsInv`, `confPolicy_alloc`, `tcSnapsInv` | `traceNames_alloc` also allocates `monoListAuthOwn tn.dn 1 []` (A8.2, as implemented: §5.3) | the traced cluster `γ`, `traceDir γd tn`, `Cluster.traceSim γ vs tn`, each voter's `voterStart` |
| `raft.NewMemoryStorage()`, `&raft.Config{…}` | the storage contract (`restartStorage`, as kvreconf), its justification `J` never compacting (`J.B k := ⌜k = 0⌝`), its bound by the new law `storBnd_zero` | the storage bound `storBnd` gated (Q6 item 8): no compaction right at a traced cluster; `storBnd_zero`, `storBnd_intro_untraced` exported (B2) | `ConfigValid`, `TraceLogger ≠ nil` (`c.rec`), `MaxSizePerMsg = ^0`, `AsyncStorageWrites = false` |
| `raft.StartNode(rc, peers)` ×3 | `StartNode.tracedSpec` (`TracedNodeApi.lean`) | **`D` fixed** (A8.3): the post's `startDone γ D cv.ID'` becomes the sealed `startDone γ cv.ID'` | `isNode`, `nodeDriver … init`, `nodeConfig`, `nodeRunning 1`, the persistent `startDone` |
| `c.apps.Add(1); go c.app(r)` ×3 | `sync.join` (`WaitGroupJoin`: three `Add(1)`s, `num_added ≤ 3`); the `go` by `wp_fork_tok_body` (`Lifting.lean`) | the thread token named (B5) | each `app` gets `nodeRunning 1`, `isNode`, the driver state, a third of the network's adder right (§6, Q34), `ownDone apps P'` with `P' := nodeRunning 1 ∗ njAdder ⅓`, and **the fork's fresh `threadTok`**, which its body must return (it ends holding one: §2.4, §6). The other goroutines (drivers, proposer, isolation) take none: `wp_fork` |
| `drivers.Add(3)` | a local `join3` lemma over the raw `WaitGroup.Add` spec (three `ownDone`s from one `Add(3)`; `join` has `Add(1)` only) | new (harness-local, glue) | three driver goroutines |
| isolation driver | `time.Sleep`, `atomic.Uint64.Store`, `below` (proved) | unchanged | nothing of raft |
| proposer | `below`, `context.WithTimeout`, **`strconv.Itoa`** (existing axiom, §6 Q33), `node.Propose.spec` (unchanged) with the AU from `tcOpsInv`, `cancel`, `atomic.Int64.Add`, `time.Sleep` | unchanged | `Propose` puts one **normal** entry on `propc` (`propP`'s first disjunct), which the traced `propc` arm needs (`PropAny`) |
| conf-change proposer | `time.Now` (Perennial's trusted spec) and `time.Time.Add` (proved), once before the loop (`concurrent.go:206`); then `atomic.Int64.Load` of `ConfChanges` at a persistent `0` (`Workload`'s `ConfChanges' = 0`: the loop's `&&` short-circuits, so the loop's `time.Now().Before`, `Status` and `ProposeConfChange` are never called) | **corrected** (S1: revision 0 said `time.Now` is never called) | the counter is never written; its points-to is made persistent at allocation |
| `drivers.Wait`, `time.Sleep`, `close(c.stop)` | `join3`, `time.Sleep`, the channel close | unchanged | — |
| `c.apps.Wait()` | `sync.join.WaitGroup.wp_Wait` | unchanged | the three `nodeRunning 1` and the three `njAdder ⅓` back |
| `r.node.Stop()` ×3 | `node.Stop.spec` | unchanged | `nodeRunning 1` in |
| `c.net.Wait()` | `netJoin` (§6, Q34): `njClose` (`njAdder 1` → the wait token), then the raw `Wait` | new (harness-local) | the counter reaches 0 (every network goroutine `Done`) |
| `return c, nil` | `runOver_intro` (`HarnessEnd.lean`) over `startDone`, with the API law `Cluster.traceSim_bootEnd` (A8.4) | the hypothesis `BootEnd D` becomes the theorem `bootEnd` (done on `trace-check-a8`); `runOver_intro` takes `□ [∗list] i ∈ vs, startDone γ i`, `traceDir γd tn`, `Cluster.trace γ = some γd` (S3) | the three `startDone`s, `nodeBoot`, `Cluster.traceSim` |

### 2.3 `app` (one per replica)

| Go | Statement used | Old → new |
|---|---|---|
| `time.NewTicker(c.cfg.Tick)`, `defer ticker.Stop()` | Perennial's `time.NewTicker.spec` (proved; needs `0 < Tick`: Q35) | unchanged |
| `case <-c.stop: return` | the closed-channel receive; `apps.Done` with `nodeRunning 1 ∗ njAdder ⅓` | unchanged |
| `case <-ticker.C: r.node.Tick()` | `node.Tick.spec` (`isNode` only) | unchanged: its traced content is `run`'s `tickc` arm |
| `case rd := <-r.node.Ready()` | `isReadyChan_recvAu.tracedSpec` | **changed** (29n finding 4): `readyGotT`'s last conjunct is the claim `readyToksClaim n γ N ms`, no longer the tokens (§3.1), inside `readyGot`'s existentials at `readyRest`'s `ms` (Probe A, P2); revision 2: the claim also carries the key's allocation bound (A1) |
| `c.handleReady(r, rd)` | `raft.IsEmptySnap`, `MemoryStorage.Append`/`SetHardState` (storage contract), `proto.Unmarshal` into a `*ConfChange` (`proto.UnmarshalConfChange.spec`, existing axiom), **`node.ApplyConfChange.spec`** with `confDecided` from `confPolicy_decide` (§2.2), `atomic.Int64.Add` | the snapshot branch refuted from client-visible facts (S12): `readyGot`'s `readyRest` holds `readySnap … L`; at `L = some l` it holds `snapshotCert γ N …`, whence `snapshotCert_made` gives `snapMade γ s` and `snapMade_elem` against `tcSnapsInv`'s `ownSnapsMade γ []` gives `s ∈ []`; at `L = none`, `rd.Snapshot' = null`, so `IsEmptySnap` is true. **Both conf arms** (revision 2, A6: as kvreconf's `Replica__applyEntry`): the entry `e` at position `k` is committed (`readyGot`'s `committedEntriesAt` with `isCommittedLogLb`). For a `ConfChange`, `tcOps_v1_boot` (§2.2) puts `k` in the bootstrap log (type `1` is never a filler: the client-visible `LogEntry.isFiller` is type `0` only, `NodeApiVocab.lean:47`; so past `boot` it would be among the requested entries, which are normal there; Probe A, P4), where `BootLogFacts` gives the voter's `AddNode`, whose bytes decode (`MarshalsConfChange`), and `Membership.applyChange_addVoter` the step at the voters' simple membership `m ∋` it. For a `ConfChangeV2`, `tcOps_emptyV2` gives `e.isEmptyV2`: its empty bytes decode (`ccDecodeV2_nil`), raft's exported **`committed_emptyV2_joint`** (`InvNodeRule.lean:365`) gives `m.isJoint`, `confAt_valid` gives `m.Valid`, and the **new raft API law `Membership.applyChange_leaveJoint`** (`m.Valid → m.isJoint → ∃ m', Membership.applyChange (.v2 ConfChangeV2M.empty) m = some m'`; Probe A, P1: raft exports no law of joint memberships, so without it the step premise is unprovable) gives the step. Either way `proto.Unmarshal` returns no error (`proto.UnmarshalConfChange.spec` / **`proto.UnmarshalConfChangeV2.spec`**, existing axioms), the `panic` (`concurrent.go:315-317`, `:322-324`) is not reached, and `confPolicy_decide` (rule `ccDecode`, decision `.apply o`) then `node.ApplyConfChange.spec` at `confAt γ k m` (the driver's view) take the step as their premise `Membership.applyChange o m = some m'`. The arm is reached in no run (G3), but its proof needs no raft-internal fact. The `CreateSnapshot`/`Compact` branch: `SnapshotEvery = 0` |
| `r.node.Advance()` | **`node.Advance.tracedSpec`** (new, §3.1; the one proof, `node.Advance.spec` its instance, A5) | the claim in, `[∗list] q ∈ ms, trTok γ q.st` out. The stopped disjunct is refuted by `nodeRunning_stopped`: the `app` holds `nodeRunning 1` |
| `for _, m := range rd.Messages { c.send(r, proto.Clone(m).(*pb.Message), …) }` | **`proto.ClonePb.spec`** (existing axiom) at `pbMessage` (the `PbType` of a `*raftpb.Message`; revision 2, B4: `PbMessage.lean` moves from `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/` to `Proof/go_etcd_io/raft/v3/`, beside `InvPbMsg`, dropping its import of rafthttp's `Net`, which its body does not use, and is listed in `etc/api/raft.txt`; rafthttp's importers import the new path; the harness then imports no server module), `below`, `send` (below) | **corrected** (S1): revision 0 said "`proto.Clone` as kvreconf"; kvreconf copies messages by hand (`copyMsg`), and the generic `proto.Clone.spec` has no `Message` case. Checked in Probe A (`probeA_cloneStep`): `ClonePb`'s `T.ro l m` from the `Ready`'s `msgOwn q.loc (readyDq q.st) q.st` by `msgOwn_persist`, and the clone's `T.dec l' m'` with `eqv` into `node.Step`'s `msgPtsC … ⟨st.msg, st.ents, st.snap, st.ctx, []⟩` (the etcd server's `netRecv` does the same from a decoded copy), the original's empty responses from `sentMsg_shape` (`eqv` only carries their emptiness), and `stepIn_intro`'s `snapLocalMsg` from `snapLocalMsg_noDir` at the harness's `γ.snapLoc = fun _ => none` (P5) |

**When the harness sends, checked against the Go.** `app` calls `handleReady`, then `Advance`, then
`send` for each message (`concurrent.go`, the comment at the loop). `node.Advance` returns only once
`run` has taken the `advancec` rendezvous (or is stopped). `run` arms `advancec` only in the `readyc`
arm, after `n.rn.acceptReady(rd)` has returned (`node.go:435-446`), and `acceptReady` ends with
`traceReady`, the `Ready` line that mints the tokens. So every message is handed to the network after
its sender's `Ready` line, and the tokens are there at `Advance`'s return.

### 2.4 `send` (one goroutine per message)

| Go | Statement used | Old → new |
|---|---|---|
| `c.net.Add(1)` (in `app`), `go func(){…}` | `netJoin.wp_Add` (§6, Q34): the caller's `njAdder ⅓` and its thread token in, `njDone` out; the `go` by `wp_fork_tok_self`, which gives `app` a fresh token back (B5) | new (harness-local) |
| `time.Sleep`, `c.replica(m.GetTo())` (proved), `m.GetType()`, `m.GetTo()`, `isolated.Load` | Perennial, `Cluster.replica.wp_proof`, the message getters | unchanged |
| `dst.node.Step(ctx, m)` | **`node.Step.tracedSpec`**, now a corollary: `stepIn_intro` (with `trTok`) then `node.Step.spec` | statement text unchanged (F2) |
| `if typ == pb.MsgSnap` (twice) | the law **`trTok_type`**, read before `Step` consumes the token: `trTok γ st ⊢ trTok γ st ∗ ⌜Cluster.trace γ ≠ none → st.msg.Type' ≠ MsgSnap⌝` | new law. Both `ReportSnapshot` calls are dead |
| `src.node.ReportUnreachable(to)` | `node.ReportUnreachable.spec` (`isNode` only; it may run after `src` is stopped: `<-n.done`) | unchanged: its traced content is `run`'s `recvc` arm on `UnreachPath` |
| `c.Dropped/Delivered.Add`, `cancel` | Perennial | unchanged |
| `defer c.net.Done()` | `netJoin.wp_Done` (the slot's thread token back) | new |

A dropped or timed-out message's token is discarded (the logic is affine). At most once holds
because the token is consumed by the one `Step` that delivers it.

---

## 3. The node API's traced statements, and the gated `node.run` that proves them

### 3.1 The client statements (`TracedNodeApi.lean`, on `etc/api/raft.txt`)

Design rule (revised, F2/F3; revision 2, A5): **one proved spec per function**; a gate lives in a
sealed predicate (`stepIn`, `nodeDriver`, `isNode`'s invariants), never as a second triple to keep in
step with the first. Where a traced client needs more than today's post (`Ready`, `Advance`), the
traced statement is **the one proof**, and today's spec, text unchanged, is its instance (a corollary,
never a second proof): `isReadyChan_recvAu` drops the claim, `node.Step.tracedSpec` is
`stepIn_intro` with `node.Step.spec`, and `node.Advance.spec` is `node.Advance.tracedSpec` at `ms = []`
(`readyToksClaim_nil`). Every one of them holds for every `γ`, traced or not, so no existing client
changes but §3.5's refusals and F2's `stepIn_intro` premise.

| Function | Old (today) | New |
|---|---|---|
| `StartNode` | `StartNode.gatedSpec` (frozen Draft, over `startTrace`); `StartNode.tracedSpec D` (hypothesis, `D` free) | A8.3: the gated post gains `startDoneB γ cv.ID'`; `StartNode.tracedSpec` has no parameter, its post the sealed `startDone γ cv.ID'`. Proved from `setupNode`'s traced spec (§5) |
| `node.Tick` | `node.Tick.spec` | unchanged |
| `node.Ready` / `isReadyChan_recvAu` | untraced law; `.tracedSpec` (hypothesis) with `readyGotT` = `readyGot` ∗ `[∗list] q ∈ ms, trTok γ q.st` (**unprovable**, 29n finding 4) | `readyGotT` = `readyGot` with **`readyToksClaim n γ N ms`** as its last conjunct, inside its existentials at `readyRest`'s `ms` (Probe A, P2: as a separate conjunct, `ms` would be unbound). `.tracedSpec` a theorem; `isReadyChan_recvAu` stays proved for every `γ` (it drops the claim) |
| `node.Advance` | `node.Advance.spec` (no tokens) | New **`node.Advance.tracedSpec`**, the one proof (A5): `node.Advance.spec`'s pre ∗ `readyToksClaim n γ N ms`; post: its first disjunct ∗ `[∗list] q ∈ ms, trTok γ q.st`; the stopped disjunct gives nothing. **`node.Advance.spec`: text unchanged, every `γ`, now its instance** at `ms = []` (`readyToksClaim_nil` in, the empty list out). F3: `run` needs nothing back |
| `node.Propose` | `node.Propose.spec` | unchanged (the `propc` payload's entry is normal by construction) |
| `node.ApplyConfChange` | `node.ApplyConfChange.spec` | unchanged (traced content: `run`'s `confc` arm) |
| `node.Step` | `node.Step.spec` (`stepIn`); `.tracedSpec` (hypothesis) | **`node.Step.spec` unchanged, proved for every `γ`** (F2). `stepIn`'s sealed body is gated through `stepP` (§3.2 items 5-6). **`stepIn_intro` gains `trTok γ st`.** `node.Step.tracedSpec` is a corollary. New law `trTok_type` |
| `node.ReportUnreachable` | `node.ReportUnreachable.spec` | unchanged |
| `node.Stop` | `node.Stop.spec` | unchanged |
| `node.ReadIndex`, `.TransferLeadership`, `.ForgetLeader`, `.ReportSnapshot`, `.ProposeConfChange` | no trace premise | **refused at a traced node** (§3.5): each gains `Cluster.trace γ = none →` |

```lean
-- InvNode.lean (moved from TracedNodeApi.lean: `stepIn_intro` is here; its sealed body needs only a
-- private import of `TracedRecvTok`, which `InvNodeChan` already reaches through `InvRawnodeReady`)
-- (revision 3, S1) the body over a `RaftNames`, so that `rtkInv` (in `isNodeChan γn`, which has no
-- `Cluster`) can state its slots at `γn.raft`; `Cluster.trace γ = γ.raft.reTrace` (`InvNode.lean:84`);
-- sealed as `trTok` is (the package's proofs `import all`)
@[no_expose] def trTokR (ρ : RaftNames) (st : MsgSt) : IProp GF :=
  match ρ.reTrace with
  | none => iprop(True)
  | some γd => iprop(⌜TrSent st⌝ ∗ recvTokOf γd st.msg st.ents st.ctx)
@[no_expose] def trTok (γ : Cluster) (st : MsgSt) : IProp GF := trTokR γ.raft st

theorem stepIn_intro (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (src : w64) (st : MsgSt) :
    st.msg.To' = id →
    sentMsg (GF := GF) γ N src st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ∗ snapLocalMsg γ id st ∗ trTok γ st ⊢        -- new conjunct
    |==> stepIn γ N id ml

/-- The driver's claim on the tokens of a received `Ready`'s messages `ms` (sealed; exclusive).
Untraced `True`. Traced: `ms = []` (nothing claimed: F3's claim-less driver, whose request records
`none`; revision 2, A5), or the driver's element of the node's escrow (`rtkInv`, §3.2 item 2) at the
`Ready`'s key `j`, recording `ms`, with the persistent bound "key `j` allocated" (`monoNatLb γn.al
(j + 1)`; revision 2, A1). **A departure from "no identification handles"** (PRINCIPLES): a
resource every traced driver threads from `Ready` to `Advance`. It carries content (which messages
the tokens are for), and a driver that drops it loses only the tokens, never the node's progress.
Alternative considered: keep `ms` inside the sealed `nodeDriver`, which needs a field of the
client-visible `NodeDriverState` (and `afterReady`'s argument) set by every client. **Also a departure
from "No disjunction of alternative specs"** (revision 3, S7): its traced body is "nothing claimed, or
the element". The disjunction is what makes `node.Advance.spec` an instance of the one traced proof
(A5) instead of a second proof; the alternative, two triples for `node.Advance`, is what PRINCIPLES'
rule is there to prevent. -/
@[no_expose] def readyToksClaim (n : Loc) (γ : Cluster) (N : Namespace) (ms : List QMsg) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(True)
  | some _ => iprop(⌜ms = []⌝ ∨ ∃ γn j, ⌜NodeOk γ γn ∧ γn's node is n⌝ ∗ isNodeChan γn … ∗
      ghostMapElem γn.rtk j (DFrac.own 1) ms ∗ monoNatLb γn.al (j + 1))

/-- (A5) Nothing claimed: what `node.Advance.spec` (the instance) passes. -/
theorem readyToksClaim_nil (n : Loc) (γ : Cluster) (N : Namespace) : ⊢ readyToksClaim (GF := GF) n γ N []

/-- (A5) **`node.Advance`'s client spec, the instance**: `node.Advance.tracedSpec` at `ms = []`,
`readyToksClaim_nil` for the claim, `[∗list] q ∈ [], _` dropped. Its text is today's. -/
theorem node.Advance.spec_of_traced (h : node.Advance.tracedSpec) : node.Advance.spec

abbrev node.Advance.tracedSpec : Prop :=
  ∀ n γ N id st es L v (ms : List QMsg), st.handling = some (es, L) →
  (∀ l, L = some l → l.dlv.length = uint.nat l.snap.Metadata'.Index') →
  {{ isPkgInit pkg_id.go_etcd_io.raft.v3 ∗ isCluster γ N ∗ isNode n γ N id ∗ nodeDriver n γ N st ∗
      advReceipt st.storage st.delivered.length es L ∗ nodeConfig n γ N v ∗ (match L with …) ∗
      readyToksClaim n γ N ms }}
    n.Advance()
  {{ RET #(); (nodeDriver n γ N { st with handling := none } ∗ nodeAppliedLb γ st.key st.delivered.length ∗
        (match L with …) ∗ [∗list] q ∈ ms, trTok γ q.st) ∨
      (nodeStopped n γ N ∗ nodeDriver n γ N { st with handling := none }) }}
```

**F2's call sites (checked).** `stepIn_intro` is used at four places; each holds
`h : Cluster.trace γ = none` (from `cluster_alloc`, `InvNodeRule.lean:214`) and discharges the new
conjunct by `trTok_untraced γ st h`:
- etcd's server, `InvNet.lean:101` (`stepIn_of_recv`): it opens `srvClusterOk γ.srv`
  (`SrvRaftLog.lean:768`, the last conjunct `⌜Cluster.trace γ.raft.cl = none⌝`); the same `icases`
  names it.
- kvreconf, `Cluster__step.lean:93`: `isClusterC`'s `%Htr0` (`DefsCluster.lean:292`).
- kvdurable, `Cluster__step.lean:90`: `isClusterC`'s `%Htr0` (`kvdurable/Defs.lean:681`).
- kv, `deliver.lean:90`: **not held today**. `deliver.spec` holds `kvPeerOk γ id nd` per peer
  (`kv/Cluster.lean:100`), which carries `⌜γ.snapLoc id = none⌝` but not the trace. kv's own predicate
  `kvPeerOk` gains `⌜Cluster.trace γ = none⌝`, introduced at its one construction
  (`StartCluster.lean:398-401`), where `kvCluster_alloc`'s `%Htr0` is in scope (`StartCluster.lean:296`).
  `deliver.spec`'s text is unchanged; kv's `interface/` changes by `kvPeerOk`'s body.

`node.ProposeConfChange` (`node__ProposeConfChange.lean:116-122`) builds `stepIn` by unfolding it
(not through `stepIn_intro`) for its conf-change `MsgProp`. With `fwdP` gated on normal entries it
cannot do so at a traced node: its refusal premise (§3.5) is what its proof uses. `node.Step.wp_proof`
itself is unchanged: it passes `stepIn`'s `stepP` to `stepWithWaitOption` whatever `stepP` is. The
`RaftWitness` part has its own copy of raft and is not touched.

### 3.2 The gated `node.run`

**`node.run.spec`**. Old: `∀ γ id n, γ.raft.reTrace = none → {{ isPkgInit ∗ isNodeChan γ id n ∗ runPre γ id n }} n.run() {{ True }}`.
**New, at the end of the work** (§9 "Order of work"): the premise dropped, one spec for both modes, the
traced content in the invariants it opens. Until every traced arm is proved, today's statement stays
and the gated one is the separate theorem `node.run.gated_of` (§9). Its `wp_proof` cites the callee
specs it cites today, plus `raft.Step.spec` with the proved `stepBundle_traced` (slice 30c, applied as
`stepBundle_traced.on_of_statement` / `onG_of_statement`), `raft.tickElection.spec`,
`raft.tickHeartbeat.spec`, and the traced RawNode triples of §3.3.

**What the node's invariants gain (sealed, raft-internal; each gate's `none` arm is today's body):**
1. **`ownRawNode`'s traced conjunct** (`rnTrace`, slice 25n) gains (added only once their facts are
   proved, §9's order, B1):
   - *(a) flag to delivery* (29n finding 2): `rs.delivered ≠ [] → b = true` for the capability's
     `∃ b`. `rnTrace` takes `rs.delivered` (or the clause sits next to it in `ownRawNode`).
     Established where `delivered` grows (`acceptReady`, `RawNode.Ready.traced`: the `Ready` line sets
     the flag first). **Kept by a step** (revision 3, N1) through the bundle's monotone flag: the end
     resource gives `∃ bt', ⌜bt = true → bt' = true⌝ ∗ trCapB … bt' …` (§3.6), `delivered` is
     unchanged, and if it is non-empty the pre's flag `bt` was `true` by (a), so `bt' = true`.
   - *(b) the outbox's types* (§3.6, G1; revision 2, A2): `TrScope s ∧ ∀ m ∈ s.outbox, TrOutMsg m`, with
     `TrScope s := s.lt = W64 0 ∧ ReadIdle s` (no transferee; no pending read: `s.rd.ro`'s queue and
     `s.rd.pend` empty). Kept by `raft.Step.tracedTriple`'s new `OutTyStep` (§3.6). The physical queues'
     half is in `XfOk` (§3.6), not here.
   - *(c) the leader exclusion* (§3.4): `s.role ≠ follower → applied ≥ |γ.reBoot|`.
   - *(d) no automatic leave* (revision 2, A3: G3 (b), §3.4 item 4; revision 3, S5): `c.autoLeave =
     false` for the configuration `c` the struct is at. "Not joint", `c.outgoing = ∅`, is already
     `trCapB`'s pure clause at that `c` (`TracedCap.lean:1085`); 1(d) adds only the flag.
   - *(e) applied below the configuration index* (revision 2, B3: lemma (ii), §3.4 item 3; revision
     3, N2: gated on the mode): `rs.mode.isDyn = true → uint.nat s.logst.applied ≤ rs.capplied`. In
     `rnTrace` (traced only, so that no untraced proof is re-opened for it), which takes `rs.capplied`
     and `rs.mode` beside `rs.delivered`. Every node of the node API is dynamic (`StartNode.lean:319`),
     and the `confc` arm's `DynCCPreOp` gives `isDyn` where it is read.
2. **The node's token escrow** (F3; new, per node). `NodeNames` gains the fields `rtk : GName` (a ghost
   map `Nat ↦ List QMsg`, the `Ready`s' keys), `np : GName` (an exclusive token), `dep : GName` (a
   monotone count of the keys deposited) and (revision 2, A1) `al : GName` (a monotone count of the keys
   allocated), allocated in `newNode`/`setupNode` (per node, S12). A new invariant, in `isNodeChan`
   (persistent), gated on `γn.raft.reTrace`, in the **fixed namespace `rtkN := nroot.@"raft_rtk"`**
   (revision 3, S1; revision 2's `N.@"rtk"` is not expressible there: `isNodeChan γn id n`,
   `InvNodeChan.lean:1242`, takes no `N` and no `Cluster`, and its invariants have fixed names,
   `advN`, `tickN`, `budgetN` = `nroot.@"raft_…"`, from which `rtkN` is disjoint). Where it is opened
   (S1): at the `readyc` commit in a `|={⊤}=>` prefix of `run`'s send AU, before the handshake's
   `inv nroot` is opened (item 3); at the `advancec` rendezvous inside `advInv`'s AU, at `⊤ ∖ ↑advN`
   (item 4). Its slots hold `trTok`'s traced body over `γn.raft.reTrace` (`Cluster.trace γ =
   γ.raft.reTrace`, `InvNode.lean:84`, and `NodeOk γ γn` gives `γn.raft = γ.raft`, so the driver's
   `trTok γ q.st` is the slot's content):
   ```
   rtkInv γn := inv rtkN (∃ (M : GMap Nat (List QMsg)) (a : Nat) (pend : Bool),
     ghostMapAuth γn.rtk 1 M ∗ ⌜dom M = [0, a)⌝ ∗ (if pend then own γn.np (Excl ()) else True) ∗
     monoNatAuth γn.al a ∗                                   -- revision 2 (A1)
     monoNatAuth γn.dep (if pend then a - 1 else a) ∗
     [∗map] j ↦ ms ∈ M, ⌜j < (if pend then a - 1 else a)⌝ -∗
        (([∗list] q ∈ ms, trTokR γn.raft q.st) ∨ ghostMapElem γn.rtk j (DFrac.own 1) ms))
   ```
   (`trTokR ρ st` is `trTok`'s body at `ρ.reTrace`; `trTok γ st := trTokR γ.raft st`.)
   (`pend`: the last key's tokens not yet deposited; a key below the deposited count stays deposited,
   since the count only grows. The slots hold the client's `trTok` bodies, `⌜TrSent q.st⌝ ∗
   recvTokOf …` (revision 2: not `readyTok`, so that the escrow and `node.Advance.tracedSpec` land before
   `readyTok`'s body gains `TrSent`, §9's order); `run`'s deposit turns `acceptReady`'s `readyTok`s,
   whose traced body becomes the same, §3.6, into them.) The claim, traced: §3.1's `readyToksClaim`
   (`⌜ms = []⌝`, or the element `j ↦ ms` with `monoNatLb γn.al (j + 1)`).
   `run`'s loop invariant holds `own γn.np (Excl ())` whenever no deposit is pending (idle and busy).
3. **`readyc` commit** (`readyP`, the `readyc` payload). `readyc` is a Perennial handshake
   (Perennial's `Chan/Idioms/Handshake.lean:46`, `inv nroot`): inside its AU the mask is `⊤ ∖ ↑nroot`, under which no namespaced
   invariant opens, and today's `handshake_send_au_upd` (`InvNodeChan.lean:1429`) takes a basic update
   `|==> (P v ∗ ▷ (Q -∗ Φ))`. Revision 3 (S1) adds the variant **`handshake_send_au_fupd`**, the same
   with `|={⊤}=> (P v ∗ ▷ (Q -∗ Φ))`, sound since `sendAu` begins with `|={⊤,∅}=>` (its proof runs the
   update first, then `handshake_send_au_upd`'s). The update runs only at the commit: a waiting
   sender's `sendAu` is executed by the receiver's thread at the rendezvous
   (`Chan/AuSpec/ChanAuRecv.lean:227-262`), so a `select` that fires another case allocates nothing. In that
   prefix `run` opens `rtkInv`, inserts the fresh key
   `a ↦ ms` (the `Ready`'s handed-out messages), raises `al` to `a + 1` and takes
   `monoNatLb γn.al (a + 1)`, sets `pend := true` by putting `np` in, and puts the element `a ↦ ms` with
   that bound (the claim's right disjunct) into `readyP`. **After `acceptReady`** (same arm, before
   `advancec` is armed, `node.go:436-438`): `run` opens `rtkInv` with `acceptReady`'s `"Htoks"`, takes
   `np` back, sets `pend := false`: key `a`'s tokens are now deposited (`dep` raised to `a + 1`).
4. **`advInv`** (the `advancec` protocol). `run` lends `np` at the rendezvous: `advDep` (run first,
   `RcvPending`) and the `SndPending → RcvCommit` step (driver first) carry it. The driver's request
   `γ.req` (fixed name; `AdvReq` gains `Option Nat`) records its claim's key `j`, or `none` (untraced, or
   the claim's left disjunct `ms = []`).
   - **`RcvPending` (run first).** `advDep` gains `own γn.np (Excl ())`. The driver, at its send's
     commit (inside the channel's AU, at `⊤ ∖ ↑advN`), opens `rtkInv`: `pend` is `false` (else the invariant's `np` and
     `advDep`'s are two), so the deposited count is `a`; its element gives `j ∈ dom M = [0, a)`, so
     `j < a` and the key's slot holds the tokens (not the element: the driver holds that one, and two
     full elements conflict). It swaps its element in and takes the tokens. It leaves `np` in `advRet`
     for `run`.
   - **`SndPending` (driver first; revision 2, A1).** The driver's payload in `advInv` is persistent
     only: `req`'s half with `j` and **`monoNatLb γn.al (j + 1)`** (a copy of its claim's bound); its
     element stays with it. **The driver's offer** can be made while `pend = true` (it got its claim at
     the `readyc` commit and may call `Advance()` before `acceptReady` returns); **its logical
     `SndPending` is entered by `run` at the rendezvous** (revision 3, S1: `run`'s thread runs the
     driver's waiting `sendAu`, `Idle → SndPending`, and its own `recvAu`, `→ RcvCommit`, in one step,
     `Chan/AuSpec/ChanAuRecv.lean:227-262`). The allocation bound is still needed: the driver's AU closure cannot
     see `run`'s `np`. `run` reaches its `advancec` receive only after the deposit, holding `np`; it
     opens `rtkInv` (at `⊤ ∖ ↑advN`): `pend = false`, so
     `dep`'s count is `a`, and the payload's bound against `monoNatAuth γn.al a` gives `j + 1 ≤ a`; it
     mints **`monoNatLb γn.dep (j + 1)`** and puts it in the `RcvCommit` answer (with the agreeing `req`
     half). The driver, at `RcvCommit → Idle` or later, opens `rtkInv` with its element and that bound:
     `j` is below the deposited count whatever `run` has allocated since (`pend` may be `true` again, for
     a later key `a' - 1 ≥ j + 1`), so its slot holds the tokens; it swaps its element in and takes them.
   - A driver without a claim (`ms = []`: `node.Advance.spec`, the instance) takes nothing: a key it
     received stays in `rtkInv` with its tokens forever. **`run` needs nothing back but `np`, which is
     its own and which `advRet`/`RcvCommit` give back in both orders, whatever the driver holds.** So the
     instance is the traced proof at `ms = []` (A5).
   - A stale claim (a key `j` from an earlier `Ready` the driver advanced without it) is harmless:
     its bound `monoNatLb γn.al (j + 1)` still holds, its key is deposited, and the traced spec delivers
     its `ms`.
   - **Both orders against the Go** (`node.go` `run`, re-read for revision 2): `advancec` is set only in
     `case readyc <- rd:`, after `n.rn.acceptReady(rd)` returns (`:435-441`, `asyncStorageWrites`
     false), and `acceptReady`'s last statement is `traceReady` (`rawnode.go:437`); the loop head arms
     `readyc` again only when `advancec == nil` (`:354`), i.e. after `case <-advancec:` (`:443-446`)
     has run `n.rn.Advance(rd)` and cleared it. So `run`'s receive on `advancec` (the `RcvPending`
     offer, or its meeting of a `SndPending` driver) happens only between a key's deposit and the next
     key's allocation: `pend = false` there, which `np` makes a logical fact. The driver's send, in
     contrast, can be offered at any time after its `Ready` receive (it is the other goroutine): the
     `SndPending` case covers an offer made while `pend = true`, the `RcvPending` case one made after
     `run`'s offer. `Advance()` itself is a send on the unbuffered `advancec` or a receive on `done`
     (stopped: nothing taken, nothing owed).
   - Untraced (`Cluster.trace γ = none`), `rtkInv` is `True` and `np` is not used: today's protocol.
5. **`netP`** (the `recvc` payload), gated:
   - traced, the network disjunct also carries `⌜TrNetTy st.msg.Type'⌝ ∗ recvTokOf γd st.msg st.ents st.ctx`,
     or its type is `MsgUnreachable` (`ReportUnreachable`); the second disjunct `hupP` (`Campaign`) is
     kept;
   - untraced, today's `netP`.
6. **`fwdP`** (a forwarded proposal on `propc`), gated: traced, `∀ e ∈ st.ents, e.Type' = EntryNormal`.

`stepIn` itself is unchanged; `NodeOk γ γn` gives `γn.raft = γ.raft` (`InvApi.lean:1649`), so the
gates read `Cluster.trace γ`. `stepIn_intro`'s proof (`ApiImpl.stepIn_intro_impl`) splits on the trace:
untraced, today's; traced, `trTok`'s `TrSent` sends a `MsgProp` to `fwdP` (normal entries) and the
rest to `netP` with its `TrNetTy` and token.

**Arm by arm** (the `select` in `node.go`'s `run`):

| Arm (Go) | Callee triple | Proved? | Premises from where |
|---|---|---|---|
| loop head: `n.rn.HasReady()`, `n.rn.readyWithoutAccept()` | `HasReady`, `readyWithoutAccept.spec` (one spec for both modes, slice 28n) | yes (re-opened by 1(a)-(e), §3.3) | `ownRawNode` |
| `case pm := <-propc: m.From = r.id; r.Step(m)` | `wp_rn_raft_Step_prop_traced` over `stepBundle_traced.onG PropAny` | yes (25n, 30c; re-opened, §3.3) | `PropAny`: `MsgProp`, non-empty, **normal entries** (`propP`; `fwdP`'s gated clause), `γ.reBoot ≠ []` (`trCapB_reBoot`). The bounds from the ceiling (below) |
| `case m := <-recvc` (guard: response from an unknown `From` → drop; else `r.Step(m)`) | `raft.Step.traced` (`raft.Step.tracedTriple`, slice 30c) | yes (re-opened, §3.3) | the token and `TrNetTy` from `netP` (5.); `StepNodeOk`'s `MsgAppResp` clause from the guard's `Progress` lookup; `MsgUnreachable` at term 0 (`UnreachPath`); `MsgHup` from `hupP`. The rest: §4 |
| `case cc := <-confc: r.applyConfChange(cc)` | traced `raft.applyConfChange` → traced `switchToConfig` | **no** (29n items 1-2) | the capability **booted** by 1(a) (kept through every step by the monotone flag, revision 3, N1): `DynCCPre` puts the entry inside the delivered log. `trCapB_hookGate_applyCC` (proved) at a follower; the leader excluded by 1(c), lemma (ii) and G3 (a) (§3.4); the result simple, 1(d) kept, by G3 (a) (the entry a bootstrap `AddNode`) |
| `case <-tickc: n.rn.Tick()` | `RawNode.Tick.traced` (26n) | yes (re-opened, §3.3) | `tickInv`'s credit; the bounds |
| `case readyc <- rd: n.rn.acceptReady(rd)` | `RawNode.acceptReady.spec` (one spec, 28n): fires the `Ready` line, post `[∗list] q ∈ ms, readyTok γ q.st` | yes (re-opened: `readyTok`'s body, 1(a) established, 1(b) by the emptied outbox; 1(c), 1(d) framed: B7, §3.3) | `ownRawNodeReady`; the escrow's allocation (with `al`) at the commit and deposit after (2.-3.) |
| `case <-advancec: n.rn.Advance(rd)` | traced `RawNode.Advance`: `stepsOnAdvance`'s self-addressed responses over `raft.Step.traced` with `pendingRel`'s `selfTok` (Q26 (a)); the storage acknowledgements over `stepBundle_traced_storAck` | **no** (designed in 28n, `AckEnd` done in 30c) | the self tokens from `pendingRel`'s `.self` arm; `TrNoSnap` makes the snapshot arm vacuous; `raft.Step.spec`'s traced `autoLeave` premise at `MsgStorageApplyResp` from 1(d); its `lt` premise at a self `MsgAppResp` from 1(b); lemma (ii)'s `applied ≤ capplied` re-established by the strengthened post `ca = max rs.capplied rs.delivered.length` (revision 3, N2: `advRS`'s `capplied := ca`, and the new `applied` is `rs.delivered.length`). The handed-out tokens are already in `rtkInv` (3.) |
| `case c := <-status` | `getStatus` | yes (reads only) | — |
| `case <-stop: close(done)` | the stop protocol | yes | — |

**The bounds premises of the traced triples** (`uint.Z rs.tc + 1 < traceNumBound`, and
`receiptBound GF + γ.reBoot.length ≤ traceNumBound`): the first from `termLB γ.bud rs.tc` and
`budgetInv` (`rs.tc ≤ receiptBound GF`) with the cluster's `readyFits` (`receiptBound GF + 3 ≤ 2^61`);
the second is `readyFits` itself (`γ.reBoot.length = 3`). Read once per arm; no new invariant.

### 3.3 The RawNode triples `run` uses, and what the new clauses re-open (S5; revision 2, B7; revision 3, N1, N3)

- **Proved, re-opened by `rnTrace`'s new clauses 1(a)-(e)** (each re-establishes `ownRawNode` at a new
  state, so each proof re-establishes the clauses; their statements do not change). They are re-opened
  in the landing that adds the clauses, after the clauses' facts are proved (§9, B1). (e) is framed by
  each of them: none moves `applied` or `capplied` (only `RawNode.Advance` does). (a) is kept by each
  that steps through the bundle's monotone flag (N1: `delivered` unchanged, the flag `true` before if
  `delivered ≠ []`, so `true` after):
  - `RawNode.Tick.traced` (26n): (a) by the monotone flag (it instantiates the tick specs' `Gout` with
    it; their no-step branch keeps the capability as it was); (b) its `raft.Step.traced`'s `OutTyStep`;
    (c) a campaign through `hup` (`HupCampaigns`' `¬ hasUnappliedConfChanges`, with §3.4's lemma (i));
    (d) the configuration unchanged (framed).
  - `RawNode.acceptReady.spec` (28n): (a) established here (the `Ready` line sets the flag before
    `delivered` grows); (b) the outbox emptied, and `TrScope` kept (it changes neither `lt` nor the read
    state's pending queues; it clears `readStates`, which `ReadIdle` does not read); (c) and (d) framed
    (it moves `applying`, not `applied`, and keeps the role and the configuration: B7); its post's
    `readyTok` body changes (§3.6), so it is re-opened for that too.
  - `RawNode.readyWithoutAccept.spec` (28n): reads only; frames the clauses.
  - `wp_rn_raft_Step_prop_traced` (25n) and the `raft.Step.traced` assembly (30c): (b) from the new
    `OutTyStep` conjunct (§3.6, L1, which re-opens the paths); (a) by the monotone flag; (d) frames (no
    step of a traced bundle changes the configuration); (c) `hup` as for `Tick`. `raft.Step.traced`
    also reads `s.lt = W64 0` from 1(b) for `raft.Step.spec`'s `MsgAppResp` premise (§3.6).
  - `stepBundle_traced_storAck` (30c), `stepBundle_traced_unreach` (27n): through the assembly.
  - **Revision 3 (N3): the three traced RawNode triples off `run`'s path**, proved theorems whose
    statements mention `ownRawNode`, so the clauses break them unless re-proved in the same landing:
    - `RawNode.Step.traced` (`TracedRawNode.lean:140`, which calls `wp_raft_Step` directly): as the
      `recvc` arm, (a) by the monotone flag, (b) by `OutTyStep`, (c) by `hup`, (d) framed; it reads
      `s.lt = W64 0` from 1(b) for the `MsgAppResp` premise.
    - `RawNode.Ready.traced` (`TracedRawNodeReady.lean:89`): moves `delivered`, so it establishes (a)
      as `acceptReady` does (the `Ready` line first); (b)-(e) as `acceptReady`.
    - `RawNode.ReportUnreachable.traced` (`TracedRawNodeRep.lean:58`): a `MsgUnreachable` through the
      bundle; (a)-(d) as `raft.Step.traced`, and the `lt` premise vacuous (not a `MsgAppResp`).
    Deleting them instead (`run` reaches none) was the review's other option; they are kept, since
    each costs one re-proof and they are the models the `recvc` arm follows.
- **Proved, unchanged:** `trCapB_hookGate_applyCC`, `traceConfChangeEvent.tracedSpec_proof` (29n).
- **Not yet:** the traced `RawNode.Advance` (28n's design); the traced `raft.applyConfChange`,
  `raft.switchToConfig`, `RawNode.ApplyConfChange` (29n items 1-2); the traced `newRaft`,
  `NewRawNode`, `Bootstrap`, `setupNode` (§5).
- The alternative S5 offered (keep a clause only `run` reads in `run`'s own invariants) does not apply:
  1(a) needs the capability's flag, which only `rnTrace` sees; 1(b) and 1(c) change inside
  `raft.Step`; 1(d) is read inside the traced `RawNode.Advance` (its `raft.Step` premise). So the clauses
  go into `rnTrace` and the re-openings above are the cost.

### 3.4 `switchToConfig`: the read-only lending, the leader case

- **Read-only lending** (29n finding 1, (a)): `traceEvent.spec` takes `RaftReadLend` (the hard state's
  fields, `raftLog`'s `lastIndex`, `state`, `id`, the tracker's `Config.Voters` maps; no `Progress`) in
  place of `RaftLend`. `raftLend_self` gives it from the whole struct; the `Changer` specs give back the
  old configuration's maps, only read (`Config.Clone`); `switchToConfig` lends them from its open
  struct. `traceConfChangeEvent.spec` becomes one spec over `RaftReadLend`; its callers are
  `switchToConfig` and `newRaft`'s call (A7).
- **The leader case** (29n finding 3; restated, S6). `AccIdle` (`TraceSimMatch.lean:4437`) says: no
  outgoing configuration, `commit ≤ |log|`, no pending conf change, the last committed conf entry is
  the configuration. It says nothing of the role. The obstacle at a leader is elsewhere: there
  `switchToConfig` (`raft.go:2015-2028`) also logs the `Commit` line through `maybeCommit` and sends
  through `bcastAppend`/`maybeSendAppend`, which `trCapB_hookGate_applyCC` (needing the phase `SimIdle`,
  `TracedApplyCC.lean:174`) covers neither. **Excluded instead of proved**, by:
  1. `raft.hup` refuses to campaign while `hasUnappliedConfChanges()` (`raft.go:1001`), and every way
     out of the follower role goes through `hup` at a traced node (`prevote = false`; `MsgTimeoutNow`
     needs a transfer, refused). `hasUnappliedConfChanges` is false iff `applied ≥ committed` or no
     conf entry in `(applied, committed]` (`raft.go:1013-1038`).
  2. **Lemma (i), the bootstrap log prefix** (S7): at a traced node, `committed ≥ |γ.reBoot|` and the
     log's entries `1..|γ.reBoot|` are the bootstrap conf entries. Source: `Bootstrap` appends `boot` and
     commits it (A7's positions `k + 4`), `committed` is monotone, and the committed log's prefix is
     `boot` (`isCommittedLogLb γ boot`, `cluster_alloc`'s) with `ownRawNode`'s log agreeing with the
     committed log below `committed`. With 1, a campaign happens only at `applied ≥ |γ.reBoot|`:
     otherwise entry `applied + 1 ≤ |γ.reBoot| ≤ committed` is a conf entry. `applied` is monotone, so
     clause 1(c) `role ≠ follower → applied ≥ |γ.reBoot|` holds from then on.
  **Convention** (revision 3, S8): a *position* `k` is 0-based (the `k`-th entry of a log, `k <
  |log|`), an *index* `i` is raft's 1-based log index (`i = k + 1`). "Position `≥ |γ.reBoot|`" and
  "index `> |γ.reBoot|`" name the same entries, those past the bootstrap log.
  3. **Lemma (ii), the `confc` arm** (S7; revision 2, B3: the short form; revision 3, N2: the
     source). An entry the `confc` arm applies sits at a position `k` with `k + 1 > raftLog.applied`.
     Stated as clause 1(e) of `rnTrace` (traced, dynamic mode; `CapOk`, `InvRawnode.lean:932`, already
     bounds `rs.capplied` by `committed`, the other way): `rs.mode.isDyn = true → uint.nat
     s.logst.applied ≤ rs.capplied`. Then at the arm `DynCCPre` (`InvRawnode.lean:555-557`) gives
     `rs.capplied ≤ k`, so `applied ≤ k`, i.e. `k + 1 > applied`.
     - **Source of the clause: the configuration index `RawNode.Advance` installs, not the driver's
       view.** `raftLog.applied` moves only at `RawNode.Advance` (`MsgStorageApplyResp`'s `appliedTo`,
       sync mode), to `applying`, which is `rs.delivered.length`; the ghost step there is
       `StepR.advance`, which sets `cidx := max r.cidx a` (`Protocol/StepR.lean:416`), and the
       configuration index is what `RawNode.Advance` returns as `ca` and `advRS` installs as
       `capplied` (`InvRawnodeReady.lean:1344`). (Revision 2 named the driver's view, `advanceP`'s `ca`
       with `monoNatLbOwn γ.cam ca`: wrong, that is the index past the last applied *conf* change,
       `runCfg`'s `(ca, rs.cfg)`, `InvNodeChan.lean:913-939`, which moves only at `ApplyConfChange`;
       in the probe's run it stays `3` while `applied` becomes `4` at the second `Ready`.)
     - **`RawNode.Advance.spec`'s post, strengthened** (`Spec/go_etcd_io/raft/v3/RawNode__Advance.lean`;
       today `rs.slent = none → rs.capplied ≤ ca ∧ ca ≤ max rs.capplied rs.delivered.length`, :126,
       an upper bound only). New, a separate pure conjunct (so that the existing conjunction's
       destructurings keep their shape):
       ```lean
       ⌜rs.slent = none → rs.mode.isDyn = true → ca = max rs.capplied rs.delivered.length⌝
       ```
       Proof, at the `iapply HΦ $$ %s1.term %ca` site (`RawNode__Advance.lean:2026`):
       `ownStepGhost_rinv` (:457) on the final ghost `ownStepGhost γ (rs.mode.toG ⟨ca, …⟩) cf id s1`
       gives `RInv`, whose `applied_cidx` (`Protocol/StepRInv.lean:268`) is `uint.nat
       s1.logst.applied ≤ ca`; `s1.logst.applied = s.logst.applying` (`Hge` with `applied ≤
       applying`) `= rs.delivered.length` (`Hdlen`); with `%Hca`'s `rs.capplied ≤ ca ≤ max rs.capplied
       rs.delivered.length`, the equality. Callers: `node__run.lean`'s `advancec` arm (the call at
       :1158-1160, through `runCfg_advance`, `InvNodeRun.lean:2673`, which keeps its hypothesis) names
       one more conjunct; nothing else applies the spec but `Link`/`Results`, which pass it through.
       Re-proved in step 2 of §9, not `sorry`ed.
     - Re-established at the traced `RawNode.Advance` (`hAdv`): the new `applied` is
       `rs.delivered.length ≤ max rs.capplied rs.delivered.length = ca`, the new `capplied`. Every other
       triple frames it (§3.3).
  4. **G3 (revision 2, A3; revision 3, S4): (a) cluster-wide, then (b) per node from it.** At a traced
     cluster:
     - **(a) No configuration entry past the bootstrap log**: every entry of every log at a position
       `≥ |γ.reBoot|` has `¬ IsConfEnt e` (`CCModel.lean:65`: type `1` or `2`), fillers included. In
       two parts:
       - **(a1) Non-empty conf entries: a gated clause of the term logs' authority** (the ghost map
         behind `isEntryR`, `Protocol/Ghost.lean:1604`, where each entry is minted once by its term's
         leader and whose fragments every node's log carries through `logRecs`/`leadPrefix`: Log
         Matching): `γ.reTrace ≠ none → ∀ minted e at index i, i > |γ.reBoot| → IsConfEnt e →
         IsEmptyV2 e`. Sealed, raft's. *Established*: `cluster_alloc_traced` (nothing minted past the
         bootstrap log). *Kept* at each minting, the leader's appends in `raft.Step`'s code: a
         proposal's entries (`stepLeader`'s `MsgProp`, at a traced node under `raft.Step.spec`'s
         existing premise `MsgProp → s.gh.tr ≠ none → ∀ e ∈ ents, ¬ IsConfEnt e`,
         `raft__Step.lean:664`, which the traced callers discharge: `propP` (one normal entry), the
         gated `fwdP`); `becomeLeader`'s empty normal entry (`raft.go:961`); a refused conf change's
         empty normal replacement (`raft.go:1341`, not reached); and `appliedTo`'s automatic leave
         (`raft.go:742-761`), an empty `EntryConfChangeV2`: **admitted by the clause** (it is
         `IsEmptyV2`), so (a1) needs neither (b) nor `raft.Step.spec`'s `autoLeave` premise. The
         minting update's statement gains the gated premise; its callers in the leader's append path
         pass the step's premise down (code proofs: `stepLeader`'s `MsgProp` branch and
         `becomeLeader`, to list at threading).
       - **(a2) Empty `ConfChangeV2`s: from the existing per-entry record, no new ghost state.**
         Every non-boot entry's `isEntryR` carries `ev2Rec γ e pt` (`Protocol/Ghost.lean:1598`): in
         the dynamic mode (`γ.reDyn ≠ none`, the node API's), an empty `ConfChangeV2` `e` comes with a
         log `P` of length `uint.Z e.Index' - 1` before it (`logRecsC γ base0 P`) and `CfgAt γ M P c`
         with `c.joint = true`. By induction on positions `k ≥ |γ.reBoot|`: if no entry at a position
         in `[|γ.reBoot|, k)` is a conf entry (the induction hypothesis with (a1)), `P`'s conf entries
         are the bootstrap `AddNode`s (lemma (i), and Log Matching through `logRecsC`), whose fold from
         the simple base `stOf (simple vs)` (`StartNode.lean:317`) is simple whatever the recorded
         decisions (an `AddNode` applied to a simple configuration is simple; one rejected leaves it
         unchanged): `c.joint = false`, a contradiction. **To check at threading** (the review's
         uncertain point): that `CfgAt` over the bootstrap prefix is that fold (the decisions recorded
         for the bootstrap positions, and `CfgAt`'s base, as stated).
       - The registry route (revision 1's) stays dropped: an empty `ConfChangeV2` is a filler
         (`Filler`, `Ghost.lean:1177`), with no ticket and no deposit.
     - **(b) No automatic leave**: clause 1(d) of `rnTrace`, `c.autoLeave = false` (with `trCapB`'s
       `c.outgoing = ∅`), at every traced node.
       - *Established*: `setupNode`, after `Bootstrap`'s three `AddNode`s (`ConfChange` V1, whose `AsV2`
         never enters a joint configuration nor sets `autoLeave`).
       - *Kept*: the configuration changes only in `switchToConfig` (the `confc` arm; `Bootstrap`) and
         at a snapshot's restore (no `MsgSnap` is ever stepped at a traced node: §3.6, `TrNetTy`). At
         the `confc` arm the entry is committed in the node's delivered log at a position `k`; by (a),
         `k < |γ.reBoot|`, so by lemma (i) it is a bootstrap `AddNode`, and the result is simple with
         `autoLeave = false`.
       - *Read*: the traced `RawNode.Advance` (`raft.Step.spec`'s premise `MsgStorageApplyResp → ents
         ≠ [] → c.autoLeave = true → s.gh.tr = none`, `raft__Step.lean:663`) and §4's last row.
     - **Order** (revision 3: no longer a joint induction). (a) is kept by every step on its own ((a1)
       by the minting premises, (a2) from `ev2Rec` and (a1)); (b) is kept at a `confc` step using (a).
       (b) is read only to discharge `raft.Step.spec`'s `autoLeave` premise, which is no longer
       needed for (a).
  5. From 1-4, the node is a follower at the `confc` arm: if not, `applied ≥ |γ.reBoot|` (1(c)) and
     `applied ≤ k` (lemma (ii)), while (a) puts the conf entry at `k < |γ.reBoot|`. So `AccIdle` and
     `SimIdle` apply.

  If (ii) or G3 fails, the fallback is 29n's: a line lemma for `ApplyConfChange` at a leader under the
  corrected specification (with its `Commit` and send lines). That lemma is not argued here.

### 3.5 The calls refused at a traced node

`run`'s `recvc` and `propc` arms can only step what the traced bundle covers (`StepEndTy ∨ AckTy`).
At a traced node the following arrive through those arms and are covered by no path: `MsgReadIndex`
(`ReadIndex`), `MsgTransferLeader` (`TransferLeadership`), `MsgForgetLeader` (`ForgetLeader`),
`MsgSnapStatus` (`ReportSnapshot`), a conf-change `MsgProp` (`ProposeConfChange`).

Each of these five `node.X.spec`s gains the premise `Cluster.trace γ = none`, and `netP`'s traced local
disjunct is restricted (§3.2, 5.). None is called by the harness (`ReportSnapshot`'s calls are dead by
`trTok_type`; the premise stays because another client of a traced cluster could call it, and `run`
could not step its `MsgSnapStatus`). `ProposeConfChange`'s premise is used by its own proof (§3.1).
Cost: L3. Rejected: bundle paths for these types (a transfer is not modelled as one; a conf change is
outside the workload; the other three would each need a `StepEnd` clause for no harness use).

### 3.6 The messages' types at the receiver (G1, G2; revision 2, A2)

`raft.Step.tracedTriple` needs `StepEndTy m.Type' ∨ AckTy m.Type'`, and the `propc` arm needs a
proposal's entries normal. At the `recvc` arm `netP` gives only `netStepTypes`; `fwdP` gives no entry
types. **No statement today supplies either fact.** The design:

- `TrSent st := TrNetTy st.msg.Type' ∨ (st.msg.Type' = MsgProp ∧ ∀ e ∈ st.ents, e.Type' = EntryNormal)`.
- **At the sender**: `acceptReady`'s tokens `readyTok γ q.st` become `⌜TrSent q.st⌝ ∗ recvTokOf …`;
  they go through `rtkInv` to the driver as `trTok` (same body). `acceptReady` proves `TrSent q.st` for
  each handed-out `q` from `outboxRelP` (`msgAbs q.st a`): if `a = some x`, `x ∈ s.outbox` and
  `rnTrace` 1(b) gives `TrOutMsg x` (below), which `msgAbs` turns into `TrSent q.st` (the abstract type
  is `mtypeOf` of the physical one; a `propose`'s entries are the message's); if `a = none` (a type
  without abstraction), `XfOk`'s new clause refutes it (the physical half, below).
- **Through the client**: `stepIn_intro` takes `trTok` (with `TrSent`) into the gated `stepP`: a
  `MsgProp` to `fwdP` (normal entries), anything else to `netP` (`TrNetTy` with the token).
- **The type list, against the Go** (unchanged from revision 1). The handed-out messages are `r.msgs`
  and the `msgsAfterAppend` not to self (`rawnode.go:145`, `:179-183`; the self ones go to
  `stepsOnAdvance`, `:414-417`). Their types at a traced node: `MsgApp`, `MsgHeartbeat` (leader),
  `MsgVote` (candidate), the three responses (`TrNetTy`), and a follower's forwarded `MsgProp` (normal
  entries, by `PropAny`). Excluded: `MsgReadIndexResp` (only from a pending read: `ReadIdle`),
  `MsgTimeoutNow` (`lt ≠ 0`), `MsgSnap` (`maybeSendSnapshot` only after compaction, which `TrNoSnap`
  refutes at `maybeSendAppend`'s two fallbacks, `raft__maybeSendAppend.lean:121-124, 431-434`; and
  `raft.send.spec`'s traced premise `mtypeOf m.Type' ≠ some .snap`: revision 2 cites these, not
  `ReplSends`, whose `.snap` exclusion needs the no-snapshot mode, off at raft's level), pre-votes
  (`prevote = false`), forwarded `MsgReadIndex`/`MsgTransferLeader` (only from stepping those types,
  which `StepEndTy` excludes), storage messages (`AsyncStorageWrites = false`: `:163-173` not taken).
  `TrScope` is kept: only `MsgReadIndex` adds a read and only `MsgTransferLeader` sets `lt`, both
  excluded; `becomeX` resets `lt`.

**The abstract half: `OutTyStep`, in `stepBundle_traced.statement`'s post (A2).** In
`StepGhostMode.lean`, next to `OutTrStep`:
```lean
def TrScope (s : NState) : Prop := s.lt = W64 0 ∧ ReadIdle s
def TrOutMsg (m : Msg) : Prop :=
  m.ty.traced = true ∨ (m.ty = .propose ∧ ∀ e ∈ m.entries, e.Type' = EntryNormal)
/-- A traced step in scope stays in scope and queues only traced types or normal proposals. -/
def OutTyStep (s s' : NState) : Prop :=
  s.gh.tr.isSome → TrScope s → TrScope s' ∧ ∀ m ∈ s'.outbox, m ∈ s.outbox ∨ TrOutMsg m
theorem OutTyStep.of_none (h : s.gh.tr = none) : OutTyStep s s'
```
- **Where it goes: the caller's end resource, not `stepClose`'s definition.** `stepBundle_traced.statement`
  (and `.on`/`.onG`/`.onA`, the per-path forms, `TracedRaftStep.lean`) end with
  `stepClose γ md c id m ents ctx s R Gout` at `Gout s' := ∃ bt', trCapB … (SimIdle C s') (stepLastEv Λ)`
  (`TracedRaftStep.lean:142, :215`). Revision 2 added `⌜OutTyStep s s'⌝`; **revision 3 (N1) makes the
  flag monotone** in the same conjunct's place:
  ```lean
  Gout s' := (∃ bt', ⌜bt = true → bt' = true⌝ ∗
                trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)) ∗ ⌜OutTyStep s s'⌝
  ```
  (`bt` the statement's binder, the pre's flag). `raft.Step`'s code proof returns `Gout s'` untouched
  (it is the caller's), so `raft__Step/*.lean` and `LemmasStepGates.lean`'s `stepClose`/`stepCloseAt`
  do not change; `raft.Step.tracedTriple`'s post, which hands back the capability through `Gout`, now
  also gives the implication and `⌜OutTyStep s s'⌝`, and so do `RawNode.Tick.traced`,
  `wp_rn_raft_Step_prop_traced`, `RawNode.Step.traced` and `RawNode.ReportUnreachable.traced`, which
  call it. `stepClose_anyB` (`TracedRaftStep.lean:146`, its `Gout` the capability alone) takes the
  pre's flag `bt` and gives `∃ bt', ⌜bt = true → bt' = true⌝ ∗ …` (it closes at `true`: the implication
  is `fun _ => rfl`), and the pure conjunct (one line each). A path closes at `true` when it logs a
  line (the fire laws set the flag) and at `bt` when it logs none; either way the implication holds.
  The tick specs (`raft__tickElection.lean:59`, `raft__tickHeartbeat.lean:51`) take `Gout` as a
  parameter: their text does not change; `RawNode.Tick.traced` instantiates it.
- **The carrier, for the broadcasting paths (revision 3, S2; L1 closed).** The path families already
  carry `⌜OutOk s o⌝` indexed by the outbox (`lineF`, `TracedPin.lean:220`; `OutOk s o := ∀ x ∈ o, x ∈
  s.outbox ∨ x.TrOk`, :40), extended at each queued message by `outOk_snoc` and turned into
  `OutTrStep` at the close by `outTrStep_of_outOk` (:57). `OutOk`'s right disjunct is strengthened:
  ```lean
  def OutOk (s : NState) (o : List Msg) : Prop :=
    ∀ x ∈ o, x ∈ s.outbox ∨ (x.TrOk ∧ (TrScope s → TrOutMsg x))
  theorem outOk_snoc (h : OutOk s o) (hx : x.TrOk) (hty : TrScope s → TrOutMsg x) : OutOk s (o ++ [x])
  theorem outTyStep_of_outOk (h : OutOk s s'.outbox) (hs : TrScope s → TrScope s') : OutTyStep s s'
  ```
  (`outTrStep_of_outOk` keeps its statement: it projects `.1`; `outOk_self`, `outOk_perm` keep
  theirs.) The `outOk_snoc` sites each prove `TrOutMsg x` from the message type their gate already
  matches (`fun _ => .inl rfl`-style for a traced type): `TracedRaftStepRecvLeadSend.lean:125`,
  `TracedRaftStepPropBundle.lean:368, 529`, `TracedRaftStepLocal.lean:150`,
  `TracedRaftStepHup.lean:640`, `TracedRaftStepRecvVoteRespWon.lean:365, 490`; and
  `lineF_untraced` (`TracedRaftStepRecvLeadSend.lean:137-162`, the read-index response, an untraced
  type) proves the guarded conjunct by refuting `TrScope s`: it gains the premise `¬ ReadIdle X`,
  which its caller has from the pending read it answers. The guard is this revision's form: the
  review's unguarded `x.TrOk ∧ TrOutMsg x` would have to refute `ReadIdle` inside `lineF_untraced`,
  which has no hypothesis to do it with. The leader's accepted-response family
  (`TracedRaftStepRecvLeadAccGates.lean:252, 408`) carries `OutOk` the same way. At the close,
  `OutTyStep` is `outTyStep_of_outOk` with `TrScope s'` from `StepEnd` (the step neither sets `lt`
  nor adds a read: §3.6's type list). `StepEnd`'s `ReplSends` (which admit `.snap`) are not read.
- **Each path proves it at its close** from the state it closes at (`StepEnd`'s `s'` and the messages
  it queued, which it knows: it built their gates; the broadcasting ones through `OutOk` above): the vote paths queue a `MsgVoteResp`; a candidate's
  campaign `MsgVote`s; the append paths a `MsgAppResp`; the heartbeat paths a `MsgHeartbeatResp` (and
  no `MsgReadIndexResp`: `ReadIdle`); a leader's accepted `MsgAppResp` `MsgApp`s (the snapshot fallback
  refuted by `TrNoSnap`, no `MsgTimeoutNow` since `lt = 0`); a leader's proposal `MsgApp`s; a
  follower's proposal the forwarded `MsgProp` with `PropAny`'s normal entries; `MsgBeat`
  `MsgHeartbeat`s; `MsgHup` the campaign's `MsgVote`s; a stale message's `LowSend` response (`TrNetTy`);
  `MsgUnreachable` and the storage acknowledgements' paths queue `MsgApp`s at most. Untraced, or out of
  scope, vacuous.
- **The files it re-opens** (the 30c assembly's paths, planned work, not a blocker): the statement and
  assembly, `TracedRaftStep.lean`, `TracedRaftStepBundle.lean` (`raft.Step.tracedTriple`,
  `stepBundle_traced`, `stepBundle_traced_storAck`), `TracedRaftStepPaths.lean`; the paths,
  `TracedRaftStepHup.lean`, `TracedRaftStepLocal.lean`, `TracedRaftStepPropBundle.lean`,
  `TracedRaftStepUnreach.lean`, `TracedRaftStepRecv.lean`, `TracedRaftStepRecvApp.lean`,
  `TracedRaftStepRecvAppAccCand.lean`, `TracedRaftStepRecvAppAccFol.lean`,
  `TracedRaftStepRecvAppAccUT.lean`, `TracedRaftStepRecvAppRej.lean`, `TracedRaftStepRecvCand.lean`,
  `TracedRaftStepRecvCandApp.lean`, `TracedRaftStepRecvHb.lean`, `TracedRaftStepRecvLeadAccBundle.lean`,
  `TracedRaftStepRecvLeadAccGates.lean`, `TracedRaftStepRecvLeadNA.lean`, `TracedRaftStepRecvLeadReq.lean`,
  `TracedRaftStepRecvLeadSend.lean`, `TracedRaftStepRecvUTApp.lean`, `TracedRaftStepRecvUTHb.lean`,
  `TracedRaftStepRecvUTResp.lean`, `TracedRaftStepRecvUTVote.lean`, `TracedRaftStepRecvUTVoteResp.lean`,
  `TracedRaftStepRecvVoteResp.lean`, `TracedRaftStepRecvVoteRespWon.lean`,
  `TracedRaftStepRecvVoteRespLost.lean`, and the close helpers of `TracedPin.lean` (27 files); their
  consumers, which pass `Gout` through, `TracedNodeRecv.lean`, `TracedRawNode.lean`,
  `TracedRawNodeRep.lean`, `InvRawnode.lean` (4). No statement outside raft's internals changes.

**The physical half (found in revision 2).** `msgAbs q.st none` holds of a message whose type has no
abstraction (`mtypeOf … = none`), and `absList` drops it: **no conjunct on the abstract outbox can
exclude it**. Of the types raft queues (`XfOk`'s `SentMsgShape`: `sentShapeTypes`), two have none:
`MsgTimeoutNow` (`sendTimeoutNow`: `stepLeader`'s `MsgTransferLeader` case, and its `MsgAppResp` case
when `m.From == r.leadTransferee`) and a forwarded `MsgTransferLeader` (`stepFollower`). Neither is
queued at a traced node in Go (no transfer is stepped: refused, `TrNetTy`; `lt` stays `0` and a
`MsgAppResp`'s sender is non-zero, `raft.Step.spec`'s premise). The design, in raft's code specs, in
the style of the traced premises they already have (`raft__Step.lean:659-664`):
- `raft.send.spec`'s traced premise `s.gh.tr ≠ none → mtypeOf m.Type' ≠ some .snap` becomes
  `s.gh.tr ≠ none → ∃ ty, mtypeOf m.Type' = some ty ∧ ty ≠ .snap`;
- `XfOk id s l` (`InvRaftPhys.lean:426`) gains the clause `s.gh.tr.isSome → ∀ q ∈ l, mtypeOf
  q.st.msg.Type' ≠ none`, which `raft.send`'s proof keeps from that premise and `acceptReady` reads;
- `raft.sendTimeoutNow.spec` gains `s.gh.tr = none`; `raft.Step.spec` gains `m.Type' =
  MsgTransferLeader → s.gh.tr = none` and (revision 3, S3: restricted to the one type whose branch can
  queue a `MsgTimeoutNow`) **`m.Type' = MsgAppResp → s.gh.tr ≠ none → s.lt = W64 0`**, passed to
  `stepLeader.spec` / `stepFollower.spec`, whose transfer branches and the `MsgAppResp` case's
  `From == leadTransferee` branch (`raft.go:1588-1590`; `From ≠ 0`, so `lt ≠ 0`) discharge
  `sendTimeoutNow`'s and `send`'s premises. `MsgHup`, `MsgBeat`, `MsgCheckQuorum`, `MsgProp`,
  `MsgUnreachable` and the acknowledgements never queue a `MsgTimeoutNow`, so the tick specs
  (`raft__tickElection`, `raft__tickHeartbeat`, which call `raft.Step.spec` with `MsgHup`/`MsgBeat`)
  discharge it vacuously and their text does not change;
- `raft.Step.tracedTriple` discharges the transfer premise by `StepEndTy` and the `lt` premise by a new
  premise `m.Type' = MsgAppResp → s.lt = W64 0`, which `run`'s `recvc` arm, `RawNode.Step.traced` and
  the traced `RawNode.Advance` (a leader's self `MsgAppResp`) read from `rnTrace` 1(b)'s `TrScope`; the
  other traced callers step no `MsgAppResp`. Every untraced caller of `raft.Step.spec` has
  `s.gh.tr = none`.
Files: `Spec/go_etcd_io/raft/v3/{raft__send,raft__sendTimeoutNow,raft__Step,stepLeader,stepFollower}.lean`
and their proofs, `InvRaftPhys.lean`, `TracedRaftStepBundle.lean`, and the callers of `raft.Step.spec`
(each untraced: the extra premises by `s.gh.tr = none`). **Lands whole in step 3, with clause 1(b)
(revision 3, N3; corrected from the review's split).** The review proposed keeping in step 2 what needs
no `lt` (`raft.send.spec`'s premise, `sendTimeoutNow`'s, the `MsgTransferLeader` premise, `XfOk`'s
clause). That does not build either: `sendTimeoutNow` is `r.send(&pb.Message{…, Type: MsgTimeoutNow})`
(`raft.go:2058-2060`), so `raft.send.spec`'s strengthened premise makes `raft.sendTimeoutNow.spec`'s
proof need its premise `s.gh.tr = none`, and `stepLeader`'s proof can discharge that at the
`MsgAppResp` call (`raft.go:1590`) only from `lt = 0` (`From == leadTransferee`, `From ≠ 0`). So the
`send` premise, `sendTimeoutNow`'s, the `MsgTransferLeader` premise, the `lt` premise and `XfOk`'s
clause are one change, and it lands where `lt = 0` has a source: step 3, beside 1(b). Nothing in step 2
reads the physical half (`OutTyStep` is about the abstract outbox; the physical half is read by
`acceptReady`'s `TrSent`, which is step 3's too).

### 3.7 The booted flag (29n finding 2)

The capability's flag `b` (under `∃ b` in `rnTrace`): `StartNode` returns it unset; the `Ready` line
(`trCap_fire_ready`), a receive line (`trCap_fire_recv`) and a `BecomeCandidate` (`trCap_fire_any`)
set it. `acceptReady` (and the traced `RawNode.Ready`, off `run`'s path) is the only function that
moves `rs.delivered`, and it fires the `Ready` line before returning, so clause 1(a) is established
there. **Kept by every step only because the bundle says so** (revision 3, N1): "flags only go up" is
true of the ghost state but not of the statements, which handed the capability back as `∃ bt'` and
so forgot it (the flag lives in an exclusive `simBoot tn id b o` inside `trCapB`,
`TraceSimGhost.lean:256`, with no persistent record). The bundle's end resource now gives
`⌜bt = true → bt' = true⌝` (§3.6), and every traced triple that steps passes it on. The `confc` arm
reads it. Q19 (a) lets the bundle and the ticks run at either flag.

---

## 4. `stepBundle_traced.statement`'s premises (slice 30c's list) and where `run` gets each

`run` calls `raft.Step.traced` from the `recvc` and `propc` arms, from `RawNode.Tick.traced`
(`MsgHup`, `MsgBeat`), and from the traced `RawNode.Advance` (self responses, acknowledgements).

| Premise | Discharged by | From where |
|---|---|---|
| `s.gh.tr = some γd` | `ownRawNode`'s trace field at a traced cluster | `cluster_alloc_traced` → `StartNode` |
| `s.prevote = false`, `s.cq = false` | `rnTrace`'s scope; `r.[raft,"checkQuorum"] ↦□ false` with `ownRaftPhysC_cq` | `startTrace`'s `TracedConfigOk` |
| `StepEndTy m.Type' ∨ AckTy m.Type'` | `recvc`: `netP`'s gated `TrNetTy` (§3.6) or `MsgUnreachable`/`MsgHup`; `propc`: `MsgProp`; ticks: `MsgHup`/`MsgBeat`; `Advance`: self responses (`TrNetTy`) or `AckTy` | **G1** for the network case |
| `NStateWf s` | `ownRawNode`'s `%Hwf` | — |
| local types at term 0 | the messages' constructors (`hupSt`, `propMsgM`, `ReportUnreachable`'s literal, raft's `tick*`, `newStorageApplyRespMsg`) | — |
| `MsgStorageAppendResp → Term ≤ s.term` | `raft.Step.spec`'s own premise, which `RawNode.Advance` supplies | — |
| a traced message to `id` | `NetMsgOk`'s `To = id` | `netP` |
| `s.term + 1`, `m.Term` below `traceNumBound` | the ceiling `rs.tc` (`RNPv`), bounded by the budget (§3.2); the message's by `termLB` in `netP` | `budgetInv` |
| `MsgTrOk` | `isRaftMsg_trRecv` (via `netP`'s `isMessage`/`isMessageC`) | the sender's `isRaftMsg` |
| the receipts' fit | the cluster's `readyFits` | `cluster_alloc_traced` |
| no learners | `rnTrace`'s scope (`c.learners = ∅`) | `startTrace` |
| `domSet s.progress ⊆ voters ∪ learners` | `ownRaftPhysC_dom` | — |
| not a pre-candidate | `ownRaftPhysC_precand` with `prevote = false` | — |
| `TrRecvShape` | `isRaftMsg_trRecv` (`SentMsgShape`, `Msg.TrOk`'s heartbeat clauses, Q18/Q28 (c)) | the sender's `isRaftMsg` |
| a proposal's batch non-empty, of normal entries | `propP` (one normal entry); `fwdP`'s gated clause | **G2** for the forwarded case |
| `StepNodeOk`: `PrvalsOk s`, `domSet s.prvals = domSet s.progress` | `ownRaftPhysC_prvals_ok`, `ownTrackerC_prvals_dom` | — |
| `StepNodeOk`: `MsgAppResp → m.From' ∈ domSet s.progress` | `recvc`'s guard (`r.trk.Progress[m.From] == nil` → drop), read with `ownTrackerC_progress_map` | — |
| the recv token `recvTokOf` | `netP`'s gated token (from `stepIn_intro`'s `trTok`); self responses: `pendingRel`'s `selfTok` | the sender's `acceptReady`, through `rtkInv` and the driver |
| (`raft.Step.tracedTriple`) `MsgStorageAppendResp → sn = none`; `MsgStorageApplyResp → ents ≠ [] → c.autoLeave = false` | `sn` is the `Ready`'s snapshot, which exists only after a stepped `MsgSnap`: **no `MsgSnap` is ever stepped at a traced node** (revision 3, S6: `netP`'s gated `TrNetTy` excludes it at `recvc`, and no other arm steps one; not `TrNoSnap`, which is about log compaction at the sender); no automatic leave: `rnTrace` 1(d) (G3 (b), §3.4 item 4) | `netP`'s gate (§3.2 item 5); G3 |
| (revision 2, A2's physical half; revision 3, S3) `m.Type' = MsgAppResp → s.lt = W64 0` | `rnTrace` 1(b)'s `TrScope` | §3.6; lands in step 3 (N3) |

Every row but G1, G2 (and G3 behind one of them) cites a fact that exists today; G1 and G2 are
§3.6's `OutTyStep` and physical half, G3 §3.4 item 4.

---

## 5. Bootstrap

### 5.1 What raft logs in `StartNode` (A7's check)

`setupNode` runs `NewRawNode` (`newRaft`), then `RawNode.Bootstrap`, then `go n.run()`. On empty
storage it logs, per voter, `|C| + 4` lines, `BootEvAt C i k` at position `k`:

| Position | Line | Logged by |
|---|---|---|
| 0 | `InitState` (term 0) | `newRaft`'s `traceInitState` |
| 1 | `ApplyConfChange` (term 0, empty `newconf`) | `newRaft`'s `switchToConfig` from the empty `ConfState` |
| 2 | `BecomeFollower` (term 0) | `newRaft`'s `becomeFollower(r.Term, None)` |
| 3 | `BecomeFollower` (term 1) | `Bootstrap`'s `becomeFollower(1, None)` |
| `k + 4`, for `k < |C|` | `ApplyConfChange` (term 1, `newconf` a permutation of the first `k + 1` voters, commit and log `|C|`) | `Bootstrap`'s `applyConfChange` per peer, through `switchToConfig` |

All are logged while unbooted, through `trCap_fire_boot` (premise `BootNext C id o e`, A7). The
segments clause `BootSegs C L` in `simInv` is kept (A7, proved).

### 5.2 The traced constructors (not yet; statements to write; S4)

Notation: `cC` is the voters' configuration (`(elements cC.incoming).Perm vs`, `cC.outgoing = ∅`), what
the capability is stated at; raft's own configuration `c` is empty at positions 0-2 and grows at
positions `k + 4`; `raft.becomeFollower.traced` keeps them apart (`hcC : b = true → cC = c`,
`TracedHooks.lean:417-421`). The phase `Φvs C _ _ := C = vs` fixes the capability's `C` to the caller's
voters (`startTrace_trCapB` needs `Φ vs …` initially; `tn.voters = vs`).

- **`newRaft.tracedSpec`** (`newRaft.spec` today sets `tr := none`):
  - pre: `newRaft.spec`'s pre with `startTrace γ vs cv` and `nodeBoot γ N vs ctxs cv.ID'`;
  - post: `ownRaftPhys` at raft's `c` with `s.gh.tr = some γd`, and
    `trCapB (some γd) γ.raftNames r cv.ID' cC false Φvs Λ2` with
    `Λ2 o := ∃ x, o = some x ∧ BootEvAt vs cv.ID' 2 x`;
  - untraced: today's spec.
  - Proved from `startTrace_trCapB` (A4, proved, at `cC` with `Λ := fun o => o = none`) and the gates:
    `trCapB_hookGate_init` gives position 0; `traceConfChangeEvent.spec` over `RaftReadLend` with
    `trCapB_hookGate_ccBoot` gives 1; `raft.becomeFollower.traced` at `b = false` gives 2. Each gate's
    `BootNext vs id o e` premise comes from the previous `Λ` and `Φvs` (which puts `C = vs`).
- **`RawNode.Bootstrap`'s traced spec**:
  - pre: the capability unbooted at `cC`, `Φvs`, `Λ2`; `bootMarshal` (Q32);
  - post: unbooted at `Λend o := ∃ x, o = some x ∧ BootEvAt vs id (vs.length + 3) x`.
  - Proved from `raft.becomeFollower.traced` (3) and, per peer, the traced `raft.applyConfChange` →
    `switchToConfig` at a follower (`trCapB_hookGate_ccBoot`, positions `k + 4`). No leader case.
- **`NewRawNode`/`setupNode` traced**: thread these. After `Bootstrap`, `simIdle_boot` (slice 21; on
  branch `trace-check-a8` it takes `id ∈ C`, which `Φvs` and the voter's `nodeBoot` give) gives the
  phase `SimIdle C s`. `setupNode` mints `bootDone tn id` by `trCapB_bootDone` (A8.2) at
  `Λend`: its `hΛ` holds since `Φvs C _ _` gives `C = vs`, so `Λend o` is `BootEvAt C id (C.length + 3)`.
  It then packs `rnTrace` (weakening `Λend` to the default `Λ`, the phase `Φvs` to `SimIdle`) with:
  - **`TrNoSnap` (revision 2, A4; L5 closed)**, in its update form
    `TrNoSnap tr ls := □ (⌜tr ≠ none⌝ -∗ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False)`
    (`TracedSend.lean`; `trNoSnap_traced` concludes `… -∗ |={⊤}=> False`; `trNoSnap_none`,
    `trNoSnap_congr`, `rnTrace_congr` keep their proofs). Built here at the fresh log state: its
    `prev.index` is `0` (a fresh `MemoryStorage`'s `FirstIndex` is `1`), refuting the first disjunct
    purely; for the second, `storPast st 1` is `∃ n ≥ 1, storCompacted st n.toNat`, and the client's
    `isStorage γ K st` (persistent, captured by the wand) has `"#Hbound" : □ (∀ c, storCompacted st c
    ={⊤}=∗ storBnd γ K c)` (`InvStorage.lean:282`), whose gated conjunct `⌜c = 0 ∨ Cluster.trace γ =
    none⌝` (Q6 item 8) refutes `c ≥ 1` at a traced cluster. It is built from the client's contract
    before `storBnd_raftBnd` (`StartNode.lean:107`) converts it to raft's `raftBnd`, so `raftBnd` needs
    no gate (the conversion drops the conjunct: one more `-` in its `icases`). The two uses
    (`raft__maybeSendAppend.lean:121-124, 431-434`) are WP steps of `raft.maybeSendAppend.spec`'s proof,
    a plain triple at `⊤` with no invariant open: `iapply trNoSnap_traced …` becomes
    `imod (trNoSnap_traced …) with []`. The other files mentioning `TrNoSnap` (25 in all) pass it by
    name: no statement changes.
  - **1(b)'s `TrScope`** (`lt = 0`, no pending read, the outbox empty) and **1(d)** (after the three
    `AddNode`s, `autoLeave = false`; `outgoing = ∅` is `trCapB`'s) hold of the fresh node; 1(a)
    (nothing delivered) and 1(c) (a follower) trivially; 1(e), lemma (ii)'s `applied ≤ capplied`, at
    `0 ≤ 0` (`Bootstrap` commits the bootstrap log but applies nothing; revision 3: the node is
    dynamic, `StartNode.lean:319`).
  - The node's escrow `rtkInv` (§3.2, 2.), with `al` and `dep` at `0` and `np` given to `run`.
- **`StartNode.gatedSpec`** (A8.3) from `setupNode` and `run`'s spawn (`node.run` at a traced node: §9's
  order, `node.run.gated_of` then the dropped premise).

### 5.3 Amendment A8 (Q36 (a), Q37 (a), decided by the coordinator): as landed

**Revision 3: the statements as frozen** (tag `trace-check-frozen-a8`, merged into `trace-check` at
`0eb3030a12`; branch `trace-check-a8`, `84dd5b2e36`..`65a42909a1`; reviews `a8-r1.md`, no first-tier
finding, and `a8-r2.md`; `notes/decisions.md`, "Amendment A8 (Q36, Q37)"). Revisions 1-2 gave the
design's statements (a ghost map for the witnesses, `bootInit` kept beside an equation); the
implementation departed from both, and this section now states what landed. Nothing below is to do
but the minting at the end of `setupNode` (§5.2), which waits on the traced `newRaft`/`Bootstrap`.

**A8.1: `simInit` (Q36 (a)).** `TraceSimGhost.lean`.
- `simInit C`'s servers: `s := fun i => if i ∈ confAbs C then { v with durable := … } else bootJunk`
  (`TraceSimGhost.lean:168`); `bootJunk` moved there from `TraceSimEnd.lean` (:153), body unchanged.
- `simInit_s_voter : i ∈ confAbs C → (simInit C).s i = { v with … }` and
  `simInit_s_nonvoter : i ∉ confAbs C → (simInit C).s i = bootJunk` (:182, :196).
- **`bootInit` is deleted** (review a8-r1: raft's `InvBoot.bootInit` has the name), with
  `bootInit_ne_simInit`, `MainSim.lean`'s `not_bootFacts` (both false now) and the unused
  `simInv_end_boot`. A7's `newTrace_bootInit` is **`newTrace_simInit`** (`TraceSimEnd.lean:123`):
  ```lean
  theorem newTrace_simInit (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hC0 : C ≠ [])
      (hCl : C.length < 2 ^ 40) (hrun : SimRun C L σ) (hev : SimEvents C.length L) (hseg : BootSegs C L)
      (hdone : ∀ i ∈ C, BootDone C L i) :
      ∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.server = confAbs C ∧ t.initSrv = confAbs C ∧
        t.init = simInit C
  ```
  and `bootFacts_of_bootDone` (`MainSim.lean:88`) states positively that complete segments give
  `BootFacts`.
- The readers that stated a voter's fact of every id gained a membership premise (`simInit_log`,
  `srvFacts_simInit`: `i ∈ confAbs C` / `j ∈ C`; `simIdle_boot`: `id ∈ C`; every caller has it); the
  others split on the two cases, the fact holding of `bootJunk` too. **B1.4 met**: every reader under
  `tracecheck_Events_traceAccepts` (`TraceSimRun`, `TraceSimMatch`, `MainSim`, `TracedNodeBoot`) was
  re-proved in that landing or compiled unchanged, none as a `sorry`.
- Argument (unchanged): `newTraceWith` builds a non-server's state from the trace's first line, a
  voter's `InitState` (term 0, a follower, empty), which is `bootJunk`; every reader of `simInit`
  reads voters' servers.

**A8.2: the completion witness (Q37 (a)), a mono list.** `TraceSimGhost.lean`, `TraceSimBootSeg.lean`,
`TracedCap.lean`, `TracedHooksGlobal.lean`.
- `structure TraceNames` gains `dn : GName` (`TraceSimGhost.lean:121`).
- `BootDone C L i := (bootSeg L i).length = C.length + 4` (:307).
- **The witness** (:314), persistent (`bootDone_persistent`):
  ```lean
  def bootDone (tn : TraceNames) (i : w64) : IProp GF := iprop(∃ k, monoListIdxOwn tn.dn k i)
  ```
- **`simInv C tn Fx`** gains `∃ Dn : List w64`, the authority `monoListAuthOwn tn.dn 1 Dn`, and the
  pure clause `∀ i ∈ Dn, BootDone C L i` (last).
- **Why a mono list, not the design's ghost map**: a ghost map's authority cannot hand out an element
  for a key already present, so a second minting for one node (the law applied twice, or by two
  callers) would need a premise the capability does not carry; a mono list's authority gives a
  persistent index witness of any member, and appending a duplicate is harmless, so the law appends
  `id` unconditionally.
- Kept by every law that closes `simInv` through `bootDone_snoc` (`TraceSimBootSeg.lean:283`:
  `BootSegs C (L ++ [e]) → BootDone C L i → BootDone C (L ++ [e]) i`) and its list form `bootDn_snoc`
  (:352): the fire laws `trCap_fire`, `_recv`, `_ready`, `_boot`, `_bf`, `_booted` (`_any` and
  `trCap_fireN` through them), and `trCapB_perm` (`Dn` unchanged). Position uniqueness is the
  existing `bootEvAt_unique` (`TraceSimBootSeg.lean:218`).
- `Cluster.traceSimInv_alloc` (`TracedApiDraft.lean:176`) and `Cluster.traceSim_alloc`
  (`TracedNodeApi.lean:133`) take `monoListAuthOwn tn.dn 1 ([] : List w64)`, which `traceNames_alloc`
  allocates.
- **The law** (`TracedCap.lean:1295`, proved as `trCapB_bootDone` in `TracedHooksGlobal.lean:1445`):
  ```lean
  abbrev trCapB_bootDone.statement : Prop :=
    ∀ (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
      (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) (E : CoPset),
    ↑(simNS γ) ⊆ E →
    (∀ C cs P o, Φ C cs P → Λ o → ∃ x, o = some x ∧ BootEvAt C id (C.length + 3) x) →
    trCapB (GF := GF) (some γd) γ r id c false Φ Λ ⊢
      |={E}=> (trCapB (some γd) γ r id c false Φ Λ ∗ ∃ tn, traceDir γd tn ∗ bootDone tn id)
  ```
  Argument: the flag unset, the node's events are all bootstrap-named, so its segment is all of them,
  `LastOf` making `o` the last; `BootSegs` puts it at the segment's last position, `hΛ` at `|C| + 3`;
  `bootEvAt_unique` makes the length `|C| + 4` (`bootDone_of_last`); append `id` to `Dn` and take the
  index witness.

**A8.3: `StartNode` returns the witness.**
- `TracedApiDraft.lean:88`: `startDoneB γ id := match Cluster.trace γ with | none => True | some γd =>
  ∃ tn, traceDir γd tn ∗ bootDone tn id`.
- `StartNode.gatedSpec`'s post gains `startDoneB γ cv.ID'` after `peers ↦*{dq} pv`.
- `TracedNodeApi.lean`: `StartNode.tracedSpec` has no parameter, its post the sealed
  `startDone γ cv.ID'` (`@[no_expose]`, :81, persistent), equal to `startDoneB` (`startDone_eq`,
  `TracedNodeApiBridge.lean:39`); `StartNode.tracedSpec_of_gated` lost its parameter.

**A8.4: the end law** (`TracedNodeApi.lean:186`, an API law; replaces the hypothesis `BootEnd D`;
stated over what the client holds, S3):
```lean
theorem Cluster.traceSim_bootEnd (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (γd : GName) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E)
    (htr : Cluster.trace γ = some γd) (hne : vs ≠ []) (hlen : vs.length < 2 ^ 40) :
    (nodeBoot γ N vs ctxs id ∗ traceDir γd tn ∗ Cluster.traceSim γ vs tn ∗
        □ ([∗list] i ∈ vs, startDone γ i) ∗ traceAuth tn.tr L : IProp GF) ={E}=∗
      traceAuth tn.tr L ∗ ⌜∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.init = simInit vs ∧
        t.server = confAbs vs ∧ t.initSrv = confAbs vs⌝
```
Proved by `startDones_bootDones` (:155: unsealing `startDone`, `traceDir_agree` making each one's `tn`
the given one), then `simInv_end_bootDone` (`TraceSimEnd.lean:194`: each `bootDone tn i` is a member of
`Dn`, so `BootDone vs L i`) and `newTrace_simInit`. `HarnessEnd.lean`: `BootEnd D` is now the theorem
`bootEnd`; `runOk_at_end` and `runOver_intro` take `γd`, `htr`, `traceDir γd tn` and
`□ [∗list] i ∈ vs, startDone γ i` in place of `D`/`HD`, and `hne`/`hlen`, which the harness has
(`vs = [1,2,3]`).

No change to `trCap_fire_boot`, `BootSegs`, `BootNext`, `trCapB`, or any other law's statement (their
proofs add one conjunct each). A8 is frozen (`trace-check-frozen-a8`).

---

## 6. Q33, Q34, Q35, and what the closed theorem rests on

**Q33 (`strconv.Itoa`).** Perennial translates `strconv` with bodies only for `ParseUint` and its
errors; `Itoa` is names-only. This repository already has `Spec/strconv/Itoa.lean` and
`axiom strconv.Itoa.wp_proof` (`Proof/strconv/Itoa.lean`, in `etc/tcb-baseline.txt`, K4's), and raft's
own linked results already rest on it (`etc/tcb-collections/raft.txt`). The proposer uses it.
`notes/perennial-changes.md`'s "Workaround here: none yet" is stale; the proposed Perennial change
(translate `Itoa`/`FormatInt` and prove the spec) stands.

**What the closed theorem rests on once `RunConcurrent` is proved** (S1; all existing; none new):
- **Raft's node API path**: the baseline of `etc/tcb-collections/raft.txt`, fifteen axioms of this
  repository: `DescribeConfChange.wp_proof`, `ccDecodeV2_nil`, `fmt.Errorf.wp_proof`,
  `proto.CloneConfState.wp_proof`, `proto.CloneEntry.wp_proof`, `proto.CloneSnapshot.wp_proof`,
  `proto.EqualConfState.wp_proof`, `proto.MarshalConfChange.wp_proof`,
  `proto.MarshalConfChangeV2.wp_proof`, `proto.SizeEntry.wp_proof`, `proto.UnmarshalConfChange.wp_proof`,
  `proto.UnmarshalConfChangeV2.wp_proof`, `raftpb.ConfChangeType.String.wp_proof`,
  `strconv.FormatUint.wp_proof`, `strconv.Itoa.wp_proof` (kv's, kvreconf's and kvdurable's collections
  have the same fifteen). It is an upper bound: the node functions the harness reaches may rest on
  fewer; the collection's `--check --update` after the proof records the exact set.
- **The harness's own calls**: `proto.ClonePb.wp_proof` (`proto.Clone` of a message, at `pbMessage`,
  whose decoder `msgDecode` is an `opaque`, not an axiom; the module moves to raft's tree, B4, which
  changes no axiom); `proto.UnmarshalConfChange.wp_proof`, `proto.UnmarshalConfChangeV2.wp_proof`
  (the `ConfChangeV2` arm, A6), `ccDecodeV2_nil` (an empty `ConfChangeV2` decodes) and
  `strconv.Itoa.wp_proof` (all already above).
- **Perennial's trusted specs**: `time.Now.wp_proof` (`Perennial/Proof/time/Now.lean:24`); not a line of a
  collection's baseline (they list this repository's axioms), but in `#print axioms`, as for
  `etcd_putget_safe`. `time.NewTicker`, `Sleep`, `Time.Add`, `context.WithTimeout` are proved in Perennial.
- **The package initializers' trust-boundary axioms** (`Init.lean`, generated), as today's
  `raft_tracecheck_safe_of`.

So the tracecheck collection's baseline gains about sixteen `axiom` lines when `RunConcurrent` is
proved: an update of the collection, recorded then, not a trust-base change (each is in
`etc/tcb-baseline.txt` today).

**Q34 (the network's wait group: several adders, unbounded).** A harness-local idiom over the raw
`WaitGroup` specs, backed by thread tokens (CLAUDE.md "Bounds"; Perennial's `tokJoin` is the model).
File `Proof/.../tracecheck/NetJoin.lean`, under `[ThreadBoundLe GF (2 ^ 31)]`.
- **Names**: `γ.wg : WaitGroupNames`, `γ.dep` (the slots' token count), `γ.ad` (the adders' fraction).
- **Invariant**: `njInv γ := ∃ ctr j, ownWaitGroup γ.wg ctr ∗ threadToks j ∗ ownTokAuth γ.dep j ∗ ⌜sint.Z ctr = j⌝ ∗ (ownWaitGroupWaiters γ.wg 0 ∨ dghostVar γ.ad (DFrac.own 1) ())`.
  `isNetJoin N wg γ := isWaitGroup wg γ.wg (N.@"wg") ∗ inv (N.@"inv") (njInv γ)` (**no pure bound**:
  revision 0 carried `⌜threadBound GF ≤ 2^31⌝`; the instance replaces it).
- **Rights**: `njAdder q := dghostVar γ.ad (DFrac.own q) () ∗ isNetJoin` (fractional). `njDone := ownToks γ.dep 1 ∗ isNetJoin`.
- **Laws**: `nj_init` (from a fresh wait group, `njAdder 1`); `njAdder_split`;
  `netJoin.wp_Add : {njAdder q ∗ threadTok} wg.Add(1) {njAdder q ∗ njDone}` (open `njInv` at `⊤`; an
  adder with `q > 0` refutes the right disjunct, so `ownWaitGroupWaiters 0` is there for `Add`'s
  `oldc = 0` case and goes back; the token is deposited, `ctr + 1 = j + 1`);
  `netJoin.wp_Done : {njDone} wg.Done() {threadTok}`; `njClose : njAdder 1 ={⊤}=∗ ownWaitGroupWaiters γ.wg 0`;
  `netJoin.wp_Wait` (by `alloc_wait_token` then the raw `Wait`, as `tokJoin.WaitGroup.wp_Wait_of`).
- **Thread tokens** (revision 2, B5): `RunConcurrent` forks each `app` by `wp_fork_tok_body`
  (`Perennial/GooseLang/Lifting.lean`), handing it the fork's fresh `threadTok`; `app`'s loop invariant
  holds one token; it deposits it at each `Add` (`netJoin.wp_Add`), the `go` gives it a fresh one
  (`wp_fork_tok_self`), and the message goroutine ends with the token `netJoin.wp_Done` hands back;
  `app` returns its token at `c.stop`. The other goroutines `RunConcurrent` forks use `wp_fork`.
- `etc/bounds-allow.txt` lists the idiom's own matches (it is the owner).
- **Perennial**: the general shared-adder join is recorded in `notes/perennial-changes.md` (S7 part 2).
- The same file gives `join3` for `drivers.Add(3)` (three `ownDone`s from one raw `Add(3)` with
  `oldc = 0`; the `WaitGroupJoin` argument at delta 3).

**The thread bound, end to end (F1, checked).**
1. `init_adequate` (`etcdstart/Adequacy.lean:111-119`) runs `goose_adequacy (n + 1) (n + 2)`, so the
   hypothesis of `Hprog` gives `HN : receiptBound GF = n + 1` and `HT : threadBound GF = n + 2`.
2. `tracecheck_adequate_of` with `Hn : n + 2 ≤ 2^31`: `ThreadBoundLe tcGF (2^31)` from `HT` and `Hn`
   (`ThreadBoundLe.of_eq`, `weaken`, `Perennial/ProgramLogic/Bounds.lean`); `receiptBound tcGF + 3 =
   n + 4 ≤ 2^31 + 2 ≤ 2^61` from `HN`.
3. `Main.spec` and `RunConcurrent.spec` take the instance; the corollary (§1.3) takes it directly.
4. `netJoin.wp_Add`: the adder holds `threadTok` and the invariant `threadToks j`, so
   `threadToks_add_one_lt` (`Perennial/GooseLang/Threads.lean:433`) gives `j + 1 < threadBound GF ≤ 2^31`
   (`ThreadBoundLe.le`). `WaitGroup.Add.spec` (`Perennial/Spec/sync/WaitGroup__Add.lean`) needs
   `0 ≤ sint.Z oldc + sint.Z (W32 1) < 2^31` with `oldc` the `w32` counter, `sint.Z oldc = j`
   (representable: `0 ≤ j < 2^31`): `0 ≤ j + 1 < 2^31`. Holds.
5. `join3` and `apps` (`WaitGroupJoin`) add constants (3), within the same bound.

**Q35 (`Workload`'s `Tick > 0`).** Taken, (a): §2.1. Not in the closed statement (§1.3 is at
`defaultCConfig`).

---

## 7. The chain, every statement: proved from, and why that suffices

★ = not proved today. † = flagged in §9. "Re-opened" = proved today, its statement unchanged, its proof
redone for a changed sealed body (§3.3). Revision 2: rows re-checked against A1-A6 and B1-B7; changed
rows say so. Revision 3: rows re-checked against N1-N3 and S1-S6; changed or new rows say "rev. 3".

| Statement | Proved from (callee statements) | Why it suffices |
|---|---|---|
| `raft_tracecheck_safe` (§1.2) | `tracecheck_adequate_of` (new binders; `Hn : n + 2 ≤ 2^31`), `tcMainSpec` | adequacy turns `Main`'s spec at every `HeapGS` into the operational statement; the instance and `Hbound` from `HT`/`HN` (§6); `Hprem` at each `hG`, as putget |
| `raft_tracecheck_accepts` (§1.3) | `RunConcurrent.spec` at `defaultCConfig` (`Workload` by `decide`) under the instance, `tracecheck_Events_traceAccepts` | the post `runOver c` is the latter's precondition |
| `tcMainSpec` / `Main.spec` ★(premises) | `Main.wp_proof` (proved) with `RunConcurrent.spec` and the checker's Link | unchanged proof, plus passing the instance and `premises boot` |
| `RunConcurrent.spec` ★ | §2.2's calls: `harness_alloc`, `tcOpsInv` (with its requested-entries clause, A6)/`confPolicy_alloc`/`tcSnapsInv`, the storage with `storBnd_zero` (B2), `startTraceC_intro`, `StartNode.tracedSpec`, `sync.join`, `join3`, `netJoin`, `wp_fork_tok_body` for `app` (B5), `app`/`send`, `node.Stop.spec`, `time.Now`, `Time.Add`, `runOver_intro` (with `bootEnd`, a theorem on `trace-check-a8`) | allocation gives each voter's `startTraceC`; the three `startDone`s with `traceDir` and `Cluster.traceSim` give `BootFacts`; `runOver_intro` composes |
| `app` ★ (harness-local: `isNode`, driver state, `nodeRunning 1`, `njAdder ⅓`, `ownDone apps …`, a `threadTok`) | `time.NewTicker`, `node.Tick.spec`, `isReadyChan_recvAu.tracedSpec`, `handleReady`, `node.Advance.tracedSpec`, `proto.ClonePb.spec` at `pbMessage` (moved to raft's tree, B4), `send`, `wp_fork_tok_self` | loop invariant: the driver idle, `nodeRunning 1`, `njAdder ⅓`, one `threadTok` (B5). Each round: the claim (with its allocation bound, A1) at the receive, the tokens at `Advance`, one `send` per token |
| `handleReady` ★ | storage contract, `tcOps_emptyV2`/`tcOps_v1_boot` (`tcOpsInv`, `ownCommittedOps_lb_prefix`, `isCommittedLogLb_agree`; Probe A, P4), `proto.UnmarshalConfChange.spec`, `proto.UnmarshalConfChangeV2.spec`, `confPolicy_decide`, `committed_emptyV2_joint`, `confAt_valid`, **`Membership.applyChange_leaveJoint`** (new raft law, P1), `Membership.applyChange_addVoter`, `node.ApplyConfChange.spec`, `snapshotCert_made`, `snapMade_elem` with `tcSnapsInv` | **changed (A6; Probe A, P1, P4)**: both conf arms from client-visible facts only (§2.3); the snapshot branch refuted from `readySnap` |
| `Membership.applyChange_leaveJoint` ★ (Probe A, P1; raft API, `InvNode.lean` beside `applyChange_addVoter`) | `ApiImpl.memApply`, `ccApplyM_leaveJoint` (`ConfchangeApiImpl.lean:109`), `leaveJointM` at a valid joint state | the empty `ConfChangeV2` is the leave; no other law speaks of joint memberships |
| `send` ★ | `netJoin.wp_Add`, `wp_fork_tok_self`, `trTok_type`, `node.Step.tracedSpec`, `node.ReportUnreachable.spec`, `netJoin.wp_Done` | the token rides into the goroutine; `ReportSnapshot` dead by `trTok_type`; the goroutine ends with `wp_Done`'s thread token |
| `netJoin` laws, `join3` ★ | raw `WaitGroup.Add/Done/Wait`, `alloc_wait_token`, `threadToks_add_one_lt`, `ThreadBoundLe.le` | §6, end to end |
| `StartNode.tracedSpec` ★ (A8.3) | `StartNode.gatedSpec` (Draft, amended), `startTraceC_eq` | the Draft's over the sealed names (as today's `tracedSpec_of_gated`) |
| `StartNode.gatedSpec` ★ | `setupNode` traced, `node.run.gated_of` then `node.run.spec` (§9's order) | `setupNode` returns the node with `bootDone`, `rtkInv` and `runPre`; `go n.run()` |
| `setupNode`/`NewRawNode` traced ★ | `newRaft.tracedSpec`, `RawNode.Bootstrap` traced, `trCapB_bootDone`, `simIdle_boot` (with `id ∈ C`), the client's `isStorage` at the gated `storBnd` (for `TrNoSnap`, A4) | §5.2: `rnTrace` with 1(a)-(e), `TrNoSnap` in its update form, the escrow (L5 closed) |
| `newRaft.tracedSpec` ★ | `startTrace_trCapB` (proved, at `cC`), `trCapB_hookGate_init`/`_ccBoot` (proved), traced `traceConfChangeEvent.spec` ★ (`RaftReadLend`), `raft.becomeFollower.traced` (proved) | positions 0-2 by `BootNext` from each previous `Λ` and `Φvs` |
| `RawNode.Bootstrap` traced ★ | `raft.becomeFollower.traced`, `bootMarshal`, traced `raft.applyConfChange` ★ (follower, `_ccBoot`) | positions 3 to `|C| + 3` |
| `trCapB_bootDone` (A8.2) | `simInv`'s `Bt`/`LastOf`/`BootSegs`, `bootEvAt_unique`, `bootDone_of_last` | proved on `trace-check-a8` (§5.3) |
| `Cluster.traceSim_bootEnd` (A8.4) | `traceDir_agree`, `simInv`'s `Dn` clause, `Cluster.traceSimInv_bootEnd`, `simInv_end_bootDone`, `newTrace_simInit` | proved on `trace-check-a8` (§5.3) |
| `isReadyChan_recvAu.tracedSpec` ★ (revised) | `isReadyChan`'s protocol with `readyP` carrying the escrow element and `monoNatLb γn.al (j + 1)` (A1) | both are minted at `run`'s `readyc` commit (§3.2, 3.), in the `|={⊤}=>` prefix of its send AU (rev. 3, S1) |
| `handshake_send_au_fupd` ★ (rev. 3, S1; raft-internal, beside `handshake_send_au_upd`, `InvNodeChan.lean:1429`) | `handshake_send_au_upd`, `sendAu`'s leading `|={⊤,∅}=>` | the update at `⊤` runs before the handshake's `inv nroot` is opened, and only at the commit |
| `isReadyChan_recvAu` (untraced law) | re-opened: `readyP`'s gated element is dropped | holds for every `γ` |
| `node.Advance.tracedSpec` ★ (the one proof, A5) | `advInv` with `np` lent and the `SndPending` payload's allocation bound (§3.2, 4.), `rtkInv` | **changed (A1)**: `pend = false` at `run`'s side of the rendezvous in both orders; in `RcvPending` the driver's element gives `j < a`, in `SndPending` the payload's `monoNatLb γn.al (j + 1)` does, and `run` answers `monoNatLb γn.dep (j + 1)`; stale keys too; `ms = []` takes nothing |
| `node.Advance.spec` | **its instance** (`node.Advance.spec_of_traced`, `readyToksClaim_nil`); text unchanged, every `γ` (A5) | no second proof |
| `node.Step.tracedSpec` (corollary) | `stepIn_intro` (with `trTok`), `node.Step.spec` | — |
| `node.Step.spec` | proof unchanged (`stepWithWaitOption` passes `stepP`) | every `γ` |
| `stepIn_intro` (gains `trTok`) | re-opened: `ApiImpl.stepIn_intro_impl` splits on the trace | §3.2 items 5-6 |
| `trTok_type`, `trTok_untraced` | `trTok`'s body (`TrSent`) | — |
| the five refused `node.X.spec`s (§3.5) | their proofs plus the premise discharging `netP`'s/`stepP`'s untraced arm (`ProposeConfChange`: its internal `stepIn`) | untraced `netP`/`fwdP` unchanged |
| `node.run.gated_of` ★ (one spec at the end) | §3.2's arms: `raft.Step.traced` with `stepBundle_traced` (re-opened), `wp_rn_raft_Step_prop_traced` (re-opened), `RawNode.Tick.traced` (re-opened), `acceptReady.spec` (re-opened), `readyWithoutAccept.spec` (re-opened), traced `RawNode.Advance` ★ (`hAdv`), traced `raft.applyConfChange` ★ (`hCC`, follower case), lemmas (i), (ii), G3 (a), `getStatus`, `rtkInv` | the invariants of §3.2 (1.-6.) give each arm's premises (§4); the leader excluded at `confc` (§3.4 item 5); the `confc` arm's booted capability from 1(a), kept by the monotone flag (rev. 3, N1); the bounds by the budget. Stated only after L1, (i), (ii), G3 and `TrNoSnap`'s form are theorems (B1.5), so its hypotheses are `hAdv` and `hCC` only |
| traced `RawNode.Advance` ★ | `raft.Step.traced` (self responses: `TrNetTy`, `selfTok`), `stepBundle_traced` on `AckTy` (`.onA`, `stepBundle_traced_storAck`), `TrNoSnap` (update form: an `imod`), `rnTrace` 1(d) (the `autoLeave` premise) and 1(b) (`s.lt = 0` at a self `MsgAppResp`), `RawNode.Advance.spec`'s strengthened post (rev. 3, N2) | 28n's design; `stepsOnAdvance` holds exactly the self responses and the two acknowledgements (`rawnode.go:411-426`); re-establishes 1(e): the new `applied` is `rs.delivered.length ≤ ca = max rs.capplied rs.delivered.length`, installed by `advRS` |
| `RawNode.Advance.spec`'s post gains `rs.slent = none → rs.mode.isDyn = true → ca = max rs.capplied rs.delivered.length` (rev. 3, N2; re-proved, step 2) | `ownStepGhost_rinv` (`RInv.applied_cidx`, `StepRInv.lean:268`), `Hge`/`Hdlen`, the existing `%Hca` | `StepR.advance`'s `cidx := max r.cidx a` is the source; `node__run.lean`'s call names one more conjunct |
| traced `raft.applyConfChange` / `switchToConfig` ★ | `Changer` specs giving back the old maps, `traceConfChangeEvent.spec` over `RaftReadLend` ★, `trCapB_hookGate_applyCC` (proved, booted) / `_ccBoot` (unbooted) | follower case argued (29n); the leader excluded (§3.4 item 5); 1(d) kept by G3 (a) |
| `rnTrace`'s new clauses 1(a)-(e) ★ | established at `setupNode` (1(a) also at `acceptReady`/`RawNode.Ready.traced`); kept by the re-opened triples of §3.3, now including `RawNode.Step.traced`, `RawNode.Ready.traced`, `RawNode.ReportUnreachable.traced` (rev. 3, N3) | added after their facts (§9's order): 1(a) by the monotone flag (rev. 3, N1), 1(b) by `OutTyStep` (§3.6), 1(c) by lemma (i), 1(d) (`autoLeave = false` only, rev. 3, S5) by G3 (a), 1(e) by `RawNode.Advance`'s strengthened post |
| `OutTyStep` and the monotone flag in `stepBundle_traced.statement`'s `Gout` ★ (A2; rev. 3, N1) | each path's close (the 27 files of §3.6); for the broadcasting paths the strengthened `OutOk` and `outTyStep_of_outOk` (rev. 3, S2); `stepClose_anyB` with the flag | each path knows what it queued (the families record it in `OutOk`) and whether it logged a line |
| `OutOk`'s strengthened disjunct, `outOk_snoc`'s new premise, `outTyStep_of_outOk` ★ (rev. 3, S2) | the 8 `outOk_snoc` sites' message types; `lineF_untraced`'s new premise `¬ ReadIdle X` from its caller's pending read | L1 closed (§9) |
| the physical half: the traced premises of `raft.send.spec`, `raft.Step.spec` (`MsgTransferLeader`; `MsgAppResp → lt = 0`, rev. 3, S3), `raft.sendTimeoutNow.spec`; `XfOk`'s clause ★ (A2) | `stepLeader`/`stepFollower`'s transfer branches and `raft.go:1590`'s `From == leadTransferee`; `raft.Step.tracedTriple`'s `StepEndTy` and `MsgAppResp → s.lt = 0` (1(b)) | §3.6; lands whole in step 3 (rev. 3, N3) |
| G3 (a) ★ (A3; rev. 3, S4): (a1) the term logs' gated clause on non-empty conf entries; (a2) empty `ConfChangeV2`s | (a1) `cluster_alloc_traced`, the minting update's new premise from `raft.Step.spec`'s traced `MsgProp` premise (the automatic leave admitted); (a2) `isEntryR`'s `ev2Rec`, lemma (i), (a1), by induction on positions | §3.4 item 4; (a) no longer needs (b). One point to check at threading: `CfgAt` over the bootstrap prefix is simple |
| lemma (ii), `applied ≤ capplied` (dynamic) ★ (B3; rev. 3, N2) | `RawNode.Advance.spec`'s strengthened post at the traced `RawNode.Advance`; framed elsewhere | §3.4 item 3: the source is the installed configuration index, not the driver's view |
| `raft.Step.traced`, `stepBundle_traced` | proved (30c); re-opened for `OutTyStep` and the flag (step 2) and for the physical half's premises (step 3) | — |
| `TrNoSnap`'s update form (A4) | `trNoSnap_traced`'s new conclusion; `raft__maybeSendAppend.lean`'s two refutations by `imod` | §5.2 |
| `storBnd`'s gate; `storBnd_zero`, `storBnd_intro_untraced` (B2) | — | the three kv-family lemmas and `memStorage_isStorage` re-proved through them (§9, L3) |
| `trCapB_hookGate_applyCC`, `traceConfChangeEvent.tracedSpec_proof`, `startTrace_trCapB`, `cluster_alloc_traced`, `harness_alloc`, `Cluster.traceSim_alloc`/`_end`, `tracecheck_Events_traceAccepts`, the checker's Link, `confPolicy_alloc`/`_decide`, `snapshotCert_made`, `snapMade_elem` | proved | — |
| `runOver_intro`, `runOk_at_end` (`HarnessEnd`) | restated over `startDone` (S3); proofs: `Cluster.traceSim_bootEnd` in place of `HD` | — |
| the fire laws, `trCapB_perm`, `Cluster.traceSimInv_alloc` | re-opened for `simInv`'s `Dn` (A8.2) | statements unchanged |

---

## 8. The end-to-end probe (after review)

**The path, in the Go's order**: `StartNode`, `Ready`, `handleReady`, `Advance`, then `send`→`Step`.

The first `Ready` of a fresh voter hands out no message, so the concrete run that reaches a message:
`StartNode` ×3; voter 1's first `Ready` (the three bootstrap entries; `ApplyConfChange` ×3 through
`tcOps_v1_boot` and `confPolicy_decide`; `Advance` without using the claim's tokens: `ms = []`); ticks
until `tickElection` campaigns (`hup`: `applied = 3 ≥ |boot|`, §3.4); voter 1's second `Ready` with
`MsgVote` to 2 and 3 (key 1 of voter 1's escrow); `Advance`, giving `trTok` for each `MsgVote`;
`proto.Clone`; `send` → `node.Step` at voter 2; voter 2's `recvc` arm steps the `MsgVote` (`TrNetTy`)
and logs the receive line after voter 1's `Ready` line.

**Probe A (client glue, harness level; easy).** A Lean `example` over the client statements as
hypotheses:
- `harness_alloc`, `tcOpsInv` (with its requested-entries clause)/`confPolicy_alloc`/`tcSnapsInv`, the
  storage with `storBnd_zero`, then `startTraceC_intro`;
- `StartNode.tracedSpec` (A8.3, as on `trace-check-a8`) for one voter;
- the fork of `app` by `wp_fork_tok_body` (B5): `app`'s precondition with its `threadTok`;
- `isReadyChan_recvAu.tracedSpec` (revised), giving `readyGotT` with the claim on `ms`;
- `handleReady`'s refutation of a snapshot `Ready` (`snapshotCert_made`, `snapMade_elem`), and (A6)
  its `ConfChangeV2` arm: `tcOps_emptyV2` (was `tc_confShaped`), `proto.UnmarshalConfChangeV2.spec`
  without error, `committed_emptyV2_joint`, `Membership.applyChange_leaveJoint` (P1),
  `confPolicy_decide`, `node.ApplyConfChange.spec`'s premises;
- `node.Advance.tracedSpec`, giving `[∗list] q ∈ ms, trTok γ q.st`; and `node.Advance.spec_of_traced`
  (A5);
- for `q ∈ ms`: `netJoin.wp_Add` with the thread token, `wp_fork_tok_self`, `proto.ClonePb.spec` at
  `pbMessage` (imported from raft's tree, B4), `trTok_type`, then `stepIn_intro` (with `trTok`) and
  `node.Step.spec` at `q.msg.To'`, and `netJoin.wp_Done` giving the goroutine's token back;
- at the end, `bootEnd` (`Cluster.traceSim_bootEnd`) with the three `startDone`s and `traceDir`, then
  `runOver_intro`.

It checks that each post supplies the next pre: the claim's `ms` against `readyGot`'s `ms` and
`rd.Messages`; `ClonePb`'s `T.ro` from the `Ready`'s `msgOwn … (readyDq q.st)` and its `T.dec`/`eqv`
into `msgPtsC … ⟨…, []⟩` (S1's correction); `trTok` against `stepIn_intro`'s `st`; `app`'s token
through each round; the `ConfChangeV2` arm's `Membership.applyChange` from `m.isJoint`; `startDone`
into the end law.

**Probe B (node level; hard, chosen by its invariant).** The new invariant is the escrow `rtkInv` with
`run`'s lent `np` and the allocation bound (§3.2, 2.-4.), plus `stepP`'s gated token and type (§3.6).
Prove, for one node:
1. `run`'s `readyc` arm: the key allocated (`pend := true`, `np` in, `al` raised, its lower bound
   minted) and the element with the bound into `readyP`, in the `|={⊤}=>` prefix of the send AU
   through `handshake_send_au_fupd` (rev. 3, S1), checking that a `select` firing another case runs no
   prefix; then `acceptReady.spec` (its `"Htoks"`) and
   the deposit (`np` out, `pend := false`, the `readyTok`s into `trTok`-bodied slots).
2. The busy loop state with `np`.
3. The `advancec` rendezvous in both orders: `RcvPending` (the driver's commit with `np` in `advDep`,
   its element giving `j < a`), and **`SndPending` with the payload's `monoNatLb γn.al (j + 1)`** (A1),
   the driver's offer made while `pend = true` and its logical `SndPending` entered by `run` at the
   rendezvous (rev. 3, S1), `run`'s commit minting `monoNatLb γn.dep (j + 1)` and the driver's
   later swap with `pend = true` again for a newer key; yielding `node.Advance.tracedSpec`'s tokens; the
   same with the claim's left disjunct `ms = []` (`node.Advance.spec`'s instance), which must leave
   `run` with `np` and nothing else owed; and with a **stale** claim. Each opening of `rtkInv`
   (`rtkN := nroot.@"raft_rtk"`, rev. 3, S1) inside `advInv`'s AU at `⊤ ∖ ↑advN`.
4. At the receiver, `stepIn_intro`'s traced split into `netP`/`fwdP`, then the `recvc` arm through the
   guard to `raft.Step.traced` with `StepNodeOk` and the token.
5. (B3; reworded, rev. 3, N2) Lemma (ii)'s check: `RawNode.Advance`'s installed `ca` is at least the
   new `applied`, i.e. the strengthened post `ca = max rs.capplied rs.delivered.length` is provable at
   `RawNode__Advance.lean:2026` from `ownStepGhost_rinv`, and `advRS` then re-establishes `applied ≤
   capplied`. (Revision 2's wording, the driver's `ca` from `advanceP`, was false: that is the last
   applied conf index, `3` while `applied` is `4` at this run's second `Ready`.)
6. (rev. 3, N1) Clause 1(a) through a step: `raft.Step.traced` at a booted node (`bt = true`, after
   voter 1's first `Ready`) gives back `bt' = true` by the bundle's implication, so the `confc` arm after
   it still has a booted capability.

The riskiest piece: it checks that the instance at `ms = []` is provable at a traced node (F3, A5),
that the deposit is found in both orders (A1), and that `rnTrace` 1(b) with `XfOk`'s new clause gives
`TrSent` at `acceptReady` (G1's sender half, A2).

---

## 9. Links not argued, the order of work, and decisions

**Links I could not argue in full** (all raft-internal; none touches §1):
- **L1: closed (revision 3, S2).** The type list holds of the Go (§3.6) and the obligation is placed:
  `OutTyStep` in `stepBundle_traced.statement`'s `Gout`, each path proving it at its close, plus the
  physical half. Revision 2 left open whether a broadcasting path sees its queued messages' types at
  its close; it does, through the families' `OutOk`, which revision 3 strengthens to record
  `TrScope s → TrOutMsg x` per queued message (§3.6, "The carrier"). `StepEnd`'s `ReplSends` is not
  read.
- **L2 (§3.4), the leader exclusion.** Lemma (i) argued (`HupGuard` is exclusive,
  `SpecResults.lean:61-73`, so 1(c) follows at the close from `StepEnd`; review r3). Lemma (ii) with its
  source corrected (revision 3, N2: `RawNode.Advance.spec`'s strengthened post, proof sketched against
  the Lean). **G3** (a) in two parts (revision 3, S4): (a2), the empty `ConfChangeV2`, from the
  existing `ev2Rec`, with one point to check at threading (`CfgAt` over the bootstrap prefix is the
  fold from the simple base, so simple, whatever the recorded decisions); (a1), the non-empty conf
  entries, still needs the term logs' minting update located, with the code proofs that call it
  (`stepLeader`'s `MsgProp` branch, `becomeLeader`), which pass `raft.Step.spec`'s traced `MsgProp`
  premise down; listed at threading. Fallback: 29n's leader line lemma.
- **L3 (§3.5, F2, F3; revision 2, B2). The client call sites, counted** (by the Go call or the lemma
  applying the spec; `RaftWitness` excluded, it has its own raft; links that only pass `wp_node_X`
  through not counted):
  - `stepIn_intro` (`trTok`, F2): 4 sites (server `InvNet.lean`; kv `deliver.lean`; kvreconf and
    kvdurable `Cluster__step.lean`), each discharged by `trTok_untraced` with a fact it holds, kv's after
    `kvPeerOk` gains it (§3.1).
  - `ReadIndex`: 4 (server `NodeBridge.lean:684`; kv `KV__Read`; kvreconf, kvdurable `Replica__read`).
  - `TransferLeadership`: 3 (kv `KV__TransferLeadership`; kvreconf, kvdurable `Cluster__Disrupt`).
  - `ForgetLeader`: 2 (kvreconf, kvdurable `Cluster__Disrupt`).
  - `ReportSnapshot`: 6 (server `NodeBridge.lean:735`, `NetBridge.lean:69`; kvreconf, kvdurable
    `Cluster__step`, `Cluster__dropped`).
  - `ProposeConfChange`: 2 (kvreconf, kvdurable `Cluster__Reconfigure`); plus raft's own
    `node__ProposeConfChange.lean` (its internal `stepIn`).
  - **`storBnd` (B2, new)**: 4. Three client lemmas unfold it: kv's `kvJ_bnd`
    (`kv/KVStorageInstance.lean:273-275`), kvreconf's `kvrJ_bnd` (`kvreconf/KvrStorageApi.lean:274-276`),
    kvdurable's `kdJ_bnd` (`kvdurable/KdStorageApi.lean:147-149`); each is re-proved through the new
    exported `storBnd_intro_untraced : Cluster.trace γ = none → nodeAppliedLb γ K k -∗ ⌜c ≤ k⌝ -∗
    storBnd γ K c` (no unfold) and gains that premise, which its caller has from its cluster's
    `%Htr0` (kv: at its storage's construction, beside the allocation; to check at threading). The
    server reaches `storBnd` through raft's exported `memStorage_isStorage`, which gains the premise
    (Q6 item 8): its call `NodeStart.lean:322` discharges it from `srvClusterOk`. The harness uses
    `storBnd_zero : ⊢ storBnd γ K 0` (any `γ`).
  - `Advance`: **0** (F3, A5: `node.Advance.spec` keeps its text as the traced proof's instance).
  - Where the fact comes from: the server's `srvClusterOk` (`srvRaftLogInv`'s, read as
    `isRaftNodeIfc_of_isNode` does at `NodeBridge.lean:510`); kvreconf's and kvdurable's `isClusterC`
    `%Htr0` (their replica lemmas, `Replica__read`/`Replica__run`, take it from the cluster predicate if
    they hold it, else their replica predicate gains it: to check at threading); kv holds it only at
    allocation, so kv's `kvPeerOk` and its replica predicate (`isReplica`, for `KV__Read`,
    `KV__TransferLeadership`) gain it. In all, **about 25 call sites in 20 files**: the server 4 files
    (+ `NodeStart.lean`), kv 4 (+ `KVStorageInstance.lean`; + `Cluster.lean`'s and the replica's
    definitions), kvreconf 6 (+ `KvrStorageApi.lean`), kvdurable 6 (+ `KdStorageApi.lean`).
- L4 (revision 0's `threadBound ≤ 2^31`): closed by F1 (§6). **L5** (`TrNoSnap`'s source): closed by
  A4 (§5.2).

**The order of work (S5, S9; revision 2, B1): no `sorry` under an existing result, no new clause on a
proved theorem before its facts.** Each landing passes the acceptance test (`notes/trace-check-goal.md`).
1. **The gates and their client-side premises, one landing** (revision 1's steps 1 and 2 merged: the
   gated `netP`/`fwdP` break `ApiImpl.stepIn_intro_impl` and the local senders at a traced `γ` unless
   `stepIn_intro`'s premise and the refusals come with them). Each sealed definition changes as a gate
   whose `none` arm is today's body: `stepP` through `netP`/`fwdP`, `readyP` (the element and its
   allocation bound), `advInv`/`advDep`/`advRet`, `AdvReq`, `trTok`, `storBnd`; the escrow
   (`NodeNames`' `rtk`, `np`, `dep`, `al`; `rtkInv` at `nroot.@"raft_rtk"`, its slots `trTokR`-bodied
   over `γn.raft.reTrace`, in `isNodeChan`; revision 3, S1), and the lemma `handshake_send_au_fupd`
   (used by step 4's `readyc` arm). With
   them: `stepIn_intro`'s `trTok` premise and the five refusals, `storBnd_zero` and
   `storBnd_intro_untraced`, and **every L3 call site** (about 25), each discharged; `trTok_type`,
   `trTok_untraced`; `isReadyChan_recvAu.tracedSpec` and **`node.Advance.tracedSpec` as the one proof,
   `node.Advance.spec` its instance** (both use only the driver's side of the escrow, so they are
   provable for every `γ` before `run`'s traced arms exist); (Probe A, P1) the API law
   `Membership.applyChange_leaveJoint`, an addition that re-opens nothing. Every proof of today's untraced results
   has `γ.raft.reTrace = none` (the premise of `node.run.spec`, `StartNode.spec`, `RestartNode.spec`,
   or the client's fact) and is re-proved by rewriting the gate. No `rnTrace` clause, no `readyTok` body
   change.
2. **The facts the new clauses need, as theorems** (no existing statement changes but the raft-internal
   ones named; revision 3, N3: nothing here needs `lt = 0` or a new `rnTrace` clause):
   - `stepBundle_traced.statement`'s `Gout` with **`OutTyStep` and the monotone flag** (A2; N1), the 27
     path files and `TracedPin.lean`'s close helpers re-proved (§3.6); `stepClose_anyB` with the flag;
     the 4 consumers that pass `Gout` through (`TracedNodeRecv.lean`, `TracedRawNode.lean`,
     `TracedRawNodeRep.lean`, `InvRawnode.lean`) re-proved; `raft.Step.tracedTriple`'s post gains the
     two (a statement change of a raft-internal traced triple, its callers re-proved here);
   - **`OutOk` strengthened** (S2): `TracedPin.lean`'s `OutOk`, `outOk_snoc`, the new
     `outTyStep_of_outOk`; the 8 `outOk_snoc` sites; `lineF_untraced`'s premise `¬ ReadIdle X` (its one
     caller in `TracedRaftStepRecvLeadSend.lean`); `ReadIdle`/`TrScope`/`TrOutMsg`/`OutTyStep` defined
     in `StepGhostMode.lean`;
   - **G3 (a)** (S4): (a1)'s gated clause on the term logs with the minting update's premise
     (`cluster_alloc_traced` establishing it); (a2) as a lemma from `ev2Rec`; lemma (i) as a pure lemma
     over the committed log;
   - `TrNoSnap`'s update form (`trNoSnap_traced`, the two `imod`s);
   - **`RawNode.Advance.spec`'s strengthened post** (N2), re-proved in `RawNode__Advance.lean`; its
     caller `node__run.lean` names one more conjunct. A proved spec under closed results: re-proved, not
     `sorry`ed.
   What builds: every changed statement is raft-internal and traced, or `RawNode.Advance.spec`'s post
   (a conjunct added); every proof that consumes them is in the list. No `rnTrace` clause, no `lt`
   premise, no physical-half premise: `raft.Step.spec`, `raft.send.spec` and
   `raft.sendTimeoutNow.spec` keep their statements, so their untraced callers are untouched.
3. **`rnTrace`'s clauses 1(a)-(e), `readyTok`'s `TrSent` body and the physical half, one landing**
   (revision 3, N3: the physical half moved here whole, §3.6, since `sendTimeoutNow`'s `send` makes its
   premises need `lt = 0`, which only 1(b) supplies):
   - the physical half: `raft.send.spec`'s premise, `raft.sendTimeoutNow.spec`'s, `raft.Step.spec`'s
     `MsgTransferLeader` premise and its `MsgAppResp → s.gh.tr ≠ none → s.lt = W64 0` (S3),
     `stepLeader.spec`/`stepFollower.spec`, `XfOk`'s clause (`InvRaftPhys.lean`); every caller of
     `raft.Step.spec`, `raft.send.spec` and `raft.sendTimeoutNow.spec` re-proved (about 26 and 20
     files mention them: the untraced ones discharge the new premises by `s.gh.tr = none`, the tick
     specs' proofs and the other non-`MsgAppResp` callers vacuously by the message type);
     `raft.Step.tracedTriple` gains the premise `m.Type' = MsgAppResp → s.lt = W64 0`;
   - the clauses, with every triple they re-open re-proved from step 2's theorems (§3.3):
     `RawNode.Tick.traced`, `acceptReady.spec`, `readyWithoutAccept.spec`,
     `wp_rn_raft_Step_prop_traced`, `raft.Step.traced` (the `lt` premise from 1(b)), and (N3)
     **`RawNode.Step.traced`, `RawNode.Ready.traced`, `RawNode.ReportUnreachable.traced`**.
   What builds: each traced theorem stepping a `MsgAppResp` (`raft.Step.traced`,
   `RawNode.Step.traced`) reads `lt = 0` from 1(b), which arrives in the same landing; the others
   discharge it vacuously. Nothing reaches a `sorry`; `etc/tcb-baseline.txt` does not move. (The
   closed results reach none of these traced triples: `etc/tcb-collections/tracecheck.txt` and
   `raft.txt`; the untraced ones they reach are re-proved by `s.gh.tr = none`.)
4. The traced arms as a theorem with the two ★ callees as **hypotheses**:
   `node.run.gated_of (hAdv : RawNode.Advance.tracedSpec) (hCC : raft.applyConfChange.tracedSpec) :
   node.run.gatedSpec` (no premise on the trace). Its hypotheses are complete (B1.5): L1, lemmas
   (i)-(ii), G3 and `TrNoSnap` are theorems by then, and each arm's other premises are §4's.
   Nothing existing depends on it.
5. Only when `hAdv` and `hCC` are proved is `node.run.spec` replaced: it becomes the gated statement
   (premise dropped), and today's statement survives as its instance (`node.run.spec_untraced`, if a
   caller still names it). The traced `newRaft`, `Bootstrap`, `setupNode` (with the minting, A8) and
   `StartNode.gatedSpec` are proved after.

**Amendment A8** lands on its own branch (`trace-check-a8`, done but `setupNode`'s minting): every
`simInit` reader under a closed result re-proved in that landing, none as a `sorry` (B1.4, §5.3).
It is independent of steps 1-5 above.

**Decisions taken in this pass (the agent's, recorded in `notes/decisions.md`, "Design pass (node
API, harness)", "Design pass, revision 1", "Design pass, revision 2" and "Design pass, revision 3"):**
- the tokens at `node.Advance` through a claim on a per-node escrow (`rtkInv`, `np`), `run` needing
  nothing back (F3); revision 2: the allocation bound `al` for the driver-first order (A1, of the
  coordinator's two options), and `node.Advance.tracedSpec` the one proof with `node.Advance.spec` its
  instance (A5);
- one proved `node.Step.spec`, the gate in `stepIn`'s body, `stepIn_intro` taking `trTok` (F2);
- `TrSent` in the sealed `trTok`, and `trTok_type`; revision 2: the outbox's types as `OutTyStep` in
  `stepBundle_traced.statement`'s `Gout` (A2), with the physical half for the untyped messages;
  revision 3: the booted flag monotone in the same `Gout` (N1), `OutTyStep` from the families'
  strengthened `OutOk` (S2), the physical half's `lt` premise restricted to `MsgAppResp` (S3) and the
  whole physical half landing with clause 1(b) (N3);
- revision 3: `RawNode.Advance.spec`'s post strengthened to `ca = max rs.capplied rs.delivered.length`
  (no loan, dynamic mode), lemma (ii)'s source (N2);
- revision 3: the escrow at the fixed `nroot.@"raft_rtk"`, its key allocated in a `|={⊤}=>` prefix of
  `run`'s `readyc` send AU (`handshake_send_au_fupd`) (S1);
- the five refused calls (`ProposeConfChange`'s premise used by its proof);
- the leader case of `confc` excluded rather than proved (lemmas (i), (ii) and G3: revision 2's joint
  invariant, revision 3's order, (a) first (the term logs' gated clause on non-empty conf entries, the
  empty `ConfChangeV2` by the existing `ev2Rec`), then 1(d), `c.autoLeave = false`, from it; A3, S4,
  S5);
- `TrNoSnap` in its update form, built at `setupNode` from the client's storage contract (A4);
- `handleReady`'s conf arms from client-visible facts (`tcOps_emptyV2`, `tcOps_v1_boot`,
  `committed_emptyV2_joint`, the new `Membership.applyChange_leaveJoint`; A6, Probe A's P1 and P4);
- A8's form as landed and frozen (`trace-check-frozen-a8`: a mono list for the witnesses; §5.3
  restated to it in revision 3);
- Q33 by the existing `strconv.Itoa` axiom; the harness's `proto.Clone` by the existing `ClonePb` at
  `pbMessage`, the module moved to raft's tree (B4);
- Q34's local `netJoin` (under the instance) and `join3`; `app`'s thread token by `wp_fork_tok_body`
  (B5); Q35 (a);
- the harness's invariants `tcOpsInv` (with its requested-entries clause), `confPolicy`, `tcSnapsInv`;
- the order of work above.

**The user's:** §1 only, settled: Q32 (the premise bundle) and **Q38 (decided by the user, 2026-11-11):
`n + 2 ≤ 2^31` and `[ThreadBoundLe GF (2^31)]`, and the corollary's form**. No other change to a closed
statement or to the trust base is proposed: revisions 2 and 3 add no axiom (revision 2 uses the existing
`proto.UnmarshalConfChangeV2.wp_proof` and `ccDecodeV2_nil`, both already in raft's collection). The
tracecheck collection's baseline will gain the existing axioms of §6 when `RunConcurrent` is proved (a
collection update, not a trust-base change).
