# Review of `notes/trace-check-design.md`, round 3 (revision 2, branch `trace-check` at `01a6b67938`)

Reviewer: an independent agent, read-only. No Lean was run and nothing was built. I judged the design
against `.claude/skills/spec/PRINCIPLES.md`, the Go harness (`examples/raft/tracecheck/concurrent.go`),
raft's Go at the traced revision (`.lake/raft-trace/`: `node.go`, `rawnode.go`, `raft.go`,
`bootstrap.go`), Perennial's channel model (`.lake/packages/perennial/Perennial/Golang/Theory/Chan/`)
and the Lean the document cites. I re-derived each point and did not reuse the previous reviews'
arguments. "Uncertain" marks what I could not check.

## Summary

- **Revision 2's answers:**
  - **A1 holds.** The escrow with the allocation bound works in both hand-off orders. One sentence about
    *when* `SndPending` is entered is wrong, and one point about masks/namespaces is wrong (B6, below as
    S1). Neither breaks the argument.
  - **A2's placement (`OutTyStep` in `Gout`) holds.** L1 can be settled now: the carrier it asks for
    already exists (`OutOk` in the path families, S2).
  - **The physical half is right of the Go,** but it is ordered wrongly in §9 (N3). It also misses the
    tick specs, unless its premise is narrowed (S3).
  - **A3 (G3) holds of the Go.** An existing per-entry record makes half of it simpler (S4).
  - **A4 and A5 hold.**
  - **A6 holds,** modulo the uncertain points of Probe A.
- **New first-tier problems:**
  - **N1.** Clause 1(a) of `rnTrace` cannot be re-established by any traced triple. The bundle's post
    forgets the `booted` flag (`∃ bt'`).
  - **N2.** Lemma (ii)'s stated source is false. The driver's `ca` is the last applied *conf* index, not
    the applied index. `RawNode.Advance.spec`'s post bounds `ca` only from above. The "one check left"
    (Probe B item 5) would fail as worded.
  - **N3.** §9's order of work does not build at step 2, and step 3's re-open list is incomplete.
- **The closed results** (`raft`, `tracecheck` and the kv-family collections) stay `sorry`-free under
  steps 1-3 as long as every re-opened proof is redone in its landing. The breakages in N3 are in
  traced, raft-internal theorems that no closed result reaches. They are build failures, or `sorry`s
  that move `etc/tcb-baseline.txt`, not unsoundness.
- **Bugs:** none found in raft's or etcd's Go. Nothing for `issues/` or `nonissues/`.

---

## First tier: links that do not hold, or statements that are false or insufficient

### N1. §3.2 item 1(a), §3.3, §3.7: clause 1(a) is not re-established by the traced triples

**The statement.** 1(a): "`rs.delivered ≠ [] → b = true` for the capability's `∃ b`". §3.7: "clause 1(a)
is established there [`acceptReady`] and kept by everything else (flags only go up)". §3.3:
`RawNode.Tick.traced` keeps (a) because "`delivered` [is] unchanged".

**Why it fails.**
- The capability carries the flag `b` in an exclusive `simBoot tn id b o` (`TraceSimGhost.lean:256`,
  inside `trCapB`, `TracedCap.lean:1078-1089`). No persistent fact records it.
- Every traced statement after a step gives the flag back existentially:
  - `stepBundle_traced.on`/`.statement` end with `Gout s' := ∃ bt', trCapB … bt' …`
    (`TracedRaftStep.lean`, the `stepClose … (fun s' => ∃ bt' : Bool, …)` conclusion).
  - `stepClose_anyB` turns a close at `true` into `∃ bt'` (same file).
  - `raft.Step.tracedTriple` returns the capability "with some `booted` flag"
    (`TracedRaftStepBundle.lean:450-456`).
- So after any step from a booted node (`b = true`), the caller holds `trCapB … bt'` for an unknown
  `bt'`. It cannot re-establish `delivered ≠ [] → bt' = true`. "Delivered unchanged" does not help.
- Every triple that re-establishes `ownRawNode` after a step is affected: `RawNode.Tick.traced`,
  `wp_rn_raft_Step_prop_traced`, the `recvc` arm, and the traced `RawNode.Advance`. So is the `confc`
  arm, which reads 1(a) to use `trCapB_hookGate_applyCC` (booted).

**Caller affected.** `node.run.gated_of`'s `confc` arm (§3.2's table, `trCapB_hookGate_applyCC`
needs a booted capability), and every re-opened triple of §3.3.

**Fix.**
- Make the flag monotone in the bundle's end resource. Next to A2's change:
  `Gout s' := (∃ bt', ⌜bt = true → bt' = true⌝ ∗ trCapB … bt' …) ∗ ⌜OutTyStep s s'⌝`.
  Each path knows it: a path that logs a line closes at `true` (the fire laws set it), and one that logs
  nothing closes at `bt`.
- `stepClose_anyB` gains the implication. So do the posts of the tick specs' `Gout`
  (`raft__tickElection`, `raft__tickHeartbeat`).
- This is the same 27-file re-open as `OutTyStep`, so it costs one more conjunct per close.
- (Alternative: mint a persistent "booted" witness at the `Ready` line, in the style of A8's
  `bootDone`, and state 1(a) over it. That is new ghost state for one clause; the monotone flag is
  cheaper.)

### N2. §3.4 item 3, §8 Probe B item 5: lemma (ii)'s source is not the driver's `ca`, and today's `RawNode.Advance.spec` does not give it

**The statement.** "`advRS` sets `capplied := ca` … where `ca` is the driver's view after applying that
`Ready` (`advanceP`'s `undecFree … ca` with `monoNatLbOwn γ.cam ca`) … **One check left**, for Probe B:
that `ca ≥` the `Ready`'s last committed index at `advanceP` (whether it is already in `ownRawNode` or
follows from `Hca`)."

**Why it fails.**
- **The driver's `ca` is the index past the last applied conf change, not the applied index.**
  - `runCfg`'s docstring: "the configuration as of the last applied conf change, `(ca, rs.cfg)` …
    `Advance` may have moved the configuration index past `ca`, over no conf entry"
    (`InvNodeChan.lean:913-939`; the clause `ca ≤ rs.capplied ∧ (ca < rs.capplied → …)`).
  - The driver's view moves only at `ApplyConfChange` (`confcP`'s `ccq` at `(k + 1, cs')`).
  - In the probe's own run: after the three boot entries the driver's `ca = 3`. The new leader's empty
    entry (position 3) is committed and applied, and `applied` becomes 4 while the driver's `ca` stays 3.
    So "driver's `ca ≥` last committed index" is false at the second `Ready` of every run.
- **`Hca` does not give it either.** `RawNode.Advance.spec`'s post bounds the returned `ca` only from
  above: `rs.capplied ≤ ca ∧ ca ≤ max rs.capplied rs.delivered.length`
  (`Spec/go_etcd_io/raft/v3/RawNode__Advance.lean:126`). In the static mode it is `ca = rs.capplied`.
- **What is true.** The ghost step `StepR.advance` sets `cidx := max r.cidx a`
  (`Protocol/StepR.lean:412-416`), so in the dynamic mode the configuration index `RawNode.Advance`
  installs is `max capplied applied ≥ applied`. The proof has this, but the spec does not export it.

**Caller affected.**
- `rnTrace` 1(e), hence §3.4 item 5 (the leader exclusion at `confc`), hence `node.run.gated_of`'s
  `confc` arm.
- Also Probe B item 5, which as worded checks a false statement.

**Fix.**
- Strengthen `RawNode.Advance.spec`'s post, dynamic mode with no loan, to
  `ca = max rs.capplied rs.delivered.length` (or at least `rs.delivered.length ≤ ca`). This is proved
  from `StepR.advance` in `RawNode__Advance.lean` (the `iapply HΦ $$ %s1.term %ca` site near :2026).
  It changes a proved spec under closed results (`node.run`'s `advancec` arm uses it through
  `runCfg_advance`, `InvNodeRun.lean:2673`), so it is re-proved, not `sorry`ed, and belongs in §9
  step 2.
- Or put `uint.nat applied ≤ ca` in `hAdv`'s statement (the traced `RawNode.Advance`). Either way, say
  that the source is the installed configuration index, not the driver's view.
- 1(e) also needs the traced cluster to be in the dynamic mode. `cluster_alloc_traced` makes one, but
  1(e) is gated only on the trace. State it, or gate 1(e) on `rs.mode.isDyn`.
- Reword Probe B item 5 to: "`RawNode.Advance`'s installed `ca` is at least the new `applied`".

### N3. §9 "Order of work": step 2 does not build, and step 3's re-open list is incomplete

**The statements.**
- Step 2: "no existing statement changes but the raft-internal ones named … its physical half
  (`raft.send.spec`'s, `raft.sendTimeoutNow.spec`'s and `raft.Step.spec`'s traced premises, `XfOk`'s
  clause; untraced callers by `s.gh.tr = none`)".
- Step 3 re-opens "§3.3: `RawNode.Tick.traced`, `acceptReady.spec`, `readyWithoutAccept.spec`,
  `wp_rn_raft_Step_prop_traced`, the assembly".

**Why it fails.**
1. **Step 2 breaks the proved traced callers of `raft.Step.spec`.**
   - The physical half adds to `raft.Step.spec` the premise `s.gh.tr ≠ none → s.lt = W64 0` (§3.6).
     It adds the same to `raft.Step.tracedTriple`, whose callers "read [it] from `rnTrace` 1(b)'s
     `TrScope`".
   - Clause 1(b) only arrives in step 3.
   - At step 2, these proved theorems have no source for `s.lt = 0`. Each calls `raft.Step.spec` or
     `raft.Step.tracedTriple` on a traced node whose `ownRawNode` says nothing of `lt`:
     - `RawNode.Step.traced` (`TracedRawNode.lean:140`, which calls `wp_raft_Step` directly);
     - `wp_rn_raft_Step_prop_traced` (`:357`);
     - `RawNode.Tick.traced` (`:572`, through the tick specs, S3);
     - `RawNode.ReportUnreachable.traced` (`TracedRawNodeRep.lean:58`);
     - `raft.Step.traced` (`TracedRaftStepBundle.lean:612`).
   - So step 2 either does not build, or leaves `sorry`s that move `etc/tcb-baseline.txt`.
2. **Step 3 misses proved traced triples that re-establish `ownRawNode` at a traced node, and so must
   re-establish the new clauses:**
   - `RawNode.Step.traced` (`TracedRawNode.lean:140`);
   - `RawNode.Ready.traced` (`TracedRawNodeReady.lean:89`), which moves `delivered`, so 1(a) is
     established there as in `acceptReady`;
   - `RawNode.ReportUnreachable.traced` (`TracedRawNodeRep.lean:58`).

   §3.3 calls these "not on `run`'s path" and leaves them out of the re-open list. They are proved
   theorems whose statements mention `ownRawNode`, so adding the clauses breaks them.
3. N1's flag implication and N2's strengthened `RawNode.Advance.spec` are statement changes the order
   does not list. The first belongs with the 27 path files (step 2). The second is in step 2 as a proved
   spec re-proved.

**Caller affected.** Every intermediate landing (the brief's acceptance test). The closed results are
not reached (`etc/tcb-collections/tracecheck.txt` and `raft.txt` reach none of these traced triples),
so this is a build/baseline issue, not soundness.

**Fix.**
- Move the physical half's `s.lt = 0` premise (on `raft.Step.spec`, `raft.Step.tracedTriple` and,
  with S3, the tick specs) into step 3, together with 1(b). Keep in step 2 only what needs no `lt`: the
  `raft.send.spec` premise, `sendTimeoutNow`'s premise, the `MsgTransferLeader` premise, and `XfOk`'s
  clause.
- Or give the traced triples a temporary pure premise in step 2 that step 3 removes. That is worse: it
  is a statement change twice.
- Add the three triples of point 2 to step 3's list, or delete them if nothing will use them. They are
  "models for the `recvc` arm", and `run` reaches none of them.

---

## Second tier: improvements

### S1. (B6, A1) §3.2 items 2-4: where `rtkInv` can be opened, and its namespace

- **`readyc` is a Perennial handshake whose invariant is `inv nroot`** (`Handshake.lean:46`). Inside
  its AU the mask is `⊤ ∖ ↑nroot`, under which no namespaced invariant opens. "Opened inside a channel
  AU at `⊤ ∖ ↑(that channel's namespace)`" therefore cannot work for `readyc`.
- **Today's payload update is a basic update.** `handshake_send_au_upd` (`InvNodeChan.lean:1429`)
  takes `|==> (P v ∗ ▷ (Q -∗ Φ))`, which can open no invariant.
- **Fix for `readyc`:** state a variant with `|={⊤}=>` in place of `|==>`. It is sound, since
  `sendAu` begins with `|={⊤,∅}=>`. Allocate the key there, before the handshake's invariant is opened.
  The prefix runs only at the commit: the receiver's thread executes a waiting sender's `sendAu`
  (`ChanAuRecv.lean:227-262`), so a `select` that fires another case never allocates.
- **`advancec` (`inv advN`) is fine:** `rtkInv` is opened inside it at `⊤ ∖ ↑advN`.
- **`rtkN := N.@"rtk"` is not expressible where the invariant lives.** `isNodeChan γ id n`
  (`InvNodeChan.lean:1242`) has no `N` (and no `Cluster`). Its invariants use fixed names (`advN`,
  `tickN`, `budgetN` = `nroot.@"raft_…"`). `N.@"rtk"` is also not provably disjoint from
  `advN` for an arbitrary client `N`. **Fix:** use `rtkN := nroot.@"raft_rtk"`, and state the slots'
  `trTok` over `γn.raft`'s trace rather than a `Cluster`.
- **A1's sentence "This order can start while `pend = true`" is not what the model does.**
  - The logical `SndPending` of `advancec` is entered only by the receiver that meets the waiting send.
  - `run`'s thread runs the driver's `sendAu` (`Idle → SndPending`) and its own `recvAu`
    (`→ RcvCommit`) in one step (`ChanAuRecv.lean:227-262`), so `pend = false` there.
  - The allocation bound is still needed: the driver's AU closure cannot see `run`'s `np`. So the
    design stands, but the sentence should say "the driver's offer can be made while `pend = true`; its
    logical `SndPending` is entered by `run` at the rendezvous".

### S2. (A2, L1) L1 can be settled now: the carrier exists

- §9 leaves open whether "a broadcasting path sees the types of its queued messages at its close".
  It does, through the path families.
- `lineF` carries `⌜OutOk s o⌝` indexed by the outbox (`TracedPin.lean:44-58, :222`):
  `∀ x ∈ o, x ∈ s.outbox ∨ x.TrOk`.
- Each send gate extends it with the message it queued (`outOk_snoc`). The sites are:
  - `TracedRaftStepRecvLeadSend.lean:125, 162`;
  - `TracedRaftStepPropBundle.lean:368, 529`;
  - `TracedRaftStepLocal.lean:150`;
  - `TracedRaftStepHup.lean:640`;
  - `TracedRaftStepRecvVoteRespWon.lean:365, 490`.
- The leader's accepted-response family carries it too (`TracedRaftStepRecvLeadAccGates.lean:252`).
- The close already turns it into `OutTrStep` (`outTrStep_of_outOk`).
- **Fix:** strengthen `OutOk`'s right disjunct to `x.TrOk ∧ TrOutMsg x`. Each `outOk_snoc` site
  proves `TrOutMsg` from the gate's message type, which it pattern-matches already.
- `lineF_untraced` (an untraced send on a local family, the read-index response,
  `TracedRaftStepRecvLeadSend.lean:139-162`) then needs `ReadIdle` to be refuted. Its callers have
  `TrScope s` as `OutTyStep`'s hypothesis.
- Then `OutTyStep` at the close is `outTrStep_of_outOk` plus `TrScope s'` from `StepEnd`.
- Name this in §3.6 and close L1. The `ReplSends` worry does not arise.

### S3. (A2, physical half) narrow `raft.Step.spec`'s `lt` premise, or count the tick specs

- `s.gh.tr ≠ none → s.lt = W64 0` is needed only where a `MsgTimeoutNow` can be queued:
  - `stepLeader`'s `MsgAppResp` branch, `m.From == r.leadTransferee` (`raft.go:1588-1590`);
  - its `MsgTransferLeader` branch, already excluded by the new type premise.
- As stated unconditionally, it also binds the both-mode tick specs, which call `raft.Step.spec`:
  `raft__tickElection.lean` and `raft__tickHeartbeat.lean`, "one spec for both modes" since slice 12.
  These would gain the premise. That is not in §3.6's file list.
- **Fix:** state it as `m.Type' = MsgAppResp → s.gh.tr ≠ none → s.lt = W64 0`. The tick specs are then
  untouched. `MsgHup`, `MsgBeat` and `MsgCheckQuorum` never queue a `MsgTimeoutNow`.

### S4. (A3) G3 (a)'s empty-`ConfChangeV2` case is already recorded per entry

- The design drops the registry route because "an empty `ConfChangeV2` is a filler … the registry cannot
  see it", and puts a new gated clause on the term logs' authority, with a minting premise not yet
  located (L2).
- But every non-boot entry's record `isEntryR` already includes `ev2Rec γ e pt`
  (`Protocol/Ghost.lean:1588-1617`). For an empty `ConfChangeV2` in the dynamic mode, the fold of the
  log before it, over recorded decisions, is a **joint** configuration.
- So, by induction on positions, the first conf entry past `|γ.reBoot|` cannot be an empty
  `ConfChangeV2`: the prefix's conf entries are the boot `AddNode`s, whose fold is simple.
  - This needs neither (b) nor the `autoLeave` premise.
  - It decouples the "joint invariant" for the automatic leave.
- Only the non-empty conf case still needs the minting premise from `raft.Step.spec`'s traced `MsgProp`
  clause.
- Uncertain: that `CfgAt γ M P c` over the boot prefix is simple whatever the recorded decisions (a boot
  `AddNode` rejected leaves the configuration unchanged, so it is still simple). Worth checking before
  adding the authority clause.

### S5. (A3) 1(d)'s `c.outgoing = ∅` duplicates `trCapB`

- `trCapB`'s pure clause already says `(elements c.incoming).Perm C ∧ c.outgoing = ∅`
  (`TracedCap.lean:1085`). Only `c.autoLeave = false` is new.
- State 1(d) as that, or derive it from a well-formedness fact "`autoLeave → outgoing ≠ ∅`"
  (confchange's `checkInvariants`) if `ownTrackerC` has or can carry one.
- Uncertain: I found no such clause in `InvTrackerC.lean`.

### S6. (A4) `TrNoSnap`: the cited source of `MsgStorageAppendResp → sn = none`

- §4's last-but-one row cites `TrNoSnap` for "no snapshot" in `raft.Step.tracedTriple`'s
  `MsgStorageAppendResp → sn = none`.
- `sn` is the `Ready`'s snapshot, which exists only after a stepped `MsgSnap`. Its source is that no
  `MsgSnap` is ever stepped at a traced node (`TrNetTy`, `netP`'s gate), not log compaction.
- Correct the citation. The A4 update form itself is right: the two uses
  (`raft__maybeSendAppend.lean:121-124, 431-434`) are inside a WP at `⊤`, and `trNoSnap_traced` has
  only those two uses. `TracedReady.lean:139` and `LemmasStepLeader.lean:112` unfold `TrNoSnap` only to
  rewrite it.

### S7. (A5) the claim's disjunction

- `readyToksClaim := ⌜ms = []⌝ ∨ element` is a sealed form of "trivial, or the real resource".
  PRINCIPLES' "No disjunction of alternative specs" warns against exactly this shape.
- It is justified here: it is what makes `node.Advance.spec` an instance rather than a second proof.
  The docstring should say it departs, next to its existing "departure from no identification handles".

### S8. Minor

- §3.4 item 4 (a) mixes "position `≥ |γ.reBoot|`" with "index `i > |γ.reBoot|`". Both are right under
  0-based positions and 1-based indices, but state the convention once.
- §2.3's `ConfChange` (V1) arm relies on the V1 entry past `boot` not being a filler. That is right:
  `Filler` admits types 0 and 2 only (`Ghost.lean:1177`), so such an entry is a requested one, hence
  in `ops.drop boot.length`, hence of type 0, which is a contradiction. Say "type 1 is never a filler"
  explicitly.

---

## The links the brief asks about, checked

| Item | Verdict |
|---|---|
| A1, both orders | Holds. In `RcvPending`, `advDep` (with `np`) is in `advInv` when the driver's send commits (the driver's thread runs `run`'s waiting `recvAu` and its own `sendAu` in one step), so `pend = false` and the element gives `j < a`. In `SndPending`, `run` holds `np` (`advancec` is armed only after the deposit, `node.go:435-446`, and `readyc` is re-armed only at `advancec == nil`, `:354`), and the payload's `monoNatLb al (j+1)` gives `j + 1 ≤ a`. Stale claims and the claim-less driver are right. Masks and namespaces: S1. |
| A2 placement | Holds (`Gout` is the caller's; `raft__Step` untouched). L1 is answered by S2. |
| A2 physical half | True of the Go: `MsgTimeoutNow` and `MsgTransferLeader` are the only untyped types in `sentShapeTypes` (`ApiVocab.lean:71-114`), and all queueing goes through `send` (`raft.go:592, 598`). Ordering: N3; scope: S3. |
| A3 | True of the Go. The sources `MsgProp` (traced premise, `raft__Step.lean:664`), `becomeLeader`, the refused-change filler, and `appliedTo` (`raft.go:742-761`, excluded via `:663` and (b)) are complete; all queueing and appending is by the leader. Simplification: S4, S5. |
| A4 | Holds (S6 is only a citation fix). `storBnd_zero` has its ingredient (`nodeAppliedLb_zero`, `InvNode.lean:553`). |
| A5 | Holds (S7). |
| A6 | Holds as a design; `committed_emptyV2_joint` (`InvNodeRule.lean:365`) is the exported law. Uncertain: Probe A's glue (`ClonePb`'s `T.ro`/`T.dec` against `msgOwn`/`msgPtsC`). |
| Order of work | Closed results stay `sorry`-free provided each re-opened proof is redone in its landing. Steps 2 and 3 as written break traced proved theorems (N3). |
| L1 | Settleable now (S2). |
| L2 | Lemma (i) holds (`HupGuard` is exclusive, `SpecResults.lean:61-73`, so 1(c) follows at the close from `StepEnd`). Lemma (ii): N2. G3: S4 reduces the locating task to the non-empty case. |

## Per statement

| Statement | Provable from its callees? True of the Go? | Sufficient for its callers? |
|---|---|---|
| §1 (settled) | not re-opened | — |
| `RunConcurrent.spec`, `app`, `send`, `netJoin` | yes (B5 checked against `Lifting.lean:1964-2014`) | yes |
| `handleReady` | yes (A6) | yes |
| `isReadyChan_recvAu.tracedSpec` | yes, with S1's `|={⊤}=>` send variant | yes |
| `node.Advance.tracedSpec` / `.spec` instance | yes (A1, A5) | yes |
| `stepIn_intro`, `trTok_type`, the refusals | yes | yes |
| `rnTrace` 1(a) | **no: not re-established after a step (N1)** | — |
| `rnTrace` 1(b) | yes, via S2's `OutOk` | yes |
| `rnTrace` 1(c) | yes (`HupGuard`, lemma (i)) | yes |
| `rnTrace` 1(d) | yes (G3 (a)); partly redundant (S5) | yes |
| `rnTrace` 1(e) / lemma (ii) | **not from the stated source (N2)**; yes with `RawNode.Advance`'s post strengthened | yes |
| physical half | yes; ordering N3, scope S3 | yes |
| `TrNoSnap` update form | yes | yes |
| `node.run.gated_of` | depends on N1, N2 | — |
| §9 order | **step 2 does not build; step 3's list is incomplete (N3)** | — |

## Ranking by need of revision

1. §3.2 item 1 / §3.3 / §3.7, `rnTrace` 1(a) and the bundle's flag (N1).
2. §3.4 item 3 / Probe B item 5, lemma (ii)'s source and `RawNode.Advance.spec`'s post (N2).
3. §9, the order of work (N3), with S3.
4. §3.2 items 2-4, the escrow's namespace and the `readyc` update (S1).
5. §3.6 / L1, name the `OutOk` carrier and close L1 (S2).
6. §3.4 item 4, G3 (S4, S5).
7. S6-S8.

No bug found in raft's or etcd's Go code. Nothing for `issues/` or `nonissues/`.
