# etcd-io/raft#86: Reduce chance of duelling leaders

- PR: https://github.com/etcd-io/raft/pull/86 (open), one commit `c976ceb6c78d8aa3cf24647bc8455fa41ef675f2`
  ("Randomise lower bits of terms"), against upstream `main` at `177ef28aa`.
- Verified at fork commit `pr-raft-86-goose-lean` (`~/etcd-pr/raft-86`). That is
  `raft37-goose-lean` (`509271dac`, the pinned raft v3.7 plus the read-index fix) with the PR's
  `raft.go` diff applied. It applied cleanly (`git apply -3`, no conflicts, no rewrite). The
  verified code is the PR's code, gofmt-unformatted indentation included.
- etcd-grove branch `pr-verify/raft-86` (worktree `/shared/etcd-grove-pr/raft-86`). The tests and
  logs behind the findings are in `notes/pr-verify/raft-86/` (see its `README.md`).

## Verdict

**Safety holds.** The PR draws the low 16 bits of a new term at random and moves the upper 48
bits (the epoch) up by exactly one. With that, election safety, log matching, leader completeness
and the read-index results still hold, proved with no new axiom or `sorry`, below the last epoch.
The protocol model's `campaign` rule now allows a jump to any later term, not just `term + 1`,
and its ghost-state proofs went through unchanged in substance: skipped terms are terms the node
never voted or campaigned in. This confirms the PR's claim that a jump is like a partitioned
candidate catching up.

**The PR has costs it does not state.**
- **The term can wrap.** The premise every campaign needs moves from `term + 1 < 2^64` to
  `term + 2^16 < 2^64`. In the last epoch the term wraps backwards, to the draw itself, where the
  old code wrapped only at `2^64 - 1`. That takes about 2^48 elections, so it is unreachable in
  practice.
- **The term budget shrinks.** `node.go`'s term budget is now in units of `2^17` per tick credit.
- **Two liveness regressions,** neither visible to the safety proof and both reproduced by Go
  tests:
  - In the race the PR targets (PreVote and CheckQuorum on, two concurrent candidates), the
    losing candidate deposes the freshly elected leader about half the time.
  - A granted pre-vote no longer means the election can be heard, because the election draws its
    term again.
- **No test was updated.** 38 existing tests fail at the PR head and pass at its parent.

**Not covered:** the probabilistic claim (fewer collisions, faster recovery) and liveness in
general. The `RawNode`/`node.go` results also assume pre-vote off, as on `lean`, so pre-vote is
covered only by `raft.Step`'s spec and the protocol model.

## Conflict resolution (verified code vs the PR)

There was none: the diff applied as is. `go build ./...` passes in the fork worktree.
`go test .` fails 38 tests, the same 38 that fail upstream at the PR head
(`notes/pr-verify/raft-86/pr-head-failing-tests.log`). At the parent `177ef28aa` all pass. The
failures are tests with hard-coded terms (`term = 2`, `r.Term + 1`), which the PR leaves
unchanged.

## Changed functions

| Function | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| `raft.nextTerm` (new) | new | not translated (new) | verified | new spec `Spec/go_etcd_io/raft/v3/raft__nextTerm.lean`, proved (`Proof/.../raft__nextTerm.lean`) |
| `raft.becomeCandidate` | behavior change | verified | verified | new spec, incompatible (term `nextTermOf s.term x`, was `s.term + 1`); callers re-checked |
| `raft.campaign` | behavior change | verified | verified | new spec, incompatible (pre-vote and election terms are `nextTerm()`s; premise `+2^16`); callers re-checked |

No types, fields or package variables change. The PR's new function reads the existing
`globalRand`, whose `isLockedRand` comes from package initialization, as for
`resetRandomizedElectionTimeout`.

### The behavior changes

- `nextTermOf t x` (`Proof/go_etcd_io/raft/v3/Defs.lean`) is the Go expression
  `((t & 0xffff_ffff_ffff_0000) >> 16 + 1) << 16 | (x & 0xffff)`. Its lemmas:
  - `nextTermOf_toNat`: its value is `((t / 2^16 + 1) mod 2^48) · 2^16 + x mod 2^16`.
  - `nextTermOf_bounds`: if `t + 2^16 < 2^64`, then `t < nextTermOf t x < t + 2^17`.
  - `nextTermOf_wraps`: if `t ≥ 2^64 - 2^16`, the result is `x mod 2^16 < t`.
- **becomeCandidate.**
  - Old: with `s.term + 1 < 2^64`, it moves to `becomeCandidate id s` at term `s.term + 1`.
  - New: with `s.term + 2^16 < 2^64`, for some draw `x` it moves to
    `becomeCandidate id s (nextTermOf s.term x)` (`Spec/.../raft__becomeCandidate.lean`).
  - Not compatible: the old postcondition named the term `s.term + 1`.
- **campaign.**
  - Old: every request and the self-response carry `s.term + 1`; for an election the node moves
    to that term.
  - New: they carry `nextTermOf s.term x` for some draw `x` (`Spec/.../raft__campaign.lean`,
    `campaignState … T`). In a pre-election that is `nextTerm()`'s draw; in an election it is
    `becomeCandidate`'s. A pre-election followed by its election makes two independent draws.
  - The premise is now `s.term + 2^16 < 2^64`, and it is exact: at `s.term ≥ 2^64 - 2^16` the
    term wraps, and to `0` for a zero draw, where `send` panics on the vote message.
- **The protocol model** (`Protocol/Model.lean`, `StepC.lean`, `StepR.lean`).
  - Old: `Step.campaign` moved to `pbecomeCandidate id s` at `s.term + 1`, with premise
    `s.term + 1 < 2^64`.
  - New: it takes any `T` with `s.term < T` (`pbecomeCandidate id s T`).
  - The model is more general than the code; the code instantiates `T := nextTermOf s.term x`.
    The ghost-state proofs were re-proved for any later `T`: `ownLogGhost_campaign` in
    `Protocol/StepGhost.lean`, `ownRaftGhost_step_campaign` in `Protocol/Refinement.lean`,
    `RefinementDyn`, and `StepRInv`.

## Callers (step 6)

Every arrow is "is called by". Each node's spec was changed as listed, and each was re-proved:
no `sorry`.

- `nextTerm` ← `becomeCandidate`, `campaign`.
- `becomeCandidate` ← `campaign`.
- `campaign` ← `hup`, `stepCandidate` (pre-vote win).
  - `hup`: `HupOk`/`HupOkC` term bound `≤ +1` → `< +2^17`. `HupGuard` keeps the campaign's term
    `T` with `s.term < T` (`Proof/.../SpecResults.lean`). Premise `+2^16`.
  - `stepCandidate`: `PrecandVoteRespResult` names the election's term
    `nextTermOf s.term x` (`Spec/.../stepCandidate.lean`); `prevoteRespResult … T`.
- `hup` ← `raft.Step` (`MsgHup`, `MsgTimeoutNow` via `stepFollower`), `tickElection`.
  - `raft.Step`: `TermStep` bounds for `MsgHup`/`MsgTimeoutNow` `+1` → `+2^17`; `RespStep`'s
    pre-vote win `= s.term + 1` → `≤ s.term + 2^17`; premises `+1` → `+2^16`
    (`Spec/.../raft__Step.lean`). The branch proofs `MsgHup`, `MsgRest`, `MsgPreVoteResp*` and
    `prevote_lemmas` were adapted.
  - `tickElection`/`tickHeartbeat`: `TickStep` `+1` → `+2^17`.
- `raft.send`'s `SendOk` and the `msgsAfterAppend` invariant `AAMsgOk` (`InvRaftPhys.lean`): a
  self-addressed `MsgPreVoteResp` may be `2^17` past the node's term (was 1).
- `RawNode.Tick`, `RawNode.Campaign`, `RawNode.Step` (`MsgTimeoutNow`), `RawNode.Advance`: these
  are exported API, and the change is client-visible. The term bounds go `+1` → `+2^17` and the
  premises `term + 1 < 2^64` → `term + 2^16 < 2^64`. The PR does not mention this; it is the
  "terms grow faster" consequence. `InvRawnode`, `InvNodeRun` and `RawNode.acceptReady` were
  adapted.
- `node.go` (`node.run`, `Node.Tick`, `StartNode`, `RestartNode`; `Proof/.../InvNode.lean`).
  - The term budget: the invariant was `M + c < 2^64 - 1`, with one credit worth one term. It is
    now `M + (c + 1) · 2^17 < 2^64`, with one tick credit worth `2^17` terms.
  - `budget_alloc` needs `(N + 1) · 2^17 < 2^64` (was `N < 2^64 - 1`). That is a bound of about
    2^47 ticks (about 4·10^5 years at 100 ms), a user-visible restriction that changes nothing in
    practice.
  - `termLB_bound`, `budget_spend` and `budget_step` were re-proved.
  - The `register` example's `budget_alloc` call still goes through.
- Downstream (etcd server, the register example, everything in `lake build`): built unchanged.

Not followed further, and nothing there needs it: etcd itself (no term arithmetic, per the
reviewer's search of `server`, `client`, `pkg` and `tests`).

## Trust base (step 7)

`etc/tcb-collections/pr-raft-86.txt` holds the roots of every changed function and checked
caller. `etc/tcb-report.py --collection … --check --update` gives the baseline in that file:

- **New axioms:** none.
  - A first version proved `nextTermOf`'s lemmas with `bv_decide`, which put its native-decide
    axiom (`nextTermOf_bv._native.bv_decide.ax_1_5`) into the trust base. They are now proved
    over `Nat` (`nextTermOf_toNat`), with axioms `propext`, `Classical.choice` and `Quot.sound`
    only.
- **New `sorry`s:** none.
- **Existing:** the collection's axioms are those of the same roots on `lean`: the protobuf `proto`
  trust boundary, `fmt.Errorf`, `DescribeConfChange`, `ConfChangeType.String`, the RNG
  (`lockedRand.Intn` reaches `rand.Int63n`, already a callee through `reset`), and Perennial's
  initializer `sorry`s.
- `etc/tcb-report.py --check` on the whole repository: the trust base matches
  `etc/tcb-baseline.txt` (229 axioms, 12 `sorry`s), as on `lean`. The full `lake build` (5106
  jobs) passes.
- `etc/verified-code.py --package go.etcd.io/raft/v3`: package `go.etcd.io/raft/v3` has 189 of
  244 functions verified and 1 assumed, the same as `lean`. The script reads the Go sources at the
  pinned revision, which has no `nextTerm`, so it lists `raft.nextTerm (verified)` among the
  specs outside the totals.

## Findings

1. **The losing concurrent candidate deposes the new leader** (liveness regression; reproduced).
   - Setup: three nodes with PreVote and CheckQuorum (etcd's defaults). Nodes 1 and 2 both win a
     pre-vote through node 3. Node 1 wins its election at `T1`, and node 3 follows it (lease).
   - Before the PR: node 2 is at the same term and becomes a follower on node 1's `MsgApp`.
   - With the PR: node 2's term `T2` is its own draw. When `T2 > T1` (half the time), node 2
     answers node 1's `MsgApp` with a `MsgAppResp` at `T2`, the `m.Term < r.Term` branch for
     `checkQuorum || preVote`. Node 1 steps down. Node 2 cannot win: its log lacks node 1's
     empty entry, and node 3 is in node 1's lease.
   - Result: no leader for about an election timeout. This is exactly the race the PR means to
     shorten, so in small clusters the PR can lengthen recovery.
   - Reproduction: `notes/pr-verify/raft-86/raft_review86_test.go`,
     `TestReview86RaceDeposesNewLeader`. The leader is deposed in 99 of 200 runs at the PR head
     and 0 of 200 at the parent.
2. **A granted pre-vote no longer means the election can be heard** (liveness; reproduced).
   - The pre-vote is sent at `T1 = nextTerm()`, the election at an independent `T2`, lower than
     `T1` about half the time.
   - A peer at `T2 ≤ P < T1` grants the pre-vote and then ignores the `MsgVote`, which carries a
     lower term than its own.
   - Reproduction: `TestReview86PreVoteGrantedVoteIgnored`, in 93 of 196 granted pre-votes.
     `TestPreVoteTermDiffersFromElectionTerm` shows the terms differ (lower in 90 of 200).
   - Suggested fix: draw once, at `becomePreCandidate`, and reuse that term for the election.
     That would also restore the pre-vote meaning "an election at this term would be heard".
3. **The term wraps in the last epoch.**
   - At `Term ≥ 2^64 - 2^16` the new term is the 16-bit draw, below the old term (zero for a zero
     draw, where `send` panics). `reset` then clears `Vote`, so the node could vote twice in an old
     term.
   - This was possible before only at `2^64 - 1`. It needs about 2^48 elections.
   - Proof: `nextTermOf_wraps`. Test: `TestNextTermWrapsInLastEpoch`, where term `2^64 - 1001`
     goes to `1076`.
   - The specs carry it as the premise `term + 2^16 < 2^64`.
4. **No tests updated.** 38 tests fail at the PR head
   (`notes/pr-verify/raft-86/pr-head-failing-tests.log`). They cannot simply be reseeded:
   `globalRand` is `crypto/rand`.

The PR fixes no finding in `issues/`. No bug in the existing (pinned) code was found, so nothing
was added to `issues/`.

## Reviewer

A fresh reviewer subagent checked the specs, the protocol generalization, the budget and the Go
code.
- **Agreed:**
  - The new specs state the PR's behavior exactly: next epoch, random low half, independent
    draws.
  - The generalized `campaign` rule is the standard Raft generalization, and nothing about
    skipped terms is missing.
  - The budget arithmetic is right.
  - `lockedRand.Intn`'s spec is sound across concurrent raft instances (mutex over
    `crypto/rand`).
  - No problem with leader transfer, CheckQuorum leases or ReadIndex.
- **Found:** findings 1 and 2 (its tests), and stale "+1" comments, since fixed.
- **Open points:**
  - `HupGuard` gives only `s.term < T`, not `T = nextTermOf s.term x`. It is weaker than the code
    but enough for every caller; `campaign`'s and `stepCandidate`'s specs keep the exact term.
  - Several upper bounds are `≤ +2^17` where `< +2^17` holds.
  - `raft.nextTerm.spec` says nothing of the draw's range (the masking makes it irrelevant).

## Draft review comment (for the user to edit and post)

> Thanks for this. We looked at it in detail. Raising only the upper 48 bits by one and picking
> the low 16 at random keeps Raft's safety argument intact: a jump to a later term is like a
> candidate that missed a few terms. We see three issues, though.
>
> 1. With PreVote and CheckQuorum on (etcd's defaults), the losing candidate of a concurrent race
>    now often deposes the winner. In a 3-node cluster, nodes 1 and 2 both win their pre-vote
>    through node 3, and node 1 then wins the election and node 3 follows it. Node 2 is still a
>    candidate. It ran its election at its own random term, so about half the time that term is
>    higher than node 1's. It then answers node 1's MsgApp with a higher-term MsgAppResp, and
>    node 1 steps down. Node 2 cannot win either, because node 3 is in node 1's lease and has a
>    longer log. Before this change both candidates were at the same term and node 2 just became
>    a follower. In our test this happens in about 100 of 200 runs, and never on `main`.
> 2. The pre-vote and the election draw their terms separately. A peer whose term is between the
>    two grants the pre-vote and then ignores the vote, which carries the lower term. Drawing the
>    term once, when becoming pre-candidate, and reusing it for the election would avoid this.
> 3. The term now wraps in the last 2^16 terms instead of only at 2^64-1, and it wraps backwards
>    (to the random low bits). This is unreachable in practice, but a check or saturation would
>    be cheap.
>
> Also, about 38 tests in the package hard-code `r.Term + 1` and fail with this change. Since the
> draw uses crypto/rand, they would need a way to inject the random source.
