# Antithesis, the RawNode side: design (#33 S3c, phase 1)

Stage S3c of mit-pdos/etcd-grove#33 (2026-11-23; branch `antithesis-rawnode-spec`). Phase 1 of
`notes/spec-first-plan.md`'s *design before plumbing*: every statement as text, each with what it is
proved from, for review before any Lean. **Nothing here is typechecked.** Lean is a sketch; names marked
*(new)* do not exist yet.

The goal of #33: a closed theorem `raft_antithesis_safe` (with a `Robust` form) that `Main` of
`examples/raft/antithesis` (branch `antithesis-check`: `harness.go`, `main.go`,
`notes/antithesis-check-design.md`) never panics. `Main` runs three verified `RawNode`s, one goroutine
each, records Antithesis's default-mode reports (`boot`, `recv`, `ready`, `send`, `apply`) and checks the
stream with a Go transcription of `EtcdRaft.tla` + `EtcdBinding.tla`; S3b gives it a Lean transcription
(`AntCheck`, `Proof/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/check/Tla/*.lean` on
`antithesis-check`) and `check.Run`'s spec. S3c closes the nine gaps S3a listed (issue #33, S3a comment):
raft's side of the chain, and the refinement that makes each report a binding step.

The user's decisions, taken pending veto (issue #33): (1) strengthen `RawNode`'s specs to expose raft's
abstract state and the effect of each input, then prove a refinement from raft's protocol model to the
binding's steps; (2) `RawNode` becomes a sealed module of raft's client API, with the term-budget laws
exported; (3) `restartSpec` keeps the durable state owned.

**Revision 1** (2026-11-23), after review round 1 (fresh reviewer; 6 first-tier, 10 second-tier). What
each first-tier finding changed:
- F1 (a forwarded `MsgProp` has term 0, which revision 0's `RecvEnd` treated as stale): `RecvEnd` gets a
  local arm for term 0 and its stale arm needs `m.term ≠ 0`, as `StepEnd`'s `StaleMsg` (§2.2).
- F2 (`commitIn_camp` false: a losing candidate also has an `isCamp`): the law takes the leader's
  `isLeader` and the committed log's `logRecs` (§2.1).
- F3 (nothing proved excludes `MsgSnap`, and a snapshot `Ready` makes the harness panic): new §2.5, the
  second raft-side change (the traced proof's no-compaction argument, `TrNoSnap`, made available
  untraced) and a row in §4; Q7.
- F4 (`AdvanceEnd` had nothing to range over: `Pending.self` drops the message): `rawNode` gets a third
  index, the self-addressed messages queued for `Advance` (§2.1, §2.2).
- F5 (state changes between reports): `NodeView` is the node's state between inputs, not at its last
  report; new lemma `antSim_quiet` (§3.2, §3.3).
- F6 (pre-vote and check-quorum off had no source): the start spec takes both off and `rawNode` keeps
  them off (`rawNode_scope`, §2.1).
Second-tier S1-S10 are folded in where they apply (§2.4 counts, `AckEnd`, `AppRespEnd`'s reject arm, C3,
C4, entry types, layout, the boot drain).

Reading order: §0 the answers the coordinator asked for; §1 the chain, top down; §2 raft's side (the API
module, the strengthened specs, the one raft-internal change); §3 the refinement; §4 where it could be
false; §5 what the trace check's simulation gives us; §6 size and order of work; §7 questions.

Citations: R = `third_party/etcd-raft-formalized/spec/EtcdRaft.tla`, B = `.../EtcdBinding.tla` (both on
`antithesis-check`), by line.

---

## 0. The answers first

**Does raft's protocol model record votes and per-entry terms? Yes, both, and more.** The protocol state
`PState` (`Protocol/Model.lean:489`) has `term`, `vote`, `lead`, `role`, the tally `votes : GMap w64
Bool`, the `outbox`, the log as `base : entryID` and `log : List EntryM` (each entry with its `Term'` and
`Index'`), `commit` and the leader's `matched`. Every node's ghost state is `ownRaftGhost γ id (toPState
s)`, at the `PState` of the node's `NState s`. The persistent ghost facts behind it record:

| raft ghost fact (`Protocol/Ghost*.lean`) | what it says | the binding variable it backs |
|---|---|---|
| `isVote γ v t c` | `v` voted for `c` in `t` (frozen, unforgeable) | `votes`, grant facts in `msgs` |
| `isLeader γ id t` (`leaderWit`) | a quorum of `isVote`s for `id` at `t` | `leaders` |
| `isCamp γ c T F` | `c`'s campaign log at `T` | vote-request facts, `ledLog[T]`'s start |
| `logRecs γ b es` / `isEntryR` | each entry was created by its term's leader at its index | log matching of `log`, `ledLog`, `chain` |
| `leadPrefix γ ldr t bL l` | `l` is a log the leader of `t` had | request facts (`Sendable`) |
| `isAcked γ v t i`, `ackIn` | `v` acknowledged the leader of `t` up to `i` | ack facts, `confirmed` |
| `isCommitted γ l`, `commitIn γ F c tm` | `l` is a prefix of the one committed log; `F` committed to `c` as known in `tm` | `chain`, `termLen` |
| `RaftState` (`Protocol/RaftState.lean`) | the durable term, vote, log, commit the client entered | `currentTerm`, `voteTerm`/`voteFor`, `log`, `commitIndex` |

S3a's "no vote in `RNState`" is right about the *client's* record (`RNState`, `ApiVocab.lean:242`, has
`term` but no `vote`, `log` or role-witness), and about nothing else: `ownRawNode` holds the `NState` whose
`toPState` has all of it, and `RNState.dur : RaftState` has the durable vote. **The gap is exposure, not
recording.**

**Is the refinement true?** For the harness's scope (three voters, empty logs, synchronous writes, one input
then its `Ready`s, PreVote/CheckQuorum/transfer off, no snapshot, membership change or read index): yes,
by the argument of §3 and §4, guard by guard. Two of the binding's rules are stricter than raft in general
and hold here only because of the scope: "no new term while leading" (B 365, needs synchronous writes and
three voters) and `CommitBeyondConfirmed` (B 435, needs that a leader's `Match` for a follower only comes
from that follower's acknowledgements in the leader's term). The 1,500 harness runs (S2) and the 720
simulator streams accepted by both checkers are the evidence; none hit a rejection. §4 lists every guard.

**The mechanism question, which decides the cost.** The binding needs the *exact* effect of each input:
`raft.Step.spec`'s post gives only `∃ B recv, StepC c id B (toPState s) recv (toPState s')`
(`GMode.StepOut`), with `recv` unconstrained and any composition of the protocol's rules. That is too
weak, and not only in principle: `campaign ; abandon` (term up, back to follower, no message) is a
`StepC` chain the binding rejects at `adopt` (B 367: a term change of a follower needs the handled
message's term); `sendApps ; higherTerm(m)` leaves an `MsgApp` of the old term in a `Ready` whose node has
moved on, which `Send` rejects (B 545). Raft's code does neither. What says so is **`StepEnd`**
(`LemmasStepGates.lean:164`): "the code's end state on the message's path", as exact as the callees' specs
(`FollowerStepResultC`, `CandidateStepResultC`, `LeaderStepResultC`, `HupOkC`, `VoteEnd`), built for the
trace check's closing wand. Every close site in `raft__Step.lean` already proves it outright (`Hend`, from
the path's callee result); the wand only receives it guarded, `s.gh.tr.isSome → StepEnd …`. **Making that
premise unconditional is the first change inside raft's step proofs** (§2.4).

**The second (review round 1, F3): no snapshot.** The untraced proofs do not exclude a leader's `MsgSnap`:
`StepEnd`'s broadcasts are `ReplSends` (`ReplOk = AppOk ∨ SnapOk`), and the no-snapshot flag `NGhost.ns`
is always `false` since U8 v2. Raft's Go sends none here (the harness never compacts its `MemoryStorage`,
so `term(Next-1)` and `entries(Next)` never fail), and the traced proof already says so
(`maybeSendAppend.spec`'s `TrNoSnap`: at a traced node a compacted log is a contradiction). §2.5 makes
that argument available to an untraced node whose storage is never compacted. Everything else is new
modules or new proofs of the `RawNode` functions.

---

## 1. The chain, top down

```
raft_antithesis_safe (+ Robust)                     S4   Spec/.../antithesis/TopLevelRobustness.lean
  └ Main's spec: check.Run accepts, so no panic     S4   from RunCluster's post + check.Run.spec (S3b)
     ├ check.Run.spec: returns AntCheck.run cfg evs S3b  (antithesis-check)
     └ RunCluster.spec: post ⌜AntCheck.Accepts cfg evs⌝ for the recorded evs     S4
        └ the harness invariant AntInv (§3.2), under the recorder lock:
            S := the checker after the recorded events (AntCheck.Checker), not done
            AntSim S V net  (§3.2)                                               S3c
          kept by each report through the per-report lemmas (§3.3)               S3c
            └ the RawNode API (§2): rawNode γ rn id rs ps, InputEnd, ReadyOut      S3c
                └ raft's proofs (one change: StepEnd unconditional, §2.4)          S3c
```

S3c delivers §2 and §3 (statements, then proofs). S4 is the harness's own proof (`RunCluster`, `node.run`
of the harness, `deliver`, `send`, the recorder) and the closed theorem; S4 uses §3's lemmas as black
boxes. The split follows the trace check's (`notes/trace-check-design.md` §2: harness statements over the
node API's traced statements).

---

## 2. Raft's side

### 2.1 The API module (decision 2)

New importable module `Proof/go_etcd_io/raft/v3/RawNodeApi.lean` *(new)*, added to `etc/api/raft.txt`
with its interface under `interface/`. It imports the internals (`InvRawnode`, `InvRawnodeReady`,
`InvNodeChan`, `RawNodeStartSpec`) non-publicly and exposes only sealed names and laws. The `RawNode`
specs themselves stay where they are (`Spec/go_etcd_io/raft/v3/RawNode__*.lean`, internal, over
`ownRawNode`); the API states their client form over `rawNode` (as `InvNodeRule` states the node API's
`unifiedSpec` variants), proved in a linking module `RawNodeApiLinked.lean` *(new)* from the internal
proofs.

```lean
/-- (new) A `RawNode` closed in a cluster, at the client's record `rs`, the protocol state `ps` and the
self-addressed messages `qs` queued for `Advance` (revision 1, F4: `rs.steps : List Pending` drops them,
`Pending.self pv t`, and after `acceptReady` they are not in the `NState`'s outbox either): `ownRawNode`
with its `NState`'s protocol reading and its queue's abstraction named. Sealed. -/
@[no_expose] def rawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState)
    (qs : List Msg) : IProp GF :=
  ownRawNodeAt γ rn id rs ps qs

/-- (new, in a module `import all`-ing `InvRawnode`) `ownRawNode`'s body with `toPState s = ps` and the
queued `stepsOnAdvance`' protocol messages `qs` (`pendList`'s records, abstracted: a leader's
self-acknowledgement at its last index, a candidate's self-vote; the storage acknowledgements carry no
protocol message). Its text is `ownRawNode`'s with two conjuncts more. -/
def ownRawNodeAt (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) :
    IProp GF :=
  iprop(∃ (s : NState) …, <ownRawNode's conjuncts> ∗ ⌜toPState s = ps⌝ ∗ ⌜PendAbs id s steps qs⌝)

theorem ownRawNodeAt_ownRawNode : ownRawNodeAt γ rn id rs ps qs ⊢ ownRawNode γ rn id rs      -- internal
theorem ownRawNode_at : ownRawNode γ rn id rs ⊢ ∃ ps qs, ownRawNodeAt γ rn id rs ps qs      -- internal
```

`ownRawNode` itself is not edited: every proof that unfolds it (`node__run*`, `InvNode*`, the traced
files) is untouched. The cost is one copy of `ownRawNode`'s conjunct list; the two entailments (by
unfolding: entailments, not `rfl`, review S8) fail to build if the copy drifts.

**The client's protocol state is `PState` as it is** (`Protocol/Model.lean`, already importable). Not a
slimmer record: every law below is over `PState`'s fields and the protocol's own functions (`plogLast`,
`plogUpToDate`, `plogTermAt`, `pbecomeFollower`, …); a second record would need its own copies of them.

**The laws** (each a theorem of `RawNodeApi.lean`, proved from `ownRaftGhost`'s conjuncts; persistent
facts read out of the owned predicate):

| law *(new)* | statement (sketch) | source |
|---|---|---|
| `rawNode_wf` | `⌜ps.base = base0 → PlogWf base0 ps.log ∧ uint.Z ps.commit ≤ plogLastIndexZ base0 ps.log ∧ ps.term = rs.term⌝` | `NStateWf`, `LogOk`, `Htrm` |
| `rawNode_logRecs` | `logRecs γ base0 ps.log` (when `ps.base = base0`) | `ownLogGhost`'s `Hrecs` |
| `rawNode_leader` | `⌜ps.role = .leader⌝ → isLeader γ id ps.term ∗ ∃ F0, isCamp γ id ps.term F0 ∗ ⌜F0 <+: ps.log⌝` | `leaderWit`, `leadLogOwn` |
| `rawNode_vote` | `⌜ps.vote ≠ 0⌝ → isVote γ id ps.term ps.vote` | `VoteHistOk`, vote table |
| `rawNode_tally` | `[∗ set] v ∈ granted ps.votes, isVote γ v ps.term id` | `Htally` |
| `rawNode_commit` | `commitIn γ ps.log ps.commit ps.term ∗ isCommitted γ (ps.log.take ps.commit)` | `ownLogGhost`'s `Hcommit` |
| `rawNode_outbox` | `[∗ list] m ∈ ps.outbox, outMsgOk …` reduced to: each message is `isMessage` once its batch is entered (as `Ready.spec`'s `Henter`) | `Hout` |
| *(revision 1, F6)* scope in the body | `ownRawNodeAt` has one more conjunct, `⌜rs.mode = .static ∧ s.prevote = false ∧ s.cq = false⌝`: the API's `rawNode` is the scope's node. The start spec establishes it from the new premise `cv.PreVote' = false ∧ cv.CheckQuorum' = false`; every step keeps it (the flags are the `Config`'s, copied by `newRaft`, never written) | `NStateWf`, the start spec |
| `rawNode_noCompact` *(revision 1, F3)* | in a never-compacted cluster, every queued message is no `.snap` (§2.5) | §2.5 |
| `rawNode_entries` *(review S6)* | every entry of `ps.log` is a filler (the leader's empty entry) or a proposal whose ticket `entTk` the client minted, so of the type the client proposed | the proposal registry (`deposited`, `entTk`) |
| `rawNode_term_tc` | `⌜uint.Z ps.term ≤ uint.Z rs.tc⌝` | exists (`ownRawNode_term_tc`) |
| `rawNode_raise_tc` | `rawNode γ rn id rs ps ⊢ rawNode γ rn id {rs with tc} ps` (`rs.tc ≤ tc`) | exists (`ownRawNode_raise_tc`) |

And the protocol's agreement laws, already in importable modules (`Protocol.Ghost`): `isLeader_unique`,
`isVote_agree`, `logRecs_agree`, `isCommitted_agree`/`isCommitted_prefix`, `isCampK_agree`. One law is
missing (the deepest raft-side obligation of S3c):

```lean
/-- (new; revision 1, F2: revision 0 lacked `isLeader` and `logRecs`, and was false of a losing
candidate's campaign record) **Leader completeness, for a client.** What was committed as known in term
`tm` is in the campaign log of every *leader* of a later term. Proved from `lc_core`/`cq_agree`
(`Protocol/LeaderCompleteness.lean`, which take `isLeader` with the campaign record and conclude at an
index of a log with records) inside `raftCommitInv`. -/
theorem commitIn_camp (γ : RaftNames) (F : List EntryM) (c tm : w64) (j T : w64) (F0 : List EntryM) :
    uint.Z tm < uint.Z T →
    ⊢ commitIn γ F c tm -∗ logRecs γ base0 F -∗ isLeader γ j T -∗ isCamp γ j T F0 ={↑raftN γ}=∗
      ⌜F.take (uint.nat c) <+: F0⌝
```

Every caller has the two added premises: C5 (§3.2) certifies every log in the binding's state, and the
binding's leader logs are of terms in `S.leaders`.

**The term budget** (decision 2; gap 2). `budgetInv`, `termLB`, `tickCred`, `budget_spend`,
`budget_step`, `termLB_bound` are `InvNodeChan.lean`'s (internal) and `termLB_rb` is `TracedNodeRun`'s.
`RawNodeApi` re-exports them under sealed names over `Cluster` (as S3a's `Cluster.budget`):

```lean
@[no_expose] def rnBudget (γ : Cluster) : IProp GF := inv budgetN (budgetInv γ.budget)
@[no_expose] def rnTermLB (γ : Cluster) (t : w64) : IProp GF := termLB γ.budget t   -- persistent
theorem rnBudget_spend : rnBudget γ -∗ ⧗ 1 -∗ rnTermLB γ t ={E}=∗ ⌜uint.Z t + 1 < 2^64 - 1⌝ ∗ rnTermLB γ (t + 1)
theorem rnBudget_step  : rnBudget γ -∗ rnTermLB γ t1 -∗ rnTermLB γ t2 ={E}=∗ ⌜… < 2^64⌝ ∗ ∃ tb, rnTermLB γ tb ∗ ⌜max t1 t2 ≤ tb⌝
theorem rnTermLB_le, rnTermLB_rb   -- monotone; at most the receipts' bound
```

`raftState_open` (S3a) already hands the client `termLB γ.budget S.term ∗ inv budgetN (budgetInv …)`; it
is restated over the sealed names. The harness needs the budget for `Tick`'s premise `rs.term + 1 ≤ rs.tc`
(a campaign must not wrap the term) and for `Step`'s `st.msg.Term' ≤ rs.tc`: before each input it raises
the ceiling with `rawNode_raise_tc`, paying a time receipt for a tick (`rnBudget_spend`), and for a message
using the sender's `rnTermLB`, carried by the network invariant.

These live in a new module so that `InvNodeChan`/`InvNode*` are not edited (#22 edits them).

### 2.2 The strengthened specs (decision 1; gaps 3-8)

**Pattern** (the trace check's, `notes/trace-check-design.md` §3.1: "one proved spec per function"): each
function gets one new proof of a stronger triple over `ownRawNodeAt` (internal) / `rawNode` (API); **the
old spec, text unchanged, is its corollary** (`ownRawNode_eq_at` in, existential out). So `node__run*`,
`InvNodeRun`, the traced specs and every other caller of the old statements are untouched, and `Link.lean`
links the old name to the corollary.

The abstract effects, `Protocol/InputEnd.lean` *(new, pure, importable)*, static mode, over `PState`:

```lean
/-- (new) The end state of `raft.Step` on a protocol message `m` (static mode, pre-vote and check-quorum
off), as the code's paths are: the stale arm, the term preamble, then the role's handler. The rules'
right-hand sides are `StepC`'s (`Protocol/StepC.lean`), so `InputEnd s m s' → StepC* s _ s'`. -/
def RecvEnd (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  -- (revision 1, F1) a local message, term 0 (a forwarded `MsgProp`: `send` stamps no term on it):
  -- no preamble, as `StepEnd`'s `StaleMsg` (`m.Term' ≠ 0 ∧ …`)
  (m.term = 0 ∧ HandleEnd c id s m s') ∨
  (m.term ≠ 0 ∧ uint.Z m.term < uint.Z s.term ∧ s' = s) ∨                 -- ignored (no report)
  (m.term ≠ 0 ∧ ∃ s1, PreEnd s m s1 ∧ HandleEnd c id s1 m s')

def PreEnd (s : PState) (m : Msg) (s1 : PState) : Prop :=
  (uint.Z s.term < uint.Z m.term ∧ s1 = pbecomeFollower s m.term (if fromLeader m.ty then m.src else 0)) ∨
  (m.term = s.term ∧ s1 = s)

def HandleEnd (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  match m.ty with
  | .vote => (PCanVote s m.src ∧ plogUpToDate s.base s.log ⟨m.logterm, m.index⟩ ∧
               s' = psendMsgs { s with vote := m.src } [Msg.plain .voteResp id m.src s.term false]) ∨
             (¬ (…) ∧ s' = psendMsgs s [Msg.plain .voteResp id m.src s.term true])
  | .voteResp => if s.role = .candidate then
        let s2 := { s with votes := recordVote s.votes m.src (!m.reject) }
        (¬ JQuorum c (granted s2.votes) ∧ ¬ JLost c s2.votes ∧ s' = s2) ∨
        (JQuorum c (granted s2.votes) ∧ WinEnd c id s2 s') ∨
        (JLost c s2.votes ∧ s' = pbecomeFollower s2 s2.term 0)
      else s' = s
  | .app => if s.role = .leader then s' = s else AppEnd id (padoptLeader s m.src) m s'
  | .heartbeat => if s.role = .leader then s' = s else
        s' = psendMsgs { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
               [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }]
  | .appResp => if s.role = .leader then AppRespEnd c id s m s' else s' = s
  | .heartbeatResp => if s.role = .leader then SendsEnd id s s' else s' = s
  | .propose => ProposeEnd id s m.entries s'
  | _ => ∃ B r, StepC c id B s r s'                      -- outside the harness's inputs

/-- `appStale`, `appAccept`, `appReject`'s right-hand sides (`StepC`), exactly one. -/
def AppEnd (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop := …
/-- `becomeLeader`, the empty entry, the self-acknowledgement, the broadcast at the won state. -/
def WinEnd (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  ∃ mt ms, LeaderMatchOk id s mt ∧ (∀ x ∈ ms, AppOk id (pwinState id s mt) x) ∧
    s' = psendMsgs (pwinState id s mt) ([pselfAck id (pwinState id s mt)] ++ ms)
/-- Accepting: the sender's `Match` raised (`max`), then possibly a commit (`JQuorum (ackedBy …)` at an
entry of the term), then appends (`AppOk` at the state after the commit). Rejecting (review S3):
`Match` kept, probe appends (`AppOk`). An unknown sender: `s' = s`. -/
def AppRespEnd (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop := …
def SendsEnd (id : w64) (s s' : PState) : Prop := ∃ ms, (∀ x ∈ ms, AppOk id s x) ∧ s' = psendMsgs s ms
/-- A leader appends the batch stamped at its term, queues the self-acknowledgement and broadcasts; a
follower with a leader forwards; otherwise dropped. -/
def ProposeEnd (id : w64) (s : PState) (es : List EntryM) (s' : PState) : Prop := …

/-- A tick: nothing, a campaign (`HupOkC`'s election arm at `PState`), or a leader's heartbeats. -/
def TickEnd (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  s' = s ∨
  (s.role ≠ .leader ∧ id ∈ c.voters ∧ ∃ peers, peers ≡ₚ elements (c.voters \ {[id]}) ∧
     s' = psendMsgs (pbecomeCandidate id s)
            ([Msg.plain .voteResp id id (s.term + 1) false] ++
             peers.map (fun d => pvoteReq id d (s.term + 1) (plogLast s.base s.log)))) ∨
  (s.role = .leader ∧ ∃ ms, (∀ x ∈ ms, HeartbeatOk id s x) ∧ s' = psendMsgs s ms)

/-- `Advance`: the queued self-addressed messages `qs` (`rawNode`'s third index: a leader's
self-acknowledgement at its last index, a candidate's self-vote) stepped in order by `RecvEnd`; the
storage acknowledgements leave `PState` as it is (`AckEnd`, §2.4). -/
inductive AdvanceEnd (c : CfgM) (id : w64) : PState → List Msg → PState → Prop
  | nil (s) : AdvanceEnd c id s [] s
  | cons (s s1 s' q qs) : RecvEnd c id s q s1 → AdvanceEnd c id s1 qs s' → AdvanceEnd c id s (q :: qs) s'
```

`ReplOk`'s `SnapOk` disjunct is excluded from every send of these relations at a never-compacted node
(§2.5): `WinEnd`, `AppRespEnd`, `SendsEnd` and `ProposeEnd` say `AppOk`, which is `ReplOk` with that
fact.

`InputEnd` is not shaped by the binding: it is raft's step function at the protocol level, the same
content as `StepEnd` (which other clients, the trace check among them, already rely on), restated on
`PState`.

**The triples, old → new** (`rawNode` in the API form; `ownRawNodeAt` in the internal one). Between
inputs (after `Advance`) `qs = []` and `ps.outbox = []`; the new pre has `rawNode … rs ps []` where the old
had `ownRawNode … rs`, and the old premises unchanged.

| Function | Old post (today) | New post (adds) |
|---|---|---|
| `RawNode.Step` (`RawNode__Step.lean`) | `ownRawNode {rs with term := t, psnap}` ∗ term bounds | `rawNode {…} ps' []` ∗ `⌜RecvEnd c id ps (absMsg ty st.msg st.ents st.ctx) ps'⌝` (`mtypeOf st.msg.Type' = some ty`; `ps` the pre's) |
| `RawNode.Tick` | `ownRawNode {rs with term := t}` ∗ `t ≤ term + 1` | `rawNode {…} ps' []` ∗ `⌜TickEnd c id ps ps'⌝` |
| `RawNode.Propose` | `ownRawNode …` | `rawNode … ps' []` ∗ `⌜ProposeEnd id ps (stamped data) ps'⌝` (dropped: `ps' = ps`) |
| `RawNode.HasReady` | `b` and its idle facts | unchanged, `rawNode rs ps qs` in and out |
| `RawNode.Ready` | `ownRawNode {rs with …}` ∗ `hsOptC`, `entsROz`, `isRaftMsg`, `isCommitted (delivered ++ ce)`, … | `rawNode {rs with …} {ps with outbox := []} (ps.outbox.filter (·.dst = id))` ∗ `⌜ReadyOut id rs ps h es ms ce ss⌝` (below) |
| `RawNode.Advance` | `ownRawNode (advRS rs t ca)` | `rawNode (advRS …) ps' []` ∗ `⌜AdvanceEnd c id ps qs ps'⌝` (`qs` the pre's) |
| `NewRawNode.emptyStartSpec` (S3a) | `ownRawNode (rawNodeRestarted …)` | premise `cv.PreVote' = false ∧ cv.CheckQuorum' = false` (F6); `rawNode (rawNodeRestarted …) pInit []` with `pInit` term 0, vote 0, follower, empty log, commit 0, empty outbox |

`c` is the static configuration (`γ.reCfg`, the three voters).

**Where they live** (review S7). The layout gives a spec file one `<F>.spec`. The internal stronger
triples are `RawNode.<F>.absSpec` in a defs module `Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean`
*(new)*, each proved in its function's proof file (which then proves `RawNode.<F>.spec` as the corollary,
both linked); the API form (over `rawNode`, §2.1) in `RawNodeApi.lean`, proved in `RawNodeApiLinked.lean`.
`etc/api/raft-layout.txt` gets the defs module as a known exception if `--layout` flags it. `interface/`
regenerates for `raft.Step` (through `stepClose`, §2.4), `maybeSendAppend` (§2.5) and the new modules.

**The `Ready` binding** (gaps 3, 4, 6, 7): what the harness reports, as functions of the protocol state
at the call (`ps`) and the client's record `rs`:

```lean
/-- (new) A `Ready`'s fields against the node's protocol state at the call. -/
def ReadyOut (id : w64) (rs : RNState) (ps : PState) (h : HardStateM) (es ce : List EntryM)
    (ms : List QMsg) (ss : Option (w64 × StateType)) : Prop :=
  -- the role it reports is the node's (`softStateIs`, `Hrole`)
  roleAfter rs.role ss = roleGo ps.role ∧
  -- the hard state after it is the node's term, vote and commit (`phsNext`, `PhsOk`)
  phsNext rs.phs h = ⟨ps.term, ps.vote, ps.commit⟩ ∧
  -- the durable state the write makes is the node's log (`durTie`, `readyDurable`): entries `es`
  -- appended at `es[0].Index`, the log afterwards `ps.log` (no snapshot: `ps.base = base0`, §2.5)
  (readyDurable rs.dur (phsNext rs.phs h) none es).ents = ps.log ∧
  (∀ e0 ∈ es.head?, ps.log.drop (uint.nat e0.Index' - 1) = es) ∧
  -- the messages are the outbox's, but those to the node itself (`rawNode`'s new `qs`)
  (ms.map (fun q => absMsgOf q.st)) ~ ps.outbox.filter (·.dst ≠ id) ∧
  (∀ q ∈ ms, q.st.msg.To' ≠ id ∧ q.st.msg.To' ∈ voters) ∧
  -- the committed entries are the log's, after those delivered, up to at most the commit index
  rs.delivered ++ ce <+: ps.log ∧ (rs.delivered ++ ce).length ≤ uint.nat ps.commit
```

`roleGo`, `absMsgOf` are *(new)* names for the existing readings (`Role` as `StateType`; `absMsg` at the
message's type). A `Ready` with nothing to hand out leaves the predicate as it was; the harness's boot drain
has none (`HasReady` is false at a fresh node: `prevHardSt = emptyState` and no entry, message or soft
state change; review S9).

**Old statements kept.** Every old `RawNode.*.spec`, `readyWithoutAccept.spec`, `acceptReady.spec`,
`NewRawNode.restartSpec`/`emptyStartSpec`: text unchanged, now corollaries. No closed theorem's statement
changes. The `RaftTla/`, `RaftNoAx/` and `KvNet/` copies are regenerated by their scripts
(`etc/gen-raft-tla.py`, `etc/copy-part.py`).

### 2.3 Which ghost state carries what (gap 5)

The binding variable, the raft fact the refinement reads it from, and where it is today:

| binding (B 44-54, R 89-116) | raft side | today |
|---|---|---|
| `currentTerm[n]`, `Vote(n)`, `log[n]`, `commitIndex[n]` | `rs.dur : RaftState` after the write = `ps.term`, `ps.vote`, `ps.log`, `ps.commit` (`ReadyOut`) | `durTie`, `PhsOk` in `ownRawNode`; not exposed |
| `role[n]` | `roleGo ps.role` = the reported soft state | `Hrole` (`rs.role = sv.RaftState'`) |
| `lastApplied[n]` | `rs.delivered.length` | exposed |
| `confirmed[n]` | the binding's own (§3.2 C3); raft: `ackAgree`/`acksOk` | not needed outside |
| `msgs`: vote requests | `isMessage(.vote)` = `isCamp` + `plogLast` | carried by every message (`isRaftMsg`) |
| `msgs`: grants | `isMessage(.voteResp, ¬reject)` = `isVote` | same |
| `msgs`: acks | `isAcked`/`ackIn` in `isMessage(.appResp)` | same |
| `votes` | `isVote` (`rawNode_vote`) | `VoteHistOk`, vote table |
| `leaders` | `isLeader` (`rawNode_leader`) | `leaderWit` |
| `ledLog[t]` | the leader's `ps.log` at its last report; its start `isCamp` | `leadLogOwn` |
| `chain`, `termLen` | `isCommitted`, `commitIn` (`rawNode_commit`) | `ownLogGhost` |
| `config`, `confAt`, `ledConf`, `ledAt`, `elAt` | constant: `InitConf`, `0` (static, no conf entry) | scope |
| `pending`, `undo`, `queue`, `reads` | the stream's shape only (§3.2 C4) | — |

### 2.4 The first change inside raft's step proofs: `StepEnd` unconditional

`stepClose`/`stepCloseAt` (`LemmasStepGates.lean:712-732`) take `⌜s.gh.tr.isSome → StepEnd c id m ents
ctx s s'⌝`; they take `⌜StepEnd c id m ents ctx s s'⌝` instead. `raft.Step.spec`'s text changes by that
definition (a weaker precondition: the caller's closing wand gets more).

`AckEnd` (the storage acknowledgements' end state: protocol reading unchanged) becomes
`⌜s.gh.tr.isSome ∨ AckScope c m sn → AckEnd m s s'⌝`, with `AckScope` the untraced scope that gives it
(review S2): no snapshot in the acknowledgement (`sn = none`) and no automatic leave (`c.autoLeave =
false`, true of a static, non-joint configuration). Its two sources change: the `MsgStorageAppendResp`
path's post already has it outright (`raft__Step/MsgStorageAppendResp.lean:98`); the
`MsgStorageApplyResp` path's post (`raft__Step/MsgStorageApplyResp.lean:194`, `⌜s.gh.tr.isSome → …⌝`)
gets `AckScope`'s disjunct, from its own `appliedTo` premise (the automatic leave runs only at
`c.autoLeave`). The snapshot-acknowledgement close (`raft__Step.lean:1077`) discharges it by `sn ≠ none`.

- **Consumers** (the close sites that apply the wand): `gate_close`, `gate_close_g`, `gate_close_mid`
  (`TracedStepGates.lean`) and their 21 applications in `raft__Step.lean` (review S1), which pass `(fun _
  => Hend)` or `(by end_ty)` (one macro, `raft__Step.lean:95`): drop the `fun _ =>` (in the macro once).
- **Providers** (the families' closing wands): the untraced wands (`RawNode__Step`'s, the
  tick/propose/advance callers', `node__run*`'s) ignore the premise and are unchanged; the traced bundle
  files use it as `(hend (by rw [htr]; rfl))` at about 50 sites in 25 files (`TracedRaftStep*.lean`):
  becomes `hend`. Mechanical.
- `RaftTla/`, `RaftNoAx/`, `KvNet/` copies regenerated.

Not touched: `InvNode*`, `node__run*` (#22), `stepLeader`/`stepFollower`/`stepCandidate`, every
`InvRawnode*`; of the `raft__Step/*` path files, only `MsgStorageApplyResp.lean`'s post.

**Alternatives considered** (Q1): (b) a new post on `raft.Step.spec` itself (`"%Hend" ∷ ⌜StepEnd …⌝`):
every caller that destructures the post by position breaks, more sites than (a); (c) gate families that
record the events at each hook gate (the trace check's mechanism without a trace): no change to
`raft.Step` at all, but every gate's obligation re-proved for the recording family (about 20 gates; the
traced bundle is 15k lines for its families), and the gates give the states at the events, not the end
state, so `InputEnd` would still need the close.

### 2.5 The second change: no snapshot at a never-compacted node (revision 1, F3)

**The gap.** Every broadcast `StepEnd` describes is `ReplSends` (`Defs.lean:1584`): `ReplOk = AppOk ∨
SnapOk`, with `m.ty = .snap → s.gh.ns = false`, and `NGhost.ns` is `false` at every node since U8 v2
(`Defs.lean:1140`). So nothing proved says a leader of the harness's cluster sends no `MsgSnap`; and a
`MsgSnap` reaching a follower gives it a snapshot `Ready`, on which the harness panics (`harness.go`
`drain`), with `ps.base ≠ base0` and C1 broken. Raft's Go sends none: the harness never compacts its
`MemoryStorage`, whose first index stays 1 with the dummy entry at 0, and a leader's `Next ≥ 1`
(`PrOk`), so `term(Next - 1)` and `entries(Next)` never fail and `maybeSendSnapshot` is never reached.

**The argument exists**, at traced nodes: `maybeSendAppend.spec` takes `TrNoSnap s.gh.tr s.logst`
(`TracedSend.lean:45`: at a traced node, a compacted log, `prev.index ≠ 0 ∨ storPast storage 1`, is a
contradiction), and its proof refutes the snapshot fallback with it.

**The change.** A node-level flag for "my storage is never compacted" (the client's promise, as
`storCapF st 1` is for the old no-snapshot mode), set at construction and kept:
- `NGhost.nc : Bool` *(new)*; `ownRaftPhys` holds `⌜nc = true⌝ → storCapF st 0` (the storage's floor
  stays 0: never compacted), as `NsCap` holds `storCapF st 1` for `ns`;
- `TrNoSnap tr ls` becomes `NoSnapIf (tr ≠ none ∨ nc = true) ls` in `maybeSendAppend.spec` (and its
  callers' threading of it, `TrNoSnap`'s users: `bcastAppend`, `sendAppend`, the win, `stepLeader`'s);
- `ReplSends`' clause `m.ty = .snap → s.gh.ns = false` gains `∧ s.gh.nc = false`;
- `NewRawNode`'s start spec takes the storage's floor-0 cap (the harness's `bootStorage` over a
  `MemoryStorage` it never compacts gives it) and sets `nc`; `rawNode` exposes it as `rawNode_noCompact`:
  every message the node queues is no `.snap`, so `ps.base = base0` and `ps.log` is the whole log.

**Cost and risk.** `NGhost` is in `Defs.lean`: adding a field with a default rebuilds all of raft and its
clients once, but no statement that builds an `NGhost` by a literal breaks (defaults). The proofs touched:
`maybeSendAppend` (the refutation is the traced one, its premise widened), the threading of
`NoSnapIf` (where `TrNoSnap` is threaded today), `ReplSends`' producers (they already prove the `ns`
clause from `PrvalsOk`'s `PrOkN`; the `nc` clause from `maybeSendAppend`'s post), `ownRaftPhys`'s new
conjunct (kept by every step: the flag is constant, the storage's cap persistent). Estimated 800-1,500
lines, and the most uncertain item of S3c: a **probe first** (Q7), proving `maybeSendAppend`'s widened
spec before anything else. Alternatives: (b) the harness handles snapshots (the binding has `snap` and
`restore`; S2 and S3b change, and §4's risk 6 of `antithesis-check-design.md` applies); (c) revive
`ns` (its machinery, `PrLo`'s `Next ≥ 2`, is for a bootstrap log and would need `Next ≥ 1` for an empty
one).

---

## 3. The refinement

### 3.1 Abstractions (gap 5)

Over the S3b transcription's types (`AntCheck`, `Tla/Types.lean`): `Str`, `Entry`, `Msg`, `Event`,
`State`, `Config`. Each mirrors the harness's Go (`harness.go`), which the S4 proof will show the harness's
reports are:

```lean
def nameOf (id : w64) : Str                  -- "raft<id>", "" for 0 (harness `Name`)
def entOf (e : EntryM) : Entry               -- noop for empty data, command with the data (entryOf)
def logOf (l : List EntryM) : List Entry := l.map entOf
def msgOf (m : Msg) (to : w64) : AntCheck.Msg   -- every field present (harness msgOf, `MFAll`)
def roleOf (r : Role) : Str                  -- follower / candidate / leader
def cfg3 : AntCheck.Config := { server := names 3, initVoters := names 3, bootstrapped := false }
```

`entOf` is injective on equal terms and indices only through the data (the entry's value is its data),
which is what the binding's `Matching` compares (B 132-134): two entries at the same index and term are
equal as `EntryM` by `logRecs_agree`, so equal as `Entry`.

### 3.2 The relation

`AntSim (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg)`, where `NodeView` is a node's
`(rs, ps)` **between inputs** (after `Advance`, `qs = []`; revision 1, F5: not at its last report, since
inputs change `ps` without a report: a grant that does not win changes `votes`, an `appResp` without a
commit changes `matched` and may send appends with no `ready`, a message causing nothing is never
reported) and `net` the messages sent and not yet received. Pure, except C5, which the harness holds as
persistent ghost facts and turns into the pure `GlobalOk` before each lemma.

- **C1 the per-node durable part** (between inputs the node has no unwritten state: every change of its
  term, vote, log, commit or role is in a `Ready` (`ReadyOut`), whose `ready` report the harness makes
  before its write, and the drain runs until `HasReady` is false):
  `S.currentTerm[n] = ps.term`, `S.vote n = nameOf ps.vote`, `S.log[n] = logOf ps.log`,
  `S.commitIndex[n] = ps.commit`, `S.role[n] = roleOf ps.role`, `S.lastApplied[n] = rs.delivered.length`,
  `ps.outbox = []`, `ps.base = base0`, `S.config[n] = InitConf`, `S.confAt[n] = 0`.
- **C2 the leader's part**: if `ps.role = .leader` then `(n, ps.term) ∈ S.leaders`,
  `S.ledLog[ps.term] = logOf ps.log`; for every voter `j`, `matchOf ps j ≥ k` with `TermAt k = ps.term`
  gives an ack fact `(j → n, ps.term, ≥ k)` in `S.msgs`, and `matchOf ps j = 0` or an ack of `j` at
  `ps.term` or `j = n` below the election's last index (`LeaderMatchOk`).
  The candidate's part: `granted ps.votes ⊆ S.granted n` (`Granted`, R 277).
- **C3 the binding's own invariants** (facts about `S` alone, kept by every step and by `GC`):
  `chain` extends monotonically and every `termLen` value is at most `|chain|`; every ack fact `a` from `n`
  at `S.currentTerm[n]` has `a.index ≤ S.confirmed[n].index` with `S.confirmed[n].term = a.term`, or
  `a.index ≤ S.commitIndex[n]`; `S.confirmed[n] = (t, k)` gives `S.log[n][1..k] = S.ledLog[t][1..k]` while
  `t ∈ DOMAIN S.ledLog`; `DOMAIN S.ledLog ⊆ {t | ∃ l ∈ S.leaders, l.term = t}`;
  `S.commitIndex[n] ≤ |chain|` and `chain[1..commitIndex[n]] = log[n][1..commitIndex[n]]` (review S4:
  the transcription's `subSeq` is an evaluation error past the end, `Types.lean:143`, and
  `CommittedEntriesPreserved` and `ApplyEv` evaluate it);
  `S.viol = []`, `S.undo[n] = none` after a `send`/`apply` and `some p` with `p.made = false` only right
  after a `ready`; `S.queue[n] = []`, `S.reads[n] = []`.
- **C4 the network**: every `m ∈ net` was recorded by a `send` (of `m.src`, but a `prop` a follower
  forwards again keeps its first sender's `From`, review S5: the binding checks nothing of a `prop`,
  B 524, 586) (so `SendableIn` held then for a request, B 546), with `S.currentTerm[m.src] ≥ m.term` and the facts it made in `S.msgs` (a grant's, an
  ack's), and carries `isMessage γ m` and `rnTermLB γ m.term`.
- **C5 `GlobalOk`, raft's global facts about everything in `S`** (from §2.1's laws and agreement laws, at
  each report): every log in `S` (`log[·]`, `ledLog[·]`, `chain`, every request's entries) is
  `logRecs`-certified, so any two are `Matching` (B 132); `chain` and every node's committed prefix are
  `isCommitted`-certified, so comparable; `(j, t) ∈ S.leaders → isLeader γ j t`; `(v, t, c) ∈ S.votes →
  isVote γ v t c`; `termLen[x] = c` → `commitIn γ chain c x`; each `ledLog[t]` starts with an `isCamp`
  log. Hence `ElectionSafety`, `OneVotePerTerm` (R 581-586), and with `commitIn_camp`, leader completeness
  for every `t > x`.

### 3.3 The per-report lemmas (one per report kind, plus `GC`)

Each is pure: `AntSim S V net ∧ GlobalOk … ∧ <raft's facts for this report> → ∃ S', S.step ev = .ok (some
S') ∧ violated S' = [] ∧ AntSim S' V' net'`, with `ev` the report the harness makes. `S.step`, `S.gc`,
`violated` are the S3b transcription's (`Tla/Binding.lean`, `Tla/Check.lean`). Proved by evaluating the
transcription's guards (each `EvalM` guard `= pure true`, no `evalError`: every field the harness sets is
present, every index in range).

| lemma *(new)* | report | raft facts it takes | binding (B) | proved from |
|---|---|---|---|---|
| `antSim_init` | (none) | `NewRawNode.emptyStartSpec`'s `pInit` ×3 | `Init0` (B 755) | definitions |
| `antSim_boot` | `boot` | `pInit` | `Boot` (162-194): `Recovered` with term 0, vote `""`, commit 0, `lastIndex 0`; voters `names 3`, `outgoing []` | C1 |
| `antSim_recv` | `recv m` | `m ∈ net` | `Recv` (199-204): `m.to = n`; a request of a term ≥ `currentTerm[n]` is `Sendable` | C4 and monotonicity of `leaders` (GC drops only `Over` terms, B 721), `ledLog` (appends only), `chain`/`termLen` (C3) |
| `antSim_quiet` *(revision 1, F5)* | none: an input, a `Ready` with no `ready` report (only `send`s and `apply`, or nothing), `Advance` | `InputEnd`/`ReadyOut`/`AdvanceEnd` with no change to C1's fields | — | C1 unchanged; C2 by the same facts as `antSim_ready`'s (new acks, grants) |
| `antSim_ready` | `ready` | `InputEnd` (or `AdvanceEnd`, a drain's later `Ready`) from the `NodeView`'s `ps₀` to `ps₁`; `ReadyOut` at `ps₁`; the handled message when `by = recv` | `Ready` = `InMemory` (213-275) + `OnDisk` (290-436) | below |
| `antSim_send` | `send q` per message of the `Ready` | `ReadyOut`'s `ms` and `InputEnd`'s queued messages | `Send` (510-593) | below |
| `antSim_apply` | `apply` | `ReadyOut`'s `ce` | `ApplyEv` (598-609) | C1, C5 (`chain` and the log agree to the commit) |
| `antSim_gc` | (GC, any time) | none | `GC` (713-723) | C2-C4 never name garbage: grants and acks to a node at their term (B 699, 701), the largest ack (702), vote requests and votes of a term some node is still in (698, 708), leader logs of a term some node is still in (709) |

**`antSim_ready`, guard by guard.** Let `T0 = ps₀.term`, `T1 = ps₁.term`, `m` the handled message.

- `InMemory.ok` (231-253): `wins` comes only from `WinEnd` (a vote response at a candidate): `role[n] =
  Candidate` (C1, reported at the campaign's `ready`), `currentTerm[n] = T` (the campaign's write),
  `T ∉ DOMAIN ledLog` (C3: else `(j, T) ∈ leaders`, `isLeader γ j T`, `isLeader γ n T` from
  `rawNode_leader`, so `j = n` by `isLeader_unique`, and `n` leading `T` before then being a candidate at
  `T` contradicts `TermsOk`/`PreEnd`), `IsQuorum(Granted(n), config[n])` (C2: the tally's grants were
  delivered, so recorded by their senders' `send`s; the self-vote by the campaign's write),
  `OneWaiting`/`confAt` (no conf entry). `leads → c ≤ Len(L)` (`rawNode_wf`, C2). `app` (a leader's new
  entries, `WinEnd`/`ProposeEnd`): `first = Len(ll1[T]) + 1`, all of term `T`. A leader's commit `c`:
  `cmt` (a new commit to an entry of `T`, `AppRespEnd`'s `JQuorum (ackedBy …)`) needs
  `IsQuorum(Acked(n, T, c))` (C2's acks); otherwise `RecordedIn(chain, termLen, L, c, T)` (C3, C5).
- `OnDisk` (361-436): term: `T1 ≥ T0`; `T1 ≠ T0 → ro[n] ≠ Leader` (a term change then a win in the same
  input needs a quorum of grants in the new term from one input: impossible with three voters, the tally
  being reset by the term change; `RecvEnd`'s vote-response arm records one vote); `elect` only from
  `TickEnd`'s campaign (`T1 = T0 + 1`, vote `n`); `adopt` only from `PreEnd` (`m.term = T1`, and its
  sender's `currentTerm ≥ T1` by C4). Vote: a changed vote is `TickEnd`'s self-vote or `HandleEnd`'s grant
  (`PCanVote` gives `V1 = Nil`; `VoteFact(m) ∈ msgs` by C4 and C1 at the candidate's campaign;
  `UpToDate` is `plogUpToDate` on `log[n]` = `ps.log`). Entries: a follower's `AppEnd`/`appAccept` gives
  `es` = the request's entries from the first conflict (`plogMaybeAppend`/`plogFindConflict`), which is
  B 384-388 (`PrevOk`, `HasFirst`, the conflict or the end); a leader's are appended at its end and
  `Sendable` from `ledLog[T]` (C2). Commit: a follower's moves only by `appAccept` (to
  `min(m.commit, lastnewi) ≤ m.commit`, the request `Sendable` by C4) or `heartbeat`; a leader's by
  `AppRespEnd`. Safety: `CommitSafety`, `LogMatching`, `CommittedEntriesPreserved` by C5;
  `LeaderCompleteness` by `commitIn_camp`; `CommitBeyondConfirmed` (435) by C3: an `app` commits within
  its own `last`, which the write's ack confirms; a heartbeat's commit is at most the leader's
  `matchOf ps j` (`HeartbeatOk`), at most an ack of `n` at `T1` (C2), which is either confirmed (C3) or at
  most `n`'s commit (then `adv` is false).
- The new `S'` satisfies C1-C3 at `ps₁` with `outbox` emptied by the `Ready`.

**`antSim_send`, by type** (530-593). `vote`: `s.term = currentTerm[n]` and `VoteFact(s) ∈ msgs` (the
campaign's write in the same `Ready`). `voteresp` granted: the vote in `votes` (the same `Ready`'s write,
or an earlier one: not `OldVotes` at the node's term). `app`/`hb`: the node leads its term (C1) and the
request is `Sendable` from `ledLog[T]` (C2), with its commit recorded (C3, from `AppOk`'s `m.commit ≤
s.commit`/`HeartbeatOk`); messages of an older term cannot be in the `Ready` (`InputEnd` queues only at
the state after the preamble, and the outbox was empty at the input, C1). `appresp` accepting: the
handled message `C[1] = pending[n]` (the `recv` of this drain), its fact `Sendable`, then `Ack`
(`PrevOk`, `HasFirst` on `log[n]` after the write) or `AckCommitted` (`appStale`: index = `commitIndex[n]`,
`prevLogIndex < commitIndex[n]`). `hbresp`: `currentTerm[n] ≤ s.term`. `prop`: no check. `s.to ≠ n` and
a server, `s.from = n` but for a re-forwarded `prop` (`ReadyOut`).

**A drain's later `Ready`s** (after `Advance`, reported with the drain's `by` and, for `recv`, the same
`pending[n]`): `AdvanceEnd` from the state after the previous `Ready`. Its term is the written one (no
`elect`/`adopt`), a follower's commit does not move (the storage acknowledgements keep `PState`), so
`OnDisk`'s message-dependent guards (`moved`'s `hasM`) are not reached for a follower; a leader's are its
own (`leads`).

### 3.4 Where the Iris is

The lemmas of §3.3 are pure. The harness (S4) holds, in the recorder's invariant, `AntSim` and the
persistent facts behind `GlobalOk` for everything in `S` (`[∗ list]` over `S.leaders`, `S.votes`, the
logs), and each node goroutine holds its `NodeView` fragment (ghost variable, the invariant the other
half). At a report it: opens the invariant, reads the new raft facts out of `rawNode` (§2.1's laws),
derives the pure `GlobalOk` for `S` plus the new items (agreement laws, `commitIn_camp`), applies the
lemma, records the new facts, closes. This keeps the refinement independent of Iris and testable by
`decide` on small states.

---

## 4. Where the refinement could be false, and the evidence

Every guard the harness's reports reach, with the raft fact that discharges it and the risk:

| guard (B) | raft fact | risk |
|---|---|---|
| `Boot`'s `Recovered`, `SameConf` (169, 194) | empty storage, voters `1,2,3` | none (S3a's `emptyStartSpec`) |
| `Recv`'s `Sendable` (203) | sent requests stay sendable | low: monotonicity of `S` (C3) |
| `wins`: `T ∉ DOMAIN ledLog` (237) | election safety, one win per term | low |
| `wins`: `IsQuorum(Granted)` (238) | tally only from delivered grants | low |
| `cmt`: `IsQuorum(Acked)` (252) | `Match` only from delivered acks; own `Match` at the win below the term's entries | low |
| `T1 # T0 => ro[n] # Leader` (365, "no new term while leading") | a win needs a quorum of grants received after the term change | **true only in scope**: false with `AsyncStorageWrites` (their own targeted stream `leader-new-term-write`) or a single voter |
| `adopt`: another node at `T1` (368) | a message's term is written by its sender before the send | low (sync harness) |
| `voted`: `V1 = Nil`, `VoteFact ∈ msgs`, `UpToDate` (370-372) | `PCanVote`, `isCamp` | low |
| follower `stores` (380-388) | `plogMaybeAppend`, `Ready.Entries` = the appended suffix | low |
| `moved`: `w.commit ≤ f.commit` (396) | `commitTo(min(m.commit, lastnewi))` | low |
| `CommitBeyondConfirmed` (435) | heartbeat commit ≤ `Match` ≤ an ack of the node in the term | **medium**: needs that `Match` is reset at the win (`reset`: 0 but self) and moved only by acks of the term; an ack by `AckCommitted` does not confirm, but then the commit cannot advance past it. The model's own "deliberate difference" (R 431-439) |
| `LeaderCompleteness` (268-271, 428) | `lc_core` | low; the cost is `commitIn_camp` (§2.1) |
| `LogMatching`, `CommitSafety`, `CommittedEntriesPreserved` (427, 430-433) | `logRecs_agree`, `isCommitted_agree` | low |
| `Send`: `s.term = currentTerm[n] ∧ role[n] = Leader` (545) | no message of an older term in a `Ready` | low, but only through `InputEnd` (not `StepC*`: §0) |
| `Send appresp`: `Ack` or `AckCommitted` (571-580) | `handleAppendEntries`'s two accepting answers | low |
| `ApplyEv` (600-607) | committed entries after the write, within the commit | low (`applyUnstableEntries`: the write precedes the `apply` report) |
| `GC` (696-723) | nothing needed is garbage | low (§3.3) |
| `ElectionSafety`, `OneVotePerTerm` (R 581-586) | `isLeader_unique`, `isVote_agree` | none |
| (no report kind) the harness's own `panic` on a snapshot `Ready` and on a non-normal entry | no `MsgSnap` (§2.5); every entry normal (`rawNode_entries`) | **true of the Go, not yet provable** (revision 1, F3): needs §2.5's change; the entry types need the harness to propose normal entries only (S4) |

**Evidence.** S2's 1,500 runs (`-race`, five schedule variants, about 1.3k-1.6k reports each, terms up to
about 11, 3-4 leaders a run) and the 720-stream simulator batch: all accepted by the Go checker and by TLC.
The targeted negative streams (37) show the two rules above can be broken by raft outside the scope
(`leader-new-term-write` needs a campaign queued before a win with asynchronous writes), which is why the
proof leans on the scope there. No run hit a rejection, so nothing went to `issues/`.

**A proof-only risk** (not a falsity): the abstract `StepC*` admits chains the binding rejects (§0). The
refinement must use `InputEnd`, which is why §2.4 exists.

---

## 5. What the trace check's simulation gives

`TraceSim*` (`Proof/go_etcd_io/raft/v3/`, 56k lines with the traced step files) simulates upstream raft's
`etcdraft.tla` from **inside** raft: the specification's state rides in raft's ghost state (`simInv`), each
`RawNode` carries a trace capability (`rnTrace` in `ownRawNode`), and the hooks' gates (`stepGates`,
families `R`, the traced bundle) re-prove every step path against the specification at each event, in the
`with_tla` build (`RaftTla/`). That was possible because the hooks fire at each event; it is why the
bundle is 15k lines.

Here the harness runs raft's main build (no hooks, decision 2 of #33), and the simulation is **outside**:
relation `AntSim` at report boundaries, kept from the `RawNode` posts. What carries over:

- **`StepEnd`** and the callee result predicates it is made of: the exact end state per path (§2.4) is
  the trace check's work, reused as is.
- the abstraction pattern (`roleAbs`, `entAbs`, `logAbs`, `msgAbs`, `TraceSim.lean`) and the converter
  discipline (`evConv` mirrors the Go converter): §3.1 mirrors `harness.go`'s `entryOf`/`msgOf`.
- `SimServerR`'s shape (a node's `PState` against its server in the specification) is C1.
- the harness design (one recorder lock, network as goroutines, the ordering argument):
  `notes/antithesis-check-design.md` §9 already reuses it; S4 can follow `RunConcurrent`'s proof.
- pure log lemmas in `TraceSimLemmas`/`TraceSimFacts` (`plog*` against list indexing) where they apply.

What does not: the traced capability, `rnTrace`, the gate families and the bundle (no hooks), `TraceSimBag`
(the binding keeps lists and sets, not bags), the `etcdraft.tla` transcription (a different model).

---

## 6. Size and order of work

Order, each step keeping every existing result proved:

0. **Probe** (revision 1): `maybeSendAppend`'s spec with `NoSnapIf (tr ≠ none ∨ nc)` (§2.5), proved, and
   its threading listed, before anything else lands: it is the least certain item.
1. `stepClose` unconditional and `AckEnd` under `AckScope` (§2.4): `LemmasStepGates`, `TracedStepGates`,
   `raft__Step.lean` (21 sites, one macro), `raft__Step/MsgStorageApplyResp.lean`'s post, the traced
   bundle's `hend` sites; regenerate the copies. About 200 changed lines.
1b. The no-compaction flag (§2.5): `NGhost.nc`, `ownRaftPhys`'s cap, `NoSnapIf`'s threading, `ReplSends`'
   clause, `NewRawNode`'s start. 800-1,500 lines.
2. `Protocol/InputEnd.lean`: the definitions and `StepEnd → InputEnd` lifting lemmas (one per type, from
   the callee results on `NState` to `PState`, reusing the existing `rframe_*`/`stepC_*` lemmas that build
   `StepCD` from the same results). 1,200-1,800 lines.
3. `ownRawNodeAt` (with `qs` and the scope conjunct) and its two entailments; the new proofs of `RawNode.Step`, `Tick`, `Propose`, `HasReady`,
   `Advance` (the queue loop: the traced `Advance` took 2.6k lines; the untraced one with `ps` should be
   well under), `readyWithoutAccept`/`acceptReady`/`Ready` (`ReadyOut` from `durTie`, `PhsOk`, `Hrole`,
   the outbox and `pendList`), `NewRawNode`'s start; the old specs as corollaries. 3,000-4,500 lines.
4. `RawNodeApi.lean`: `rawNode`, the laws, `commitIn_camp`, the budget re-exports; the API-form specs and
   their linking module; `etc/api/raft.txt`, `interface/`. 800-1,500 lines (`commitIn_camp` is most of the
   uncertainty).
5. The refinement (§3): `AntSim`, `GlobalOk`, the lemmas; on top of S3b's `AntCheck`. 5,000-8,000 lines,
   most in `antSim_ready` and the guard-evaluation lemmas over the `EvalM` transcription.

**Estimate: 11,000-18,000 lines for S3c**, raft side 6,000-9,500 (§2.5 included), refinement
5,000-8,500 (`antSim_quiet` and C3's commit-chain invariant added). S4 (harness,
closed theorem) comes after and is not counted. Builds go through `/shared/tmp/build-slot.sh`; step 1
rebuilds raft's step proofs and everything above (the server, the examples), so it lands first and alone.

---

## 7. Questions for the user (each with a recommendation)

**Q1. How the posts learn each input's exact effect.** (a) Make `StepEnd` unconditional at
`raft.Step`'s closing wand (§2.4): one definition, 21 consumer sites (one macro) and ~50 mechanical provider sites in
the traced bundle, `RaftTla/` regenerated. (b) A new conjunct in `raft.Step.spec`'s post: more callers
break. (c) Recording gate families, no change to `raft.Step`: about 20 gate obligations re-proved, and
still not the end state. **Recommend (a).**

**Q2. Where the refinement lives.** (a) In the antithesis example's tree
(`Proof/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Sim*.lean`), using only raft's API
module: the API is then tested by a real client. (b) In raft's tree, like `TraceSim`. **Recommend (a).**

**Q3. Branches.** The refinement needs S3b's `AntCheck` (on `antithesis-check`). (a) Steps 1-4 on
`antithesis-rawnode-spec`, landed on their own; step 5 on a branch from `lean` after S3b's transcription
lands (or merging `antithesis-check` read-only). (b) Merge `antithesis-check` into this branch now.
**Recommend (a)**: steps 1-4 are raft's API and useful without the example; they also carry the build
cost of step 1, which should not wait on S3b.

**Q4. What the API exposes.** (a) The protocol state `PState` as it is (already importable), with
`InputEnd`/`ReadyOut` over it. (b) A slimmer client record (term, vote, role, log, commit), with copies of
the protocol functions over it. **Recommend (a).**

**Q5. Leader completeness.** (a) A new raft law `commitIn_camp` from `lc_core` (§2.1). (b) Re-prove the
model's own `LeaderCompleteness` from the binding's history (`S` alone), as Antithesis's TLAPS/Veil proof
does. **Recommend (a)**: raft has the argument; (b) is a second proof of the same theorem over another
model.

**Q6. The old `RawNode` statements.** (a) Kept, text unchanged, as corollaries of the new proofs (the
trace check's rule). (b) Replaced by the new ones, every caller updated (`node__run*`, which #22 edits).
**Recommend (a).**

**Q7. Excluding snapshots** (revision 1, F3; §2.5). Nothing proved today says the harness's leaders send
no `MsgSnap`, and the harness panics on one. (a) A no-compaction flag at raft's level (`NGhost.nc`), the
traced proof's `TrNoSnap` argument made available untraced, the client promising never to compact
(`storCapF st 0`); probe first. (b) The harness handles snapshots (`snap`/`restore` reports): S2 and S3b
change, and the binding's known divergence on a snapshot's configuration is near. (c) Revive the old `ns`
mode, whose `Next ≥ 2` machinery is for a bootstrap log. **Recommend (a)**, after the probe.
