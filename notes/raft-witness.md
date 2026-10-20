# Witness support in raft (etcd-io/raft#133)

Branch `raft-witness` (this repository), fork branch `raft-witness-goose-lean` of
`upamanyus/etcd` (raft). Started 2026-10-19.

## What #133 is

etcd-io/raft#133 proposes an "extended Raft" for clusters of regular servers plus at most one
*witness*: a voter that keeps no log, only a little metadata (term, vote, and the replication
set, term and subterm of the last entry it was told about), so that it can be a storage object
(a file on a share, a cloud blob updated by compare-and-swap). The design and an informal proof
are in the paper the issue links (github.com/joshuazh-x/extended-raft-paper, `proof.tex`); its
TLA+ spec (`algo/extended-raft.tla`) is a draft that does not type-check (`witnessSubterm` is
never initialised, `InitLeaderVars` sets per-server variables to scalars), so "checked with TLC"
is not of that file. The implementation is etcd-io/raft#168 (draft, "needs rebase", Feb 2024);
`notes/pr-verify/raft-168.md` on branch `pr-verify/raft-168` verified its quorum/tracker/confchange
parts on witness-free configurations and found four crashes.

The algorithm:
- Every entry carries a *subterm*. A leader starts subterm 0 at election (its replication set
  then excludes the witness) and a new subterm, with an empty entry, whenever it changes its
  *replication set*: the configuration minus one voter (the witness, or a regular voter it
  considers down). (term, subterm) names one replication set.
- Replication to the witness: when quorum−1 regular members of the replication set acknowledge
  an entry of the current term and subterm, the leader sends the witness (term, subterm, index,
  replication set); the witness stores them (if newer than its own) and acknowledges. Later
  entries of the same subterm are acknowledged on the witness's behalf without a write
  (*shortcut replication*; in #168, the witness proxy answers from its cached state).
- Votes: a candidate asks the witness only when one vote short; the witness grants if the
  candidate's last (term, subterm) is newer than its own, or equal and every responder so far is
  in the stored replication set.

## The Go code (fork branch `raft-witness-goose-lean`)

#168 rebased onto the pinned raft (`raft37-goose-lean-a1`, `c8217eb9`) as one commit (the
conflict resolutions of `pr-verify/raft-168`), then:
- **A cluster without a witness behaves exactly as v3.7**: the leader starts a new subterm on a
  conf change only if the old or new configuration involves a witness; the log lines are v3.7's;
  v3.7's tests and datadriven testdata pass unchanged (they were rewritten by #168). This is what
  lets the existing proof carry over with a "no witness" premise.
- `ApplyConfChange` keeps v3.7's signature (#168 made it return an error).
- The four crashes of `pr-verify/raft-168` fixed: `makeWitness` re-adds a tracked witness to
  the incoming config (Restore of a joint config keeping the witness); `raftLog.subterm`
  replaces the panicking `entry`/`lastEntry` (a candidate whose log ends at a snapshot reports
  subterm 0, which can only make the witness refuse; `maybeCommit` skips a compacted index);
  `OneLessThanQuorum` of one voter is 0.
- A candidate asks each witness at most once per campaign (`witnessVoteAsked`; #168 asked again
  on every vote response while pending, after the witness's own rejection too: a request loop).
- witness.go: the answer to an older-term request carries Term/From (raft dropped it); the cache
  is the stored state after a successful update; the ack of a request that raised the witness's
  term carries the new term (it carried the old one, so the leader dropped it).
- `ChangeReplicationSet` returns `false` at once when the epoch has no witness (`f6de2ff0b`;
  behaviour-preserving: the loop changed nothing then), so its witness-free proof is short.
- `ResetReplicationSet` without a witness installs the bare epoch (subterm, zero replication
  sets) and returns (`eebbe9e9`; behaviour-preserving: the sets are read only with a witness).
- `witness_test.go`: reproductions of the findings, and a two-nodes-plus-witness cluster (commit
  with the witness while a node is down, shortcut replication without storage writes, the node
  lacking a witness-committed entry is not elected, recovery).

## Why it is safe (static configuration, one witness)

Write n for the voters (witness included), q = n/2 + 1, RS(t, s) for the replication set of
subterm s of term t, H for regular members of it that acknowledged an index, W the witness.

- (t, s) determines RS(t, s): one leader per term, subterms count up from 0 within a term,
  subterm 0's set excludes W (so (t, 0) is never written to W).
- Every acknowledgement by W of index i in term t (written or shortcut) has: an entry at
  idx ≥ i in the leader of t's log with (t, s); |H| ≥ q−1 with H ⊆ RS(t, s) ∖ {W}, each having
  acknowledged idx in term t; and W's state was (t, s, RS(t, s)) at some point. W's
  (last term, last subterm) only grows (writes need a strictly newer pair), and so does its term.
- Leader Completeness, the case the witness adds: the voter in both the commit quorum and the
  winning quorum of a later term T is W. W's state when it voted is ≥ (t, s) (its term was T > t
  then, and the state with term t came earlier). Cases on the candidate's reported last (lt, ls)
  against W's (lt_w, ls_w) ≥ (t, s):
  - lt > t: the induction hypothesis at lt (as in the regular case);
  - lt = t, ls > s: the candidate's last entry is the leader of t's, of a later subterm, so past
    idx (subterms are nondecreasing in a term): it has the entry;
  - (lt, ls) = (t, s) = W's: every responder, so the q−1 granted votes G before asking W, is in
    RS(t, s) ∖ {W}, as is H; |RS ∖ {W}| = n − 2 < 2(q − 1), so G and H meet in a regular voter
    who acknowledged idx and voted for the candidate: the regular case.
  The candidate's reported subterm may be below its real one (snapshot: 0); only the second
  case uses it, and a lower report only makes W refuse.
- Election Safety: W votes once per term (its vote is in the CAS-updated state).

Not covered by this argument: a witness in a joint configuration or across reconfiguration
(the stored replication set is of the configuration of its subterm); #168 allows a witness in
each half of a joint configuration and checks the responders against the incoming half only.

## How it goes into the proof (plan)

The pivot of Leader Completeness is `lc_adj_gen` (`Protocol/LeaderCompleteness.lean`): a voter in
both the commit quorum and the winning quorum, its vote record and its acknowledgement history.
The witness becomes a member of the configuration whose ghost records are owned by a witness
invariant (over the `WitnessStorage` trust boundary) instead of `ownRaftGhost`:
- `isAcked γ W t i`: a witness disjunct, justified by the leader's record `isRS γ t s rs`, the
  acknowledgements of H (carried by the leader's witness request), and a lower bound of W's
  state history (the cache, or the write);
- `voteJust γ W T c`: W's state at the vote, the request's campaign and its granted set G;
- `lc_adj_gen`: the witness case above, by the regular case at a voter of G ∩ H;
- entries gain the subterm (`EntryM`), nondecreasing within a term in a leader's term log.

Stages:
- W0 (done): Go implementation and tests; translation.
- W1 (done 2026-10-19, "W1" below): the build back to green on witness-free configurations
  (the `ownRaftPhys` facts: no witness in the tracker, `witnessMsgs = []`, subterm 0).
- W2 (done 2026-10-20, "W2" below): the protocol model and ghost extension (static mode),
  Leader Completeness and Election Safety with a witness.
- W3: the raft functions' witness paths (`maybeCommit`, `stepCandidate`, `maybeStartNewSubterm`,
  `sendAppendToWitness`, `sendRequestVoteToWitness`) and `witness.go`.
- W4: `examples/kv` with a witness (user request, 2026-10-19), its closed theorem re-proved.

## W1: what the witness-free proof says (2026-10-19)

The invariants (no new protocol invariant; the raft struct's and the tracker's facts):
- `ownTrackerC`/`ownTracker`: the configuration has no witness (`ownCfgCC`'s
  `Witnesses = [0, 0]`), no peer is the witness or `0` (`NoWitP`: `IsWitness = false`, and the
  id `0`, which raft#168 reads as "the witness" when `Witnesses[i] = 0`, is not tracked:
  `LeaveJoint` keeps an outgoing voter `0`), and the epoch is witness-free and read-only
  (`ownEpochNW`: subterm 0, no witness, none excluded; `ResetReplicationSet`/
  `ChangeReplicationSet` allocate new epochs, so an epoch is never written in place).
- `raftOwn`: `witnessMsgs = nil` and `witnessVoteAsked = nil`.
- The model's `Progress` has `witness` (mirroring `IsWitness`), `EntryM` has `Subterm'`, and
  the protocol's `stamp` sets it to 0 (W2 changes this).

Specs that changed, and why (the new code forced each):
- `appendEntry` stamps subterm 0 (`stamp`); `becomeLeader` calls `maybeStartNewSubterm(true,
  false)`, specified (`raft__maybeStartNewSubterm.lean`) for `confChange = false` only, the
  witness-free behaviour: reset to a fresh witness-free epoch and append the empty entry, or
  (check-quorum) nothing.
- `poll` is `pollAndReportDiff` (raft#168's rename), returning the votes still needed per half.
- `switchToConfig` takes the old tracker's epoch (`ownEpochNW tv0.Epoch'`): the body reads
  `r.trk.Epoch.HasWitness()`.
- `MakeProgressTracker` returns `Witnesses = [0, 0]` and the witness-free epoch;
  `confchange.Restore`'s `Progress` objects are no witness's.
- `RawNode.Bootstrap`, `setupNode`, `StartNode` (and the server's `newRaftNode`,
  `NodeStartSpec`, `bootOk`) take `∀ p ∈ peers, p.IsWitness = false`: Bootstrap adds a witness
  peer with an `AddWitness` change.
- `BootLogOk`: the boot entries are at subterm 0 (Bootstrap leaves `Subterm` unset).
- `OneLessThanQuorum` of one voter returns 0 (no premise `|s| ≠ 1` any more).
- New witness-free specs: `Epoch.HasWitness` (false), `Epoch.ReplicateToWitness`,
  `ProgressTracker.{ChangeReplicationSet (false), OneLessThanQuorumInReplicationSet (nil),
  ResetReplicationSet (true only)}`, `raft.getWitnessVoteRequestReadiness` (nil),
  `Entry.GetSubterm`.
- `ccApplyM` facts (`CCApplyC.lean`): a change it accepts adds no witness (`AddWitness` is
  "unexpected conf type" to its model) and tracks no `0` if the old state did not, which give
  `Changer.Simple`/`EnterJoint`'s and `LeaveJoint`'s new premises in `applyConfChange`.
- The server's `EntryModel` has a `subterm` field, so that `toM`/`ofM` stay inverse; no server
  spec constrains it.

## W2: the protocol with a witness (2026-10-19/20, branch `raft-witness-w2`)

Static mode only (`γ.reDyn = none`; `wOwn` says a dynamic node's subterm is 0); one witness
`γ.reWit` (`0` for none), a voter of `reCfg` that is not a node (`reWit_ok`: no acknowledgement
map, no vote-time logs).

The model (`Model.lean`, `StepC.lean`):
- messages `wapp`/`wvote`/`wprevote` (the subterm in `Commit`: `Msg.sub`); `PState.sub`/`rsx`
  (the subterm and the excluded voter, `exclOf`: the witness when `rsx = 0`); `CfgM.wit`;
- `propose` stamps the leader's current subterm (`stampS`); `newSub` starts a subterm with an
  empty entry; `sendWApp` sends the witness an entry of the current term and subterm that
  `quorum − 1` voters of the replication set (`rsVoters`) acknowledged; `askWitness` asks the
  witness one vote short, with every responder; `sendWPre` (pre-votes carry nothing).

The ghost state:
- each node's lists (`wOwn`, `reWG`): per term it led, its subterm list (an item
  `(index, subterm, excluded voter)` per entry it appended, `SubSorted`), whose item an entry's
  record carries (`isEntryR`'s `subRec`), and per campaign its granted list, closed by `none` at
  the win (`winGrant` in `isWinCore`), whose lower bound a witness vote request carries
  (`grantLb`), so that the votes it reports are in the winning quorum (`grantLb_win`);
- the witness's storage (`Witness.lean`, `wGhost`): the authority of the state history
  `reWHist` (term and last `(term, subterm)` nondecreasing, `wHistOk`; each state's last entry
  justified by its witness request, `wStJust`) and its half of its vote map;
- `isAcked`'s witness disjunct (`wAck`: a witness request `wJust` — the leader's item, the
  entry in its log, `quorum − 1` acknowledgements of the replication set — and a state of the
  history with that entry's `(term, subterm)`, a cache or the stored state); `voteJust`'s
  (`wVoteJust`: the state the vote was granted from and the request's `wVoteReq`).

Proved (no `sorry`, no axiom): every `StepC` rule's ghost step (`Refinement.lean`; the witness
rules' messages carry `wJust`/`wVoteReq`: `ownRaftGhost_wapp`/`_wvote`); Leader Completeness's
witness case (`lc_wit`, `LeaderCompleteness.lean`: newer term by induction, a later subterm by
the subterm list's order, the same `(term, subterm)` by `G ∩ H ≠ ∅` among the regular voters,
`|rs ∖ {w}| = n − 2`); so `leader_completeness`, `state_machine_safety` and election safety
(`isLeader_unique`) hold of a cluster with a witness, whose allocation (`ownRaftGhost_alloc_core`,
parameter `wit`) gives the storage's `wGhost γ wInit`; one lemma per `witness.go` path
(`Witness.lean`): storage read, `handleAppendNoUpdate` from a cache or the stored state, term
raise, `handleAppend`'s write, `handleVote`'s grant (in the votes table), `handleHeartbeat` at
the stored state's term (the read-index acknowledgement holds since the witness acknowledged
nothing above it; answered from the cache it would not: the bug fixed in `edd87c489`). Lease
reads stay outside the proof (ReadOnlySafe only), and are not supported with a witness.

Not yet (W3): the code's witness paths and `witness.go` against these lemmas (a
`WitnessStorage` trust-boundary spec whose CAS owns `wGhost`); the code-level allocation passes
`wit = 0`.

## W3a: the tracker's epoch and `witness.go` with a witness (2026-10-20, branch `raft-witness`)

The Go code: the fork's `9ed005d46` (`edd87c489` plus two fixes found writing the specs: a
newer-term heartbeat is answered at the new term, `handleHeartbeat(m, term)`; `cloneState` reads
a nil stored state as the zero state; rows 13 and 14 of `notes/raft-witness-vs-pr168.md`).

The tracker's epoch (`InvEpoch.lean`):
- `EpochM` (subterm, two halves `RSM`: witness, excluded voter, non-witness voters); `ownEpoch`,
  persistent (an epoch is never written in place); `RSWF V w r` (a half well formed for its
  voters `V` and the configuration's witness `w`), `EpochWF` (bare without a witness, else both
  halves well formed);
- `resetEpoch` (what `ResetReplicationSet` builds: each half's witness excluded), `rsChanged`
  (what `ChangeReplicationSet` rebuilds a half into around a new excluded voter `x`, the witness
  or an inactive member of the replication set) and `rsChanged_wf`; `ChangeEpochOk` (the next
  subterm, the same witnesses, both halves well formed: which voter is excluded depends on
  `RecentActive`, which the `Progress` model leaves out, so the spec leaves it open, as the
  protocol's `newSub` does).

Specified and proved with a witness (the witness-free specs, `spec_nw`, their corollaries, used
by the existing callers): `ResetReplicationSet`, `ChangeReplicationSet` (`chgRes`: the progress
map, whose peers include the halves' voters), `OneLessThanQuorumInReplicationSet` (`OltqOk`),
`Epoch.HasWitness`, `Epoch.ReplicateToWitness`, `ReplicationSet.GetNonWitnessVoterSlice`,
`scopedAckIndexer.AckedIndex`.

`witness.go`:
- the model (`InvWitnessM.lean`): the durable state `WHS` (W2's `WState` plus the commit index,
  the leader, the outgoing replication set), a request `WMsg`, and each handler as a pure
  function (`wOlder`, `wNewer`, `wHeartbeat`, `wAppendNoUpdate`, `wAppend`, `wVote`,
  `wNoUpdate`), and `Process`'s round, `wStep`;
- the heap (`InvWitness.lean`): a state field by field at a fraction (`whsF`; `whsRO`, the
  storage's and the cache's; `whsOwn`, the one a handler builds, frozen by `whsOwn_freeze`;
  `whsOpt`, the cache, nil before the first read); a request `ownWMsg`; an answer `respOpt`;
- every handler specified against its model and proved: `handleHeartbeat`, `handleAppendNoUpdate`,
  `handleAppend`, `handleVote`, `processMessageWithOlderTerm`, `processMessageWithNewerTerm`,
  `processNoUpdate`, `cloneState`, `isHealthy`; the `WitnessHardState` getters (and the
  `HardState` getters field by field, at any fraction: a built state's hard state is owned);
- the storage contract (`InvWitnessStorage.lean`), a premise of the witness's specs, not an
  axiom: `isWitnessStorage s N P`, the stored state's ghost counterpart an abstract `P` in an
  invariant of namespace `N`; `GetWitnessState` runs the caller's `P σ ={⊤ ∖ N}=∗ P σ ∗ Ψ σ` at
  its read (W2: `wGhost_read`), `WitnessState.Update` is a compare-and-swap that runs the
  caller's `P σ ={⊤ ∖ N}=∗ P σ' ∗ Ψ` iff the stored state is still the one read (W2:
  `wGhost_raise`, `_write`, `_vote`, `_push`). With `N ⊆ raftRegN`, W2's `wGhost_vote` (at
  `⊤ ∖ raftRegN`) fits the mask.

Not yet: `Process` (its spec against the contract, `wStep` per round with the retry on
`ErrWitnessStateModified`, which needs that variable's value among the raft package's facts,
`etc/gen-init.py`'s `SPECIAL`); its instance at `P := wGhost γ ∘ WHS.ws`, which maps each
`wStep` case to W2's lemma (the model's `WMsg`/`WResp` to W2's `Msg`); and the raft functions'
witness paths (`maybeCommit`, `stepCandidate`, `maybeStartNewSubterm`,
`sendAppendToWitness`, `sendRequestVoteToWitness`) with a witness.

## W3b-A: the raft predicates with a witness (2026-10-20, branch `raft-witness`, in progress)

The representation, generalized from W1's witness-free facts (commits `c5ca6b38ad`, `020525d6f6`,
`59ebeaee75`):
- the epoch is the tracker's state: `Trk.ep` (`NState.ep`, default the bare epoch of subterm 0);
  `ownTrackerC` holds `ownEpochOk c.incoming c.outgoing c.wit tv.Epoch' t.ep` (`EpochOkC`: bare
  without a witness; bare or well formed, `EpochWF`, with one -- a follower's stays bare until it
  leads), `ownTracker` (witness-free) `ownEpochNWm` (bare); the epoch structures moved to
  `Defs.lean`. `toPState` reads a leader's `sub` and `rsx` from it (`epochRsx`: half 0's excluded
  voter, `0` for the witness), a non-leader's are `0` (`toPState_ep_nl`); `toPState_becomeLeader`
  and `toPState_voteRespResult` take the installed epoch (subterm 0, the witness excluded);
- `ownTrackerC`: `WitP c.wit` (the configuration's witness alone has a witness's `Progress`, no
  peer is `0`; `WitP.zero`: it is `NoWitP` at `0`), the configuration `ownCfgCCw c.wit`
  (`Witnesses = [c.wit, 0]`); `confchange`'s specs stay witness-free (`ownCfgCC = ownCfgCCw 0`),
  and the conversions to and from them take `c.wit = 0` (`ownTrackerC_toCC`, `ownResult_transfer`,
  `ownTrackerC_reconfig`, `ownTrackerC_toSimple`): a configuration change with a witness is out
  of the static mode;
- `ownRaftPhysG`'s witness id `W` (`0` for `ownRaftPhys cfg`, `c.wit` for `ownRaftPhysCV c`);
  the queue `r.witnessMsgs` and the asked set (`witOwn W wsl asked wq`, `InvWitnessOut.lean`:
  `ownWQueue`, each request an `ownWMsg` whose protocol reading `wAbs` -- `wapp`, `wvote`,
  `wprevote`, a heartbeat -- is on the outbox: `outboxRel`'s fourth argument `wq`; `ownAsked`;
  without a witness both nil and nothing queued), the field values `wsl asked` with a pure
  equation `Hwf` (so that a struct update elsewhere re-seals by `assumption`, like the other
  fields);
- witness-free accessors, for now, take `c.wit = 0`: `ownRaftPhysC_toPhys`, `ownRaftPhysC_nowit`,
  `raft.wp_load_trk_EpochC` (general: `raft.wp_load_trk_EpochC'`, `ownEpochOk ... e s.ep`),
  `raft.wp_load_trk_witnessC`, `ownRaftPhysC_view` (the Ready view: handing out witness
  messages is not done); `ownRaftPhysC_retrack`/`ownRaftPhysCV_reconfig` take the witness
  unchanged.

State: `InvTracker`, `InvTrackerC`, `InvRaftPhys`, `InvApplyConfC`, `confchange`, the tracker's
specs build; the raft function proofs that use the changed predicates do not yet (see the last
build's list in the W3b-A report): each needs either `c.wit = 0` (witness-free callers) or its
witness branch proved (`appendEntry` with the epoch's subterm, `maybeCommit` →
`sendAppendToWitness`, `stepCandidate`/`campaign` → the witness's vote, `maybeStartNewSubterm`,
`bcastHeartbeatWithCtx` → `sendHeartbeatToWitness`, `maybeSendAppend`, `promotable`, `reset`'s
asked set, `newRaft`'s tracker at the bare epoch), and the Ready path (`InvRawnode*`,
`RawNode.*`, `node.*`) `outboxRel`'s new argument and the witness queue.

Proved at any configuration (2026-10-20, commits `32e2981a18`, `2ee6eed844` and after):
- `appendEntry` stamps the epoch's subterm (`stampS s.term s.ep.sub`; the `Subterm != 0` branch
  allocates the cell, the other stores `nil`); `proposed` (stepLeader's `MsgProp` state) the same;
- `maybeStartNewSubterm` (`subtermStart`): with `newTerm` the reset epoch at subterm 0
  (`ResetReplicationSet.spec_c`, `EpochOkC_reset`); without, `ChangeReplicationSet.spec_c` -- nothing,
  or the next subterm's epoch (`ChangeEpochOk`) and the empty entry at it; the `HasWitness` log
  lines (`ReplicationSet.String`, proved: at most `2^62` ids, `RSM.strLen`, from the tracker's
  size bound, `ownRaftPhysC_strLen`; it rests on `strconv.FormatUint`'s trust-boundary axiom,
  which raft's results did not use before);
- `maybeSendAppend` (nothing to the witness, as when paused), `promotable` (`false` at the
  witness: the spec says `id ≠ c.wit`).

**Staged (2026-10-20): no witness yet.** To get the tree building before every witness branch is
proved, `witOwn` carries `⌜W = W64 0⌝` (marked `STAGED` in `InvRaftPhys.lean`), read out by
`ownRaftPhysC_wit0` at each witness site not proved yet: `maybeCommit` (`sendAppendToWitness`),
`bcastHeartbeatWithCtx` (`sendHeartbeatToWitness`), `campaign`/`stepCandidate` (the witness's vote
and pre-vote, `getWitnessVoteRequestReadiness`), `stepLeader`'s check-quorum and other `NoWitP`
uses, `applyConfChange`/`restore` (a witness-free configuration stays one: `ccApplyM_wit0`), the
Ready views (`ownRaftPhysC_view`, `ownRaftPhysC_toPhys`), `MsgProp` (`StepR.propose`, the dynamic
model, stamps subterm 0). `ProgressTracker.ConfState` and `switchToConfig` take `c.wit = 0` as a
premise (with a witness `cs.Witness` is set, which `ConfStateM` does not model, and
`switchToConfig` calls `maybeStartNewSubterm(false, true)`). Every result still holds; they are
about witness-free configurations, as the `RawNode` layer (`ownRaftPhys`, `CfgM.simple`) already
is. Grep `STAGED`/`ownRaftPhysC_wit0` for what is left; the conjunct goes when the last is proved.

Retranslated at the fork's `99cb9e2d9` (2026-10-20): `OneLessThanQuorumInReplicationSet` returns `nil`
also for a witness both halves share when only one replicates to it (`OltqNone`; the spec now gives
`oltqRes` back in every case). Static mode is unaffected (one half). kv's `wErrOk` records
`IsNewError` (W3b-B's storage contract) and follows from raft's initialization (`wErrOk_of_init`).

Gaps of the model found on the way: `leaveJointState` (`InvConfchange.lean`) builds a configuration
without a witness (Go's `LeaveJoint` keeps `Witnesses[0]`); `ConfStateM` has no witness fields
(Go's `ConfState()` sets `Witness`/`WitnessOutgoing`), so a snapshot's configuration loses the
witness in the model.

## W3b: `Process`, its instance at W2's ghost state, the `Witness` interface (2026-10-20, branch `raft-witness-w3b`)

- `ErrWitnessStateModified` is among the raft package's facts (`isInitialized`, `Base.lean`;
  `Init.lean`): a non-nil pointer error (`IsNewError`). The storage contract's `Update` gives
  back a pointer error (`IsNewError`) on failure, so `Process`'s `err == ErrWitnessStateModified`
  is decided (interface equality of two pointer errors).
- `witness.Process` (`Spec/.../witness__Process.lean`, proved): for any reading `P`/`Lb`/`Φr`
  of the storage's states the caller picks, the cache's `wNoUpdate` answer is `Φr`'s
  (`Hcache`), at each read the caller gives `Lb` and the round's obligation `wObl` (`wStep`: an
  answer without a write, or the write's shift run at the compare-and-swap), for a request of
  the four types the witness answers. A failed compare-and-swap is retried; `Process` is
  partially correct (the loop need not end). `NewWitness` (`ownWitness … WHS.zero true`) and
  `Close` specified and proved.
- The instance (`InvWitnessGhost.lean`): `P σ := wGhost γ σ.ws`, `Lb σ := wSt γ σ.ws`,
  `Φr := wRespOk γ` (an answer's protocol reading, `absMsg`, carries `isMessage`), a request
  read as W2's `Msg` (`wAbsReq`). Each `wStep` case is one of W2's lemmas: the heartbeat at the
  stored term `wGhost_heartbeat`; the cache's answers `wSt_app_noupd` (and nothing for an older
  term's or a pre-vote's); at the CAS a newer term `wGhost_raise`, an append `wGhost_write`
  (after the raise), a vote `wGhost_vote`, a pre-vote the state written back unchanged.
  `witness.Process.ghost` (`InvWitnessIface.lean`) is the spec at W2's ghost state: a request
  whose reading is legitimate is answered, if at all, legitimately, the cache a state of the
  history.
- `ownWitnessI γ N wi` (the `*witness` `NewWitness` returns, as a `Witness`) and
  `Witness.wp_Process'`/`Witness.wp_Close'`: the methods through the interface, what raft and
  the kv example call. `WHS.zero.ws = wInit`: a fresh witness's cache is W2's initial state.
- Two adjustments of W2, both minimal: the vote rule counts the responders over the stored
  replication set (`votesInSet`), which needs it without repetition, so `isMessage .wapp` and
  `wStJust` carry `Nodup` (proved at `sendWApp` from `vs ≡ₚ elements …`); and `vote_insert`
  is at any mask containing `raftLogN` (`vote_insertE`), so the storage's namespace `N` need
  only be disjoint from the log invariant's (`↑raftLogN ⊆ ⊤ ∖ ↑N`), not inside `raftRegN`.
- Premises of the instance: the witness's id is `γ.reWit ≠ 0`, the request is to it
  (`μ.to = γ.reWit`) from a node (`μ.frm ≠ 0`), and `raftCommitInv γ`.

No new axiom or `sorry`.
