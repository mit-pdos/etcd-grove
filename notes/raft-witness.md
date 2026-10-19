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
- W1: the build back to green on witness-free configurations (the `ownRaftPhys` facts: no
  witness in the tracker, `witnessMsgs = []`, subterm 0), every spec as before.
- W2: the protocol model and ghost extension (static mode), Leader Completeness and Election
  Safety with a witness.
- W3: the raft functions' witness paths (`maybeCommit`, `stepCandidate`, `maybeStartNewSubterm`,
  `sendAppendToWitness`, `sendRequestVoteToWitness`) and `witness.go`.
- W4: `examples/kv` with a witness (user request, 2026-10-19), its closed theorem re-proved.
