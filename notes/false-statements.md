# False statements, and duplicate specs

The single most useful signal this project has produced, and the reason
[STATUS.md](STATUS.md) points here before it points anywhere else. Read this
before adding a claim — a spec, an `Axiom`, an `Admitted` `Lemma`, or a
comment that promises an invariant.

Each of these was asserted, compiled, and lived in the tree until a proof
needed the fact and could not get it:

| what | why it was false |
|---|---|
| `wp_raft__appendEmptyEntry` | owned only the log; `appendEntry` also queues a `MsgAppResp` |
| `step_win` | claimed one `App` per peer; `maybeSendAppend` sends one only when the log and `Progress` allow |
| `spec_raft__campaign.v` | no term-no-wrap premise; `send` `Panicf`s on `Term = 0` after `becomeCandidate` increments |
| `inv_raft_phys.v`'s `r.step` comment | promised an invariant that appeared in no conjunct |
| `own_progress` | no `IsLearner = false`, so `promotable`'s postcondition was not derivable |
| `TallyVotes`'s `VoteLost` conjunct | Go's `VoteLost` is "cannot still win", not "a majority rejected" |
| `wp_ProgressTracker__Visit` | owned no part of the tracker *struct*, but `Visit` has a pointer receiver and loads `p.Progress` through it (`tracker.v:809`, `:837`) |
| `TallyVotes`'s `VoteWon` conjunct | `MajorityConfig.VoteResult` returns `VoteWon` outright for an empty config (`quorum.v:412-418`), while `is_quorum ∅ q` is `0 < 0` |

**Seven of the eight were claims about what raft's code does that nobody had
checked against the generated body** — the cheapest check available. The
eighth (`r.step`) was prose promising an invariant.

The two found on 2026-09-16 add a third tell, and it is the sharpest one:
**a spec for a method with a pointer receiver must own the receiver's
fields.** `own_tracker` is indexed by the tracker *value* and owns what that
value points at — deliberately, so that it is disjoint from `own_raft_phys`'s
`r ↦ rv` by construction. That is right, and it is exactly why every
pointer-receiver method on the tracker needs `trk ↦ tv` *as well*.
`ResetVotes` and `RecordVote` had it; `Visit` did not, and a comment above it
explained at length why it did not need to. The comment reasoned about
*mutation*; the obligation is about any *read* through the receiver. Two
probes settle it in one `-vok` run: `wp_start; iNamed; wp_auto` with the
precondition as written, and again with `trk ↦ tv` added — if the second gets
further, the first was false.

Two tells worth grepping for:

- **An evar in a re-seal.** `iExists (rv <| step' := _ |>)` means a field
  nothing constrains. Both `r.step` and `IsLearner` hid there.
- **An `Admitted` lemma under a `Qed`.** `stepCandidate` was `Qed` while
  consuming a false `TallyVotes`; the `Qed` inherited the falsity. `reset`
  was `Qed` while consuming a false `Visit`, and `becomeFollower`,
  `becomeCandidate` and `becomeLeader` rest on `reset`. An `Admitted` is not
  a placeholder for work, it is an unchecked claim. Discharge leaves before
  trusting roots — and when a leaf turns out to be false, **repair the
  statement even if it stays `Admitted`**: a true assumption is a debt, a
  false one invalidates everything above it.

And one habit: **for every `send` on a path, ask where `Term ≠ 0` and
`m.To ≠ id` come from.** `send` `Panicf`s on both, and `wp_Logger__logf`
deliberately excludes the panicking methods, so such a path must be shown
unreachable rather than assumed away. Two of the eight were caught that way.


## Duplicate specs: where the next false statement will come from

Added 2026-09-18, found by `etc/check-module-discipline.py` (see
[decisions.md](decisions.md)). A Go function with two Hoare triples has one
triple nothing checks, because a proof only ever consumes one of them. That is
the same shape as every row of the table above, so it belongs here.

The checker reads the program expression out of each triple rather than
trusting the lemma name, and reports which Go function a spec really talks
about. Run it:

    etc/check-module-discipline.py --scope raft --summary

### `raft.stepLeader` — two triples, two ownership stories

The live one. Both still exist as of 2026-09-18:

| where | precondition | postcondition | state |
|---|---|---|---|
| `election/spec_stepLeader_MsgVoteResp.v` | `own_raft_phys cfg r id s`, `m.Type = MsgVoteResp` | state unchanged, `err = nil` | `Qed` |
| `readonly.v:936` `wp_raft__stepLeader_MsgReadIndex` | `r ↦ rf ∗ own_raft γ rf`, `m.Type = MsgReadIndex` | `True` | `Admitted`, used by nothing |

The preconditions are disjoint on `m.Type`, so **neither statement
contradicts the other**. What is inconsistent is the ownership:
`own_raft_phys` owns `r ↦ rv` itself, while `own_raft` (`readonly.v:461`) is
a second, axiomatized ownership story for the same struct — the one
[decisions.md](decisions.md) already flagged on 2026-09-14. No single proof
of `Step` can hold both, so whichever survives, the other has to be
restated against the survivor's predicate. Two tells that the `readonly.v`
one is the throwaway: its postcondition is `True`, which hands the caller
back nothing at all and so is useless to any caller that continues, and a
`grep` finds no use of it anywhere.

### `raftLog.lastIndex` and `raftLog.lastEntryID` — two each, but consistent

Both were in `inv_raftlog.v`: an indexed `_at` form stated at a fixed
`(prev, sents, uents)` split, and a weak form over the existential
`own_raftLog`. **Consistent**, because each weak form was *derived* from its
`_at` form a few lines below it. Still two exported triples, and still a
thing a future edit could make disagree.

Resolved 2026-09-18, and the two went opposite ways, which is the point:

- `lastIndex` exports **only** the `_at` form. Its postcondition pins the
  value (`prev.index + |sents| + |uents|`), and that equation is exactly what
  `term`'s and `lastEntryID`'s proofs need to satisfy `Storage.Term`'s range
  premise. The weak form cannot be strengthened back, so it cannot be the
  spec. Callers holding only `own_raftLog` open it with the new
  `own_raftLog_acc` (`inv_raftlog.v`), same shape as `own_raft_misc_option`.
- `lastEntryID` exports **only** the weak form, which is what all four of its
  callers want; its `_at` form is now a lemma inside
  `proof_raftLog__lastEntryID.v`, hidden by the ascription exactly as
  `Step`'s branch lemmas are.

So the rule is not "always keep the stronger one". It is: **keep the form
callers consume, and demote the other to proof structure inside the functor.**

### Restricted specs: one triple today, two tomorrow

Four collections specify a function only for the messages election reaches:

| collection | function | restricted to |
|---|---|---|
| `raft__send_vote` | `raft.send` | `MsgVote`, `MsgVoteResp` |
| `stepCandidate_MsgVoteResp` | `raft.stepCandidate` | `MsgVoteResp` |
| `stepFollower_MsgVoteResp` | `raft.stepFollower` | `MsgVoteResp` |
| `stepLeader_MsgVoteResp` | `raft.stepLeader` | `MsgVoteResp` |

Each is a single triple with a premise on `m.Type`, which is legitimate. They
are listed because they are **where the second triple will appear**: log
replication needs `send` for a `MsgApp` and `stepLeader` for a `MsgAppResp`.
When it does, widen the triple that exists rather than adding a second
`Module Type` — see the 2026-09-14 entry in [decisions.md](decisions.md),
which was superseded once already for exactly this reason. The checker
reports all four as `N1-name` notes so they stay visible.

### Name a spec after the function it specifies

Two specs did not, and one of them is the first row of the table above:

- **`wp_raft__appendEmptyEntry` specified the method `appendEntry`.**
  `appendEmptyEntry` occurs **nowhere** in the generated code —
  `grep -c appendEmptyEntry new/code/go_etcd_io/raft/v3.v` is `0`. A spec
  named after a function that does not exist cannot be read against a body,
  which is the check that would have caught it; instead it sat in the tree
  owning only the log while `appendEntry` queued a `MsgAppResp`. Renamed
  `wp_raft__appendEntry` 2026-09-18.
- `wp_campaign_peer_ids` specified `quorum.JointConfig.IDs` and named neither
  the receiver nor the method, so a second spec of `IDs` would not have
  collided with it by name — and `Include`-collision is what the module
  system relies on to make a duplicate a build error. Renamed
  `wp_JointConfig__IDs`.

**New tell: a spec whose name is not the Go function's name.** It is
mechanically checkable and the checker does it, both directions — the Go
function a triple names must exist in `new/code/`, and the collection must be
named after it.
