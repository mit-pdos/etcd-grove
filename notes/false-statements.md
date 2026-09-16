# Eight false statements in three days

The single most useful signal this project has produced, and the reason
[STATUS.md](STATUS.md) points here before it points anywhere else. Read this
before adding a claim — a spec, an `Axiom`, an `Admitted` `Lemma`, or a
comment that promises an invariant.

The single most useful signal this project has produced. Each of these was
asserted, compiled, and lived in the tree until a proof needed the fact and
could not get it:

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

