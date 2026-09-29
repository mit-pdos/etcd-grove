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
| `wp_raft__appendEntry`, again | owned no part of `es`, but the method writes `Term`/`Index` into every element (`v3.v:3453-3461`) — "own what you write" |
| `wp_raft__appendEntry`, again | claimed `RET #true` unconditionally; there is a `return: #false` when `increaseUncommittedSize` rejects (`v3.v:3463`) |
| `own_tracker`'s `HmaxInfl` comment (`inv_tracker.v`) | said `Config.validate` requires `MaxInflightMsgs ∈ (0, 1<<30]`; `validate` checks only `> 0` (`v3.v:2830-2832`). The conjunct itself (`< 2^62`) is needed and kept, so `own_raft_phys` is **unsatisfiable for a valid `Config` with `MaxInflightMsgs ≥ 2^62`**, and `newRaft`'s spec takes the bound as a premise of its own. Found 2026-09-24 writing that spec |

**Nine of the ten were claims about what raft's code does that nobody had
checked against the generated body** — the cheapest check available. The
tenth (`r.step`) was prose promising an invariant.

**`wp_raft__appendEntry` is on this list three times**, which is the
strongest argument in the file for the 2026-09-18 rule that an `Axiom` about
a Go function belongs inside a spec/postulates/proof/link collection like
any other triple (see [decisions.md](decisions.md)). It is the one triple
here that will never be proved from the code, so it is the one nothing ever
forced to be right.

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
unreachable rather than assumed away. Three of the ten were caught that
way — the third being `appendEntry`'s `RET #true`, below.


## Duplicate specs: where the next false statement will come from

Added 2026-09-18, found by `etc/check-module-discipline.py` (see
[decisions.md](decisions.md)). A Go function with two Hoare triples has one
triple nothing checks, because a proof only ever consumes one of them. That is
the same shape as every row of the table above, so it belongs here.

The checker reads the program expression out of each triple rather than
trusting the lemma name, and reports which Go function a spec really talks
about. Run it:

    etc/check-module-discipline.py --summary

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

## 2026-09-18: `wp_raft__appendEntry` asserted an unconditional `true`

Found in review of the module-discipline branch, in the same axiom the rename
above touched. Two independent over-claims, both visible from the triple
alone once you read `raft__appendEntryⁱᵐᵖˡ` in `new/code/go_etcd_io/raft/v3.v`:

- **No ownership of `es`.** The method writes `Term` and `Index` into every
  element of the slice (`raft__appendEntryⁱᵐᵖˡ`'s `slice.for_range`,
  `v3.v:3453-3461`), so the triple asserted the safety of a write to memory
  it had no claim on. This is the `wp_ProgressTracker__Visit` mistake one
  level out: not "own the receiver's fields" but **own what you write**.
  `es ↦* ents` is now a precondition, and comes back existentially
  quantified — it *does* come back, because `raftLog.append` copies the entry
  values into `unstable.entries` rather than taking the caller's slice.
- **`RET #true` for an arbitrary `es`.** `appendEntry` does have a
  `return: #false`: the path where `increaseUncommittedSize(es)` rejects the
  batch (`v3.v:3463`). The triple quantified over every `es : slice.t`, so it
  claimed the batch is always accepted.

**The obvious fix is also wrong, and this is the more useful half of the
story.** Weakening the result to `∃ accepted : bool, RET #accepted` is sound
as an assumption and makes `becomeLeader` **unprovable**, because
`becomeLeader` does not ignore the result:

    if !r.appendEntry(pb.Entry{Data: nil}) { r.logger.Panic("empty entry was dropped") }

and `wp_Logger__logf` deliberately excludes `Panic`. Measured, not inferred:
with the existential form `make …/proof_raft__becomeLeader.vok` fails with
`Error: Failed to progress.` — `wp_auto` cannot step `if: ~accepted` for an
opaque boolean — while `make …election.required_vos` passes, which is exactly
how the weakening looked fine.

What is actually true is that the reject path is unreachable *for an empty
payload*. `increaseUncommittedSize` returns `false` only when

    uncommittedSize > 0 ∧ payloadsSize(ents) > 0 ∧ … > maxUncommittedSize

(`v3.v:5401`), and `payloadsSize` sums `len(e.Data)` (`v3.v:7515,7524`). So
the triple keeps `RET #true` and carries the premise
`Forall (λ e, sint.Z e.(Entry.Data').(slice.len) = 0) ents`, which is
precisely what `becomeLeader` passes — `pb.Entry{Data: nil}` — and which
makes the `Panic` *demonstrably* dead rather than assumed away. That is the
rule this file already states for `send`: a panicking path has to be shown
unreachable, and showing it needs the fact that makes it unreachable to be in
the premise.

**Tell, and it is the same one as the first row of this file's table:** a
triple that quantifies over an argument it says nothing about. `∀ es :
slice.t` with no `es ↦* _` in the precondition and no occurrence of `es` in
the postcondition means the claim does not depend on the argument at all —
for an `Axiom` at a trust boundary, that is exactly where an unprovable
strengthening hides. Worth grepping for: a `∀`-bound `slice.t` or `loc` that
appears only in the program expression.

**And a second tell, from the wrong fix:** when weakening a postcondition
makes a *caller* stop compiling, the weakening is the wrong repair — the
caller was relying on the strong form for a reason, and here the reason was
a `Panic` it has to rule out. Reach for the premise that makes the strong
form true before reaching for a weaker conclusion. A `vos` build will not
tell you the difference; only `vok` will.

## `wp_raftLog__slice_at` is false at a log with ~2^63 unstable entries (2026-09-20)

`raftLog.slice`'s `extend(ents, unstable)` computes `need := len(dst)+len(vals)`
as a Go `int`. With about `2^63` unstable entries `need` wraps negative,
`need <= cap(dst)` becomes true, and the code takes the in-place `append`
branch that `spec_extend.v` deliberately does not cover (Go itself would
then panic on the negative re-slice). The triple therefore over-claims at
that extreme, exactly as `campaign`'s did at `term = 2^64 - 1`.

Unlike `campaign`'s, this one has no premise to hang the fix on: the
consumer that matters, `hasUnappliedConfChanges`, opens `own_raftLog`, whose
entry lists are existential, so `hup`/`Step` cannot state `hi - lo < 2^63`;
and a bound carried in `own_raftLog_at` cannot survive `appendEntry`
(decisions.md). So it is left as the one deliberate `Admitted. (* Trusted *)`
on the election path — "the log fits in memory" — with the arithmetic in
the file's header. **The tell**: an `int` sum of two slice lengths whose
operands come from different owners (here `Storage` and `unstable`); the
model bounds each slice at `2^63` but not their sum.

## `spec_raft__maybeSendSnapshot.v`: `own_raft_phys ∗ own_progress pr` is contradictory at its call site (2026-09-21)

`own_raft_phys` contains `own_tracker`, which contains
`[∗ map] p ∈ prs, own_progress p` with `dom prs = cfg`; `maybeSendAppend`
calls `maybeSendSnapshot` with `pr = prs !! to` for a voter `to`. Both
copies of `own_progress pr` are `pr ↦ pv` at `DfracOwn 1`, so the
precondition is unsatisfiable exactly when it is called. Probed:
`iCombine "H1 H2" gives %Hbad` yields `✓ (DfracOwn 1 ⋅ DfracOwn 1)`. The
triple is *true* (for a `pr` outside the tracker) and was Qed against;
it is simply uncallable. Third of its family, after the 2026-09-14
`own_tracker` double-claim and the 2026-09-16 `Visit` receiver bug.

**The rule:** when a spec takes `own_raft_phys` and a sub-resource side by
side, check that the sub-resource is not already inside it. The cheap probe
is the `iCombine … gives` above. **The companion rule:** a predicate that
hides the struct under `∃ rv` cannot express "this call does not touch field
`f`"; a proof that must come back to a pointer it read *before* such a call
needs the field pinned as a parameter. Making what the field points at
persistent (`↦$□`) pins the *contents* at a location, not *which* location
the predicate names afterwards — so the read-only progress map was necessary
but not sufficient for `maybeSendAppend`. The fix was `own_raft_notrk`
(STATUS item 18) -- itself replaced on 2026-09-22 by fields of `nstate.t`
(`progress`, `lent`); see decisions.md, "Three layers". The rule above
still stands; what changed is where the pinned field lives: in the
abstract state, not in a variant predicate.

## The same family, fourth member: `send` owned the log the caller had a slice of (2026-09-21)

Repairing `maybeSendSnapshot`'s precondition and `send`'s hidden tracker
(above) was not enough for `maybeSendAppend`: `send`'s precondition also
owned the **log**, and `raftLog.entries` lends its result *out of*
`own_raftLog`, so `ents` and the log cannot be held at once — yet
`payloadsSize(ents)` runs *after* the send (v3.v:3153-3157), and the
message literal reads `r.raftLog.committed` while `ents` is out. The
sharpest form of the rule: **when a function borrows a sub-resource out of
a predicate `P` and then calls something specified on `P`, the borrow must
come back out of `P`'s precondition, not be re-derived from `P`'s
postcondition**; persistence of the borrowed thing fixes re-finding, not
holding. Second tell, independent of the first: look at what the code does
*after* a call, not just before it — a spec review that stops at the call
misses this class. Fix: `own_raft_bare` (decisions.md), and
`entries`/`slice` now hand the `raftLog` record back beside the result.
**Superseded 2026-09-22**: `own_raft_bare` is gone; `maybeSendAppend` now
puts the tracker and the log **on loan** (`nstate.lent := Some tv`) across
`send`, and `send` is stated on `own_raft_phys` for any `s`.
**Superseded 2026-09-29**: nothing of the log is lent any more; the log
holds its entries read-only and `entries` hands `ents` out read-only and
for good, so only the tracker is on loan across `send`.

