# Reconfiguration safety: the paper proof (stage B1, 2026-10-14)

State machine safety (two committed logs agree) and read-index linearizability for etcd-raft
with arbitrary configuration changes (joint consensus, learners, `AutoLeave`, removal of the
leader), at the protocol level. This is the plan's design checked step by step against the
Go code at the pinned revision (`40f8be730b18`), with the places where it was incomplete or
needed a fix marked **[gap]** and repaired. Its Lean foundation (pure: quorum overlap and the
configuration of a log prefix) is `Proof/go_etcd_io/raft/v3/Protocol/CfgOverlap.lean`; lemma
names below in `code` are that file's unless they belong to the existing protocol files
(`Protocol/{Model,StepC,Ghost,GhostState,LeaderCompleteness,ReadIndex}.lean`).

Conclusions, in short:

* The design holds, with five repairs: (1) a commit fact must also record "the committer's log
  has at most one conf entry above its configuration index" (the committer's I3 at commit
  time), which the far case `j_c ≥ j_m + 2` uses after the committer's state is gone;
  (2) `win_fresh` is not closed by real-time ordering alone: when the *new* winner has the
  older configuration, the adjacent-case argument for it meets a voter that knew the
  *existing* winner of the term and may hold that winner's entries; the existing winner's
  leader completeness (available: it is in the table) closes it; (3) the campaign record must
  carry the commit index at campaign `k` and witnesses of terms `< T` for the conf entries up to
  `k`; (4) read index's case `j_r ≥ j_m + 2` is not "the reader's committed prefix covers the
  entry" but a contradiction through the doomer's campaign; (5) the witness invariant must be
  node-local (`W`, carried by `MsgApp`/heartbeat/`MsgSnap` for their commit index), since the
  first commit of a position can be of a later term than a commit that covers it afterwards.
* The campaign guard is needed in exactly one place: it makes the candidate's configuration
  the fold of its whole committed prefix (`k`). "At most one conf entry above `k`" follows
  from I1 alone.
* No counterexample to the design; one new code finding, unrelated to safety but in the
  same validation: `issues/raft-joint-empty-transition-panic.md` (an empty `ConfChangeV2`
  with a non-`Auto` transition is accepted while joint, committed, and panics every node;
  reproduced by a Go test).
* `CfgOk`'s size bound must be `< 2^62`, not raft's `≤ 2^62`: at `2^62` two disjoint incoming
  voter sets have a symmetric difference of `2^63`, which Go's `int` reads as negative, and
  `Simple` accepts the swap (no overlap).

## 0. Scope

* **A1** (`issues/raft-advance-before-applyconfchange.md`): the application calls
  `ApplyConfChange` for every conf-change entry of a `Ready`'s `CommittedEntries` before the
  `Advance` that acknowledges them. Consequence used throughout: a node's configuration is
  the fold of its committed log up to a *configuration index* `a` with
  `applied ≤ a ≤ commit` (more precisely `a ≤ applying`, or `a = base` after a snapshot not yet
  applied, see 4.10).
* **Fresh nodes**: no crash-restart with persisted state (so **A2**, atomic persistence of
  entries and `HardState`, `issues/raft-commit-lost-with-entries-kept.md`, is moot). Every
  node starts from one configuration `c0` with `CfgOk c0` and the same initial log. (Go's
  bootstrap applies its conf entries on every node before any message; a node added later
  starts with an empty configuration and log and is unpromotable until it has applied a
  snapshot or the bootstrap prefix: until then its configuration does not matter, see 4.12.)
* **A3**: a snapshot's `ConfState` is the configuration of the committed prefix up to its
  index (the application's `CreateSnapshot` passes the `ConfState` its `ApplyConfChange`s
  produced). Like A1 an obligation of the application; `MsgSnap` is accepted by the step
  specs only at a non-joint configuration (stage A2).
* `DisableConfChangeValidation = false` (already `newRaft`'s premise).
* **No panic**: every committed conf entry applies (`ccApplyM ... = some _`), and every
  configuration tracks fewer than `2^62` ids. An entry that would panic every node
  (`issues/raft-unknown-transition-panic.md`, `issues/raft-joint-empty-transition-panic.md`,
  "removed all voters") is applied by no node of the argument: `cfgFold` is `none` past it and
  `RawNode.ApplyConfChange.spec` requires `some`.
* Synchronous storage (no `AsyncStorageWrites`): see 4.10 for the window it would open.

## 1. Definitions

**Logs and positions.** A node's full log is `fp ++ log` from `base0` (the existing
`FullOk`), so the entry at log index `i ≥ 1` is at list position `i - 1`. All logs below are
full logs. `IsConfEnt e` (`CCModel.lean`): `e.Type' ∈ {1, 2}` (`EntryConfChange`,
`EntryConfChangeV2`), what `hasUnappliedConfChanges` and `stepLeader` test.

**Decoding.** `dec : Entry → Option CCOp` gives a conf entry's change as `applyConfChange`
takes it (`CCOp = transition × changes`, `AsV2`). It is a function of the entry: the entry's
`Data'` slice was proposed with bytes recorded persistently (`isPropData`, agreement), and a
conf entry's bytes decode (`CCDecodes`: `stepLeader` `Unmarshal`s them and panics otherwise).
The Lean statements are generic in `dec`.

**Configurations.** `ccStepB op s` is `ccApplyM op.1 op.2 s` (`raft.applyConfChange`'s
choice of `LeaveJoint`/`EnterJoint`/`Simple`, `none` on every `confchange` error) followed by
the size check; `entStep` applies a conf entry's decoded change and leaves the state on any
other entry; `cfgFold dec s l` folds `entStep` over `l` (`none` if any step is). The
configuration of a log prefix `X.take a` is `cfgFold dec c0 (X.take a)`.
`confCount l` is the number of conf entries of `l`, `confPos l` their positions
(`mem_confPos`, `length_confPos`).

**Configuration index.** For a configuration reached as `cfgFold dec c0 (X.take a)`, its index
is `j = confCount (X.take a)`. Committed prefixes agree, so for the committed log `P` (the
global `ownCommitted` log) `C_j := cfgFold dec c0 (P.take a)` for any `a` with exactly `j`
conf entries in `P.take a` is well defined, and `P` only grows. Write `p_1 < p_2 < ...` for
`P`'s conf positions (as log indices). Facts below record a prefix length `a`, never only a
configuration value (different `j` may give equal values; the index is what the case
analysis needs).

**Lean (`CfgOverlap.lean`), all proved, no `sorry`, no axiom:**

* `QOverlap c1 c2 := ∀ q1 q2, JQuorum c1 q1 → JQuorum c2 q2 → ∃ x, x ∈ q1 ∧ x ∈ q2`;
  `QOverlap.symm`, `QOverlap.refl` (incoming ≠ ∅), `JQuorum_incoming`, `JQuorum_intersect`.
* `CfgOk s := CfgInv s ∧ s.cfg.incoming ≠ ∅ ∧ GMap.size s.cfg.ids < 2^62`.
* `maj_symdiff_overlap : symdiffN l r ≤ 1 → IsQuorum l q1 → IsQuorum r q2 → ∃ x, x ∈ q1 ∧ x ∈ q2`.
* `simpleM_overlap`, `enterJointM_overlap`, `leaveJointM_overlap`, `ccApplyM_overlap`: from
  `... = some s'`, `CfgOk s` and `GMap.size s'.cfg.ids < 2^62`: `QOverlap s.cfg s'.cfg ∧ CfgOk s'`.
  (`Simple`: both non-joint, `symdiff ≤ 1` once the `int` cannot wrap (`not_symdiffTooBig`).
  `EnterJoint`: the new outgoing half is the old incoming set. `LeaveJoint`: the incoming
  half is kept.)
* `cfgFold_append`, `cfgFold_ok` (`CfgOk` is kept along a fold), `cfgFold_zero` (no conf
  entry: same state), `cfgFold_le_one_overlap`, and
  `fold_adjacent : i ≤ j → confCount (l.take j) ≤ confCount (l.take i) + 1 → CfgOk s0 →
  cfgFold dec s0 (l.take i) = some si → cfgFold dec s0 (l.take j) = some sj → QOverlap si.cfg sj.cfg`
  (`fold_adjacent'`: either order). So `QOverlap C_j C_j'` whenever `|j - j'| ≤ 1`.

## 2. State

Per node, beyond `PState`: `applied` (`raftLog.applied`), `pci` (`pendingConfIndex`), the
configuration index `a` (the configuration is `cfgFold dec c0 ((fp ++ log).take a)`),
whether a snapshot is pending (`hasNextOrInProgressSnapshot`).

Ghost, beyond today's:

* **Campaign record** of `c` at `T`: `(F0, k)`, the campaign log and the commit index at
  campaign, with `j_c := confCount (F0.take k)` and, for every conf position `p ≤ k` of `F0`,
  a witness (below) of term `< T`. **[gap 3]** (today `isCamp γ c T F0` has no `k`.)
* **Winners table** in `raftCommitInv`: `T ↦ (winner, V, k)`, `V` a `JQuorum` of the winner's
  configuration `C_{j_c}` of granted votes. Replaces `isWin`'s `IsQuorum γ.reCfg V`; one entry
  per term (that is election safety, `ES` below).
* **Commit fact** `cqW t n G a`: today's `cq t n G` (term `t` at `n` in `G`, `leadFull t G`,
  a quorum acknowledging `t` up to `n`) with the quorum a `JQuorum` of
  `cfgFold dec c0 (G.take a)`, `a ≤ n`, `G.take a` committed, and
  - **at most one** conf entry of `G` above `a` **[gap 1]**;
  - for every conf position `p ≤ a` of `G`, a **witness**: `cqW t' n' G' a'` with `t' ≤ t`,
    `p ≤ n'`, `a' < p`, `G'` agreeing with `G` up to `p`, and `confCount (G'.take a') =
    confCount (G.take (p - 1))` (its configuration is exactly the one just before `p`).
  The definition recurses on `a` (a witness has `a' < p ≤ a`): well founded, a plain
  recursion on `Nat` in Lean, no guardedness needed.
* **`W(n)`** (node-local) **[gap 5]**: for every conf position `p ≤ commit` of `n`'s log, a
  witness `cqW t' n' G' a'` as above (agreeing with `n`'s log up to `p`) with `t' ≤ term`.
  A candidate's (from its campaign record) are of terms `< T`.
* **Messages**: an `MsgApp` carries, for its sender's log slice and `m.commit`, I1 (below) of
  `(prefix ++ entries, m.commit)` and the sender's witnesses for the conf positions
  `≤ m.commit`; a heartbeat and an `MsgSnap` carry the witnesses up to their commit index.

## 3. Invariants

* **Cfg** (A1): `cfgFold dec c0 ((fp ++ log).take a) = some cfg` with `CfgOk`,
  `applied ≤ a ≤ commit`, `(fp ++ log).take commit` committed. A leader, candidate or
  pre-candidate has no pending snapshot and `base ≤ applied`.
* **I1** (every node, every message's slice): if `p1 < p2` are conf positions of the log then
  `p1 ≤ commit`. Hence **at most one conf entry above `commit`**.
* **I2** (campaign): `F0` has no conf entry in `(applied, k]` (the guard), so the
  configuration at campaign is `cfgFold dec c0 (F0.take k)` (any `a ∈ [applied, k]` folds to
  it), and by I1 `F0` has at most one conf entry above `k`.
* **I3** (leader): (a) every conf entry of its log is at a position `≤ pci`; (b) at most one
  conf entry of its log is above `applied` (hence above `a`).
* **W(n)** as above; **ES**: one table entry per term.

## 4. The rules

Each `StepC` rule at the node's configuration `c = cfgFold dec c0 (log.take a)`, and the rules
the reconfiguration adds (4.9-4.11).

**4.1 campaign** (`hup`, `raft.go:968-988`; pre-vote: the guard is checked at `hup`, the
campaign after a pre-vote win (`stepCandidate`) checks nothing). Premises: not leader,
`promotable` (`id ∈ c.voters`, no pending snapshot), no conf entry in `(applied, commit]`
(`hasUnappliedConfChanges`). Record `(F0, k) = (log, commit)`; I2 holds by the guard and I1;
the witnesses of `W(n)` have terms `≤` the old term `< T`. A pre-candidate's log and commit
do not change until its campaign (any `MsgApp`/heartbeat/`MsgSnap` of its term makes it a
follower), `applied` only grows, and no conf entry is in `(applied, commit]`, so the guard
still holds at the campaign. **The configuration is fixed from campaign to win**: the only
conf entries the application may apply are in `(applied, applying] ⊆ (applied, commit]`
(A1), none; `restore` only runs at a follower. (So the stage-A2 panic, a removed candidate
winning, `issues/raft-advance-before-applyconfchange.md`, is excluded by A1.)

**4.2 grantVote / rejectVote**: no configuration involved (raft votes whatever its own
configuration, learners and removed nodes included).

**4.3 win**: `JQuorum c (granted votes)`; `win_fresh` (section 5) adds the table entry.
`becomeLeader` sets `pci := lastIndex` (`raft.go:953`) and appends the empty normal entry:
I3(a) holds; I3(b): no conf entry in `(applied, k]` (I2, `applied` only grew), at most one
above `k` (I1).

**4.4 propose** (`stepLeader` `MsgProp`, `raft.go:1295-1333`; the model's `propConf`). A conf
entry is kept iff `pci ≤ applied` and the joint/leave shape matches; then
`pci := lastIndex + i + 1`. I1: every earlier conf entry is `≤ pci ≤ applied ≤ commit`.
I3(a): the new `pci` is the new entry's position. I3(b): every other conf entry is
`≤ applied`. A second conf entry of the batch is refused (`pci > lastIndex ≥ applied`).
Auto-leave (`appliedTo`, `raft.go:740-761`) is this rule (an empty `ConfChangeV2` stepped as
`MsgProp`), with the same checks. (Validation is the leader's only defence: the `Changer`'s
errors surface at apply time, as panics: `issues/raft-joint-empty-transition-panic.md`.)

**4.5 appAccept** (`handleAppendEntries`, `maybeAppend`). New log: the sender's log up to
`lastnewi`, then (only if no entry conflicted) the old tail beyond it; new commit
`max(commit, min(m.commit, lastnewi))`. I1: if `p1 < p2 ≤ lastnewi`, both are in the
sender's slice, whose I1 gives `p1 ≤ m.commit`, so `p1 ≤ min(m.commit, lastnewi)`. If
`p2 > lastnewi`, no entry conflicted, so the log is unchanged (every sent entry matched) and
the old I1 applies with a commit no lower. `W`: new conf positions `≤` the new commit get
the message's witnesses (terms `≤ m.term = term`). Cfg: `a` unchanged, commit only grows.

**4.6 heartbeat** (`commitTo(m.Commit)`): commit only grows: I1 kept; `W` from the message.
**appStale / appReject / appResp / beat / reMatch / drain / readFwd / readState / sendFree /
zeroAck / takeReads**: nothing configuration-related moves.

**4.7 commit** (`maybeCommit`, also after `switchToConfig`): `JQuorum c (ackedBy n)`, term `t`
at `n`, `commit < n`. The new fact is `cqW t n G a` with `G` the leader's full log and `a` its
configuration index (`a ≤ commit < n`): at most one conf entry of `G` above `a` by I3(b);
the witnesses for conf positions `p ≤ a` come from `W(L)` (`p ≤ a ≤ commit`, terms `≤ t`).
`commit_extend` then extends the global log as today (`cq_agree`, now on `cqW`, section 7).
**Witness construction**: the new conf positions `p ∈ (commit, n]` (at most one, I3(b),
since `commit ≥ applied`) get the new fact itself as witness: `t ≤ t`, `p ≤ n`, `a < p`, and
every conf entry before `p` is `≤ a` (another one in `(a, p)` would be a second conf entry
above `applied`). So `W(L)` extends to the new commit. Well-foundedness: a witness's index
`a' < p ≤ a`. **[gap 5]**: a witness cannot be "the first commit of `p`": a stale leader of
an earlier term can commit `p` after a later term did, and its fact needs witnesses of terms
`≤` its own; `W` gives exactly that, since a node's commit only moves by its own commits
(witnessed at its term) or by messages of its term.

**4.8 snapRestore / snapFastfwd / snapStale**: restore only at a follower and only for an
index above the commit (`restore`, `raft.go:1849-1931`): log `[]` at base `m.index`, commit
`m.index`, configuration the snapshot's `ConfState` (A3: `cfgFold` up to `m.index`), `a :=
m.index > applied` with the snapshot pending, so unpromotable (`promotable`,
`raft.go:1934-1937`) until `Advance` applies it (`appliedSnap`: `applied = m.index`).
I1 trivially (no entry above the base); `W` from the message. Fast-forward: commit only.

**4.9 Advance / applied** (new): `applied` moves to `applying ≤ commit`; by A1 every conf
entry up to it is already applied (`a ≥ applied`). Auto-leave as 4.4.

**4.10 ApplyConfChange** (new; `ApplyCCOkC` of stage A2): `a` moves past the next conf entry
(in `(a, applying]`); `cfgFold` gives the new configuration (some, by the no-panic scope).
A leader may then commit (4.7 at the new configuration). Nothing else changes (I1, I3, `W`
do not mention the configuration). With asynchronous storage writes, `stableSnapTo` (the
append response) and `appliedSnap` (the apply response) can be stepped apart: in between
the node is promotable with `applied < base`, and `hasUnappliedConfChanges` scans compacted
entries and `Panicf`s -- a liveness/panic matter, out of scope (synchronous `Advance` steps
both).

**4.11 leader step-down on removal** (new; `switchToConfig`, `raft.go:1986-1994`): with
`stepDownOnRemoval` a removed or demoted leader becomes a follower at the same term. The
model's `abandon` excludes leaders, so this is a new rule: harmless for the invariants (it
voted for itself in `T`, cannot vote again in `T`, cannot campaign in `T`), but today's ghost
(known leaders, `klOk`) assumes a leader stays leader for its term and must be checked.
Without `stepDownOnRemoval` the removed leader stays leader, unpromotable, committing with
quorums of its configuration (which excludes it): nothing in the argument needs it to be a
voter (stage A2's code-level spec requires the step-down for its own reasons).

**4.12 learners, removed and new nodes**: only voters of their own configuration campaign
(`promotable`); a learner's or non-member's votes count only through `JQuorum` (`IsQuorum`
intersects with the half). A node whose configuration is not yet `cfgFold dec c0 _` (added,
not yet caught up) neither campaigns nor leads.

## 5. The winners table and `win_fresh`

Today `isLeader_unique` intersects two winning quorums of one voter set. With configurations
`C_j`, `C_j'` of two winners of `T` that are far apart (`|j - j'| ≥ 2`) the quorums need not
meet, and the argument goes through leader completeness at `T` -- whose adjacent case uses
election safety at `T` (the `d` branch of `lc_core`: a voter that voted knowing a leader of
`T`). The table breaks the circle by real-time order: when `c` wins `T`, every entry already
in the table satisfies ES and hence (section 7, by induction on terms) `lc_core` at `T`.

**`win_fresh`**: `c` wins `T` with `V` (`JQuorum C_{j_c}`, `j_c` from its campaign record), and
the table has `c' ≠ c` at `T` (`c` is not in it: a candidate of `T` never led `T`) with `V'`,
`j_{c'}`. Contradiction:

* `|j_c - j_{c'}| ≤ 1`: `QOverlap` (`fold_adjacent` on the longer of the two committed
  campaign prefixes) gives `v ∈ V ∩ V'`, who voted for both in `T`: `isVote_agree`.
* `j_{c'} ≤ j_c - 2` (the table's winner is older): `c`'s campaign commit `k_c ≥
  p_{j_{c'}+2}`; its witness `w` for `p_{j_{c'}+2}` has term `< T` and configuration index
  `j_{c'} + 1`, adjacent to `c'`'s. `lc_adj(T, c', w)` (section 7; `c'` is in the table, so
  its `d` branch is closed by ES) puts `G_w` up to `n_w ≥ p_{j_{c'}+2}` into `F0_{c'}`, so
  `F0_{c'}` has the conf entries `p_{j_{c'}+1}` and `p_{j_{c'}+2}`, both above `k_{c'}` (the
  first one `≤ k_{c'}` would give `F0_{c'}.take k_{c'}` more than `j_{c'}` conf entries):
  two conf entries above the commit, against I1 at `c'`'s campaign.
* `j_c ≤ j_{c'} - 2` (the new winner is older) **[gap 2]**: symmetrically, `c'`'s witness `w`
  for `p_{j_c+2}` (term `< T`, index `j_c + 1`), and `lc_adj(T, c, w)` for the *new* winner
  would put `p_{j_c+1}, p_{j_c+2}` above `k_c`. But `c` is not in the table, so `lc_adj`'s
  `d` branch is open: a voter `v ∈ V ∩ Q_w` may have voted for `c` knowing a leader `ldr` of
  `T` with `v ∉ V_ldr`; ES of the table gives `ldr = c'`, which is no contradiction. What
  that branch costs is the history bound `T + 1` (`vbnd T true`): `v`'s vote-time log may
  hold entries it got from `c'` at `T`, i.e. `hist`'s `okL` logs include leader logs of term
  `T`, which are `c'`'s. Those agree with `G_w` up to `n_w` by `lc_core(T, c', w)` (`c'` is in
  the table; `w`'s term `< T`): `c'`'s logs extend `F0_{c'}`, which reaches its own last
  entry. With that extra case in `lc_agree`, the adjacent argument for `c` goes through
  (`v`'s vote-time log has no entry of term `T`: it is at most as up to date as `F0_c`,
  whose terms are `< T`) and gives the contradiction with I1 at `c`'s campaign.

So `lc_adj` takes, instead of "`c` is in the table", the hypothesis "every leader of `T` that
a voter of `V` knew at its vote is `c`, or satisfies `lc_core` at `T`".

## 6. Commit facts and their witnesses

As in 4.7. Each `cqW t n G a` is created inside `raftCommitInv` by `Step.commit` from the
leader's state (I3(b) and `W(L)`), so every commit fact anywhere has its witnesses, and the
recursion bottoms out at configuration indices with no conf position below them (`a < p_1`).
The witness agreement (`G'` agrees with `G` up to `p`) is stored, not derived, so that
using a witness needs no `cq_agree` at an unknown term.

## 7. Leader completeness with configurations

Fix a winner `c` of `T` (table entry `(c, V, k_c)`, campaign log `F0`, `j_c = confCount
(F0.take k_c)`), and a commit fact `cqW t n G a` with `t < T`, quorum `Q` (a `JQuorum` of
`C_{j_m}`, `j_m = confCount (G.take a)`). **`lc_core(T)`**: every full log `X` with records
that reaches `F0`'s last entry has term `t` at `n`. By strong induction on `T`; at `T`,
first the adjacent case for every `t < T`, then the far cases.

* **`|j_c - j_m| ≤ 1` (`lc_adj`)**: `QOverlap` gives `v ∈ V ∩ Q`; the old argument verbatim
  (`tbl_voter`, `hist` bounded by `T` once the `d` branch is closed, `lc_agree` with the
  induction hypothesis below `T`, the up-to-date comparison: same last term by `recs_chain`,
  later last term `tc < T` by the induction hypothesis at `tc`). Only `quorums_intersect_cfg`
  is replaced, by `QOverlap`; the `d` branch uses ES (section 5).
* **`j_c ≥ j_m + 2`**: `p_{j_m+1}, p_{j_m+2} ≤ k_c` (the candidate's configuration has
  `j_c` conf entries, all `≤ k_c`). If `n ≤ k_c`: `F0`'s committed prefix covers `n`; the
  commit fact that justifies `k_c` (term `< T`) and `cqW t n G a` agree up to `n`
  (`cq_agree`, induction hypothesis at the larger of the two terms, `< T`); `X` agrees with
  `F0` up to `F0`'s last index (`recs_chain`, log matching). If `n > k_c`: `G` agrees with
  `F0` up to `k_c` (same `cq_agree`), so `G`'s conf entries `j_m + 1` and `j_m + 2` are
  `≤ k_c < n` and `> a` (`G.take a` has `j_m`): two conf entries of `G` above `a`, against the
  commit fact's at-most-one **[gap 1]**.
* **`j_c ≤ j_m - 2`**: the witness `w = cqW t_w n_w G_w a_w` of the commit fact for the conf
  position `p_{j_c+2} ≤ a` has `t_w ≤ t < T`, `n_w ≥ p_{j_c+2}`, configuration index
  `j_c + 1`: adjacent. `lc_adj(T, c, w)` puts term `t_w` at `n_w` into `F0`, so `F0` agrees with
  `G_w` up to `n_w` and has the conf entries `p_{j_c+1}, p_{j_c+2}`, both above `k_c` (as in
  section 5): against I1 at `c`'s campaign. (The design said "above the candidate's applied
  index, against I2"; above `k_c` is stronger and needs I1 only.)

The induction is well founded: the far cases use the induction hypothesis below `T` and the
adjacent case at `T`; the adjacent case uses ES at `T` (table members) or, in `win_fresh`,
`lc_core(T)` of the table's member (section 5), never the far cases at `T` for the same `c`.
The witness's own witnesses are used when `lc_core` is applied to a witness (read index, 8;
`win_fresh`'s `lc_core(T, c', w)` meets only `j_{c'} ≥ j_w + 1`, whose far case uses `w`'s
at-most-one, not its witnesses).

`cq_agree`/`cq_lt_agree` keep their proofs (`lc_core` for the later term's winner, which is
in the table). Every use of `isLeader_unique` (`lc_core`'s `d` branch, `read_arrive`'s
own-term case, `leadFull_agree`) becomes ES of the table.

## 8. Read index

At a request's arrival the leader `L` of `T` (commit at an entry of `T`) records `readOk`
(the global log's justification is of term `≤ T`, as today), or *dooms* the record with the
global log's commit fact `cqW t n G a`, `t > T` (its quorum acknowledged at `t > T` before
the arrival). The record now keeps the commit fact itself (with its witnesses: the
"evidence tree"), not just `(t, q)`. At confirmation a quorum `Q` of `C_{j_r}` (`L`'s
configuration then, `JQuorumAcked`) answered a heartbeat of `T` sent after the arrival, so no
member of `Q` had acknowledged above `T` before the arrival (`ownRaftGhost_not_doomed`).
**`rqRecOk_confirm`**: the record is not doomed. With `j_m` the doom fact's index:

* `|j_r - j_m| ≤ 1`: `Q` meets the doom quorum: a member acknowledged at `t > T` before the
  arrival.
* `j_r ≥ j_m + 2` **[gap 4]**: `L`'s committed prefix has `p_{j_m+2} ≤ a_L`; `W(L)`'s witness
  `w_L` for it has term `≤ T < t`. `lc_core(t, ldr_t, w_L)` (the doom fact's leader is in the
  table) puts `G_{w_L}` up to `p_{j_m+2}` into its campaign log, which `G` extends: `G` has
  conf entries `j_m + 1` and `j_m + 2` above `a` -- against the doom fact's at-most-one. (Not
  "unless the reader's committed prefix covers the entry": the doom fact's `n` plays no
  part.)
* `j_r ≤ j_m - 2`: the doom fact's witness `w` for `p_{j_r+2}` (index `j_r + 1`, adjacent to
  `j_r`, term `t_w ≤ t`). If `t_w > T`: `Q` meets `w`'s quorum, whose members acknowledged at
  `t_w > T` before the arrival (the witness predates the doom fact). If `t_w < T`:
  `lc_core(T, L, w)` puts `G_w` up to `p_{j_r+2}` into `L`'s campaign log; if `t_w = T`, `G_w`
  is an earlier log of `L` itself. Either way `L`'s current log has the conf entries `j_r + 1`
  and `j_r + 2`, both above `a_L ≥ applied` (`L`'s configuration has `j_r`): against I3(b).

## 9. What B2 should do first

1. **The model**: `PState` gains `applied`, `pci`, the configuration index and the pending
   snapshot; `StepC`'s campaign gets the guard and `promotable`, `propose` gets `propConf`
   with `pci`/`applied` and the joint checks (stage A2's "Left": `propConf` at a joint
   configuration), and three new rules: `Advance` (applied), `ApplyConfChange` (the
   configuration index past one conf entry, `ApplyCCOkC` read as a step), the leader's
   step-down. Prove the old relation is the new one at a fixed configuration with no conf
   entry applied (as `step_iff_stepC`).
2. **I1 and I3, pure**: as `Prop`s on `PState` and on `MsgApp` slices, with one preservation
   lemma per rule (section 4) -- no ghost state needed, and they are what everything else
   rests on.
3. **The decoder** as a ghost-derived function (`isPropData` agreement), and `Cfg` stated
   with `cfgFold`; the bootstrap/added-node scope (section 0) fixed.
4. Then the ghost: the campaign record's `k` and witnesses, `cqW` with its recursion on
   `a`, `W` in `ownLogGhost` and the message knowledge, the winners table with `win_fresh`,
   `lc_core`/`lc_adj` restated (the induction hypothesis structure of section 7), read index.
