<!-- 2026-11-08: a reading of each etcdraft.tla fix (etc/tla-fixes/) against Ongaro's thesis, the Raft paper,
the thesis's raft.tla and raft's documentation, by a subagent; the downloads it cites under scratchpad/ were
not kept. Item numbers are its own; etc/tla-fixes/README.md maps them to the patches. -->

# Are the etcdraft.tla fixes justified by Raft's design?

Assessment of the ten `issues/raft-tla-*` findings (etcd-io/raft `c51f010`, = v3.7.0 for these files)
against Raft's intended design, independent of "the Go code does it".

## Sources

- **Thesis**: D. Ongaro, *Consensus: Bridging Theory and Practice*, Stanford PhD thesis, 2014. The PDF
  came from `web.stanford.edu/~ouster/cgi-bin/papers/OngaroPhD.pdf` and was converted with pdftotext
  (`scratchpad/thesis/thesis.txt`). Citations give the **printed page** and, in brackets, the PDF
  page. The summary figures (Fig. 3.1, Fig. 5.3) are images and did not extract. For their text I
  quote the paper's identical Figures 2 and 13.
- **Paper**: Ongaro & Ousterhout, USENIX ATC 2014 (`raft.github.io/raft.pdf`, `scratchpad/thesis/paper.txt`).
- **Thesis TLA+**: `ongardie/raft.tla` master (`scratchpad/thesis/tla/raft.tla`). This is the
  thesis's Appendix B spec plus its 2014-12 fixes. It has a static `Server` set with no membership
  changes, no snapshots and no durable-state split.
- **raft sources**: `scratchpad/raft-main` (`raft.go`, `log.go`, `doc.go`, `design.md`, `confchange/`).

## Summary

| # | Item | Fixed model is... | Original model | Could the fix mask a raft bug? | Verdict |
|---|------|-------------------|----------------|--------------------------------|---------|
| 1 | restart-initstate-unmatched | not a model change (Go trace logging) | n/a | no; but see the note on restored configuration | **code-only** (instrumentation) |
| 2 | learner-demotion-unmodelled | a single-server removal from the voting set (thesis §4.3) plus a non-voting member (§4.2.1) | a permitted subset (never demotes) | the config change: no. **The demoted leader keeps leading** (without `StepDownOnRemoval`), which departs from thesis §4.2.2 | **design-justified** for the change; flag leader continuation |
| 3 | snapshot-committed-follower | InstallSnapshot's receiver rules (thesis §5.1, paper Fig. 13, steps 6-7); the commit fast-forward is a safe optimization | **wrong**: it ignores a snapshot beyond the follower's commit index, contrary to Fig. 13 | no | **design-justified** |
| 4 | snapshot-response-subtype | a message-label choice | equally permitted | no | **implementation-choice** (subsumed by 3) |
| 5 | readded-member-matchindex | a conservative reset of volatile leader state (`design.md`: "match is set to zero") | also sound in the thesis's world | no; the opposite choice would be the bug (raft's heartbeat commit trusts `Match`) | **implementation-choice** |
| 6 | msgapp-commit-unclamped | Fig. 3.1 / paper Fig. 2 verbatim ("leaderCommit: leader's commitIndex"; the receiver clamps) | equivalent state effect (the thesis's raft.tla clamps at the sender too) | no | **design-justified** |
| 7 | vote-refused-known-leader | a strengthening of the vote guard; same spirit as thesis §4.2.3 | the thesis's "first-come-first-served" rule, also permitted | no: safety- and liveness-neutral, because a second candidate cannot win a term that already has a leader | **implementation-choice** |
| 8 | leader-completeness-stale-leader | the repaired guard is essentially the thesis's own **Theorem 1** (App. B) | **wrong**: guards on the entry's term, not its commit term | no | **design-justified**; prefer #549's form |
| 9 | more-up-to-date-cut-batches | the invariant is **not a Raft property** (false in the thesis's own raft.tla too) | wrong | no | drop it, or replace it with the two correct halves below |
| 10 | restart-truncated-log | thesis §3.8 / Fig. 3.1 (the log is persistent state; restart restores what was persisted) | **wrong** beyond the TLC error: it can restore entries that were never persisted | no | **design-justified** |

None of the fixes is "code-only" in the dangerous sense, and none is suspicious as a model change.
The one place where raft departs from the thesis in a way a careful spec should flag is item 2's
corollary: a leader removed or demoted from the voters keeps leading.

---

## 1. raft-tla-restart-initstate-unmatched

The fix is to raft's trace logging (`raft.go:469`, `traceInitState` before `confchange.Restore` and
`loadState`), not to the model.

1. **Design.** Nothing in the design is at stake. The model's `Restart` restores the durable state,
   as the thesis requires (§3.8, p.27 [45]: each server "persists its current term and vote ... [and]
   new log entries"; "the commit index ... can safely be reinitialized to zero"). The logged event
   should describe the state the node restarts in.
2. **Original.** Not applicable: the model was right, and the instrumentation recorded a pre-load state.
3. **Adversarial.** The patch also stops logging the `ApplyConfChange` and `BecomeFollower`
   transitions that happen while the persisted state loads. These are not protocol steps, so hiding
   them is harmless.
   One real gap stays open, and the write-up already notes it. raft restores the configuration from
   the snapshot's `ConfState` only (the application then re-applies later configuration entries). The
   model's `Restart` restores `durableState[i].config`, the configuration at the last `Ready`. So a
   restarted raft node can briefly run with an *older* configuration than the model gives it.
   - The thesis has no such window: "each server always uses the latest configuration found in its
     log" (§4.1, p.35 [53]).
   - raft deliberately applies configurations at apply time (`doc.go:263-270`: "equivalent in terms
     of safety").
   - The vote comment at `raft.go:1235-1240` itself points to a stale-configuration election bug
     (etcd-io/etcd#7625). That thread argues that apply-time activation is "undesirable (if not
     outright unsound)".

   Proving conformance with a model that restores the newer configuration may therefore hide
   behaviour that matters. This is not caused by this fix, but it is a nearby assumption to keep
   visible.
4. **Verdict: code-only** (instrumentation). It does not bake anything into the model.

## 2. raft-tla-learner-demotion-unmodelled

The candidate change: `AddLearner` also accepts a voter (`j \notin GetLearners(i)`) and appends
`newconf |-> GetConfig(i) \ {j}`, with `j` added to the learners.

1. **Design.**
   - In quorum terms, demoting a voter is removing one server from the voting configuration.
     Thesis §4.3 (p.35 [53]): "When adding a single server to a cluster or removing a single server
     from a cluster, any majority of the old cluster overlaps with any majority of the new cluster
     ... it guarantees the existence of 'the voter'." So the change is an instance of the thesis's
     single-server change.
   - The demoted server stays a non-voting member, as in §4.2.1 (p.37 [55]): "The leader replicates
     log entries to it, but it is not yet counted towards majorities for voting or commitment
     purposes."
   - raft documents demotion: `confchange/confchange.go:191-228` ("we either add a new learner or
     demote a voter"), `tracker/tracker.go:47-70`, and `Config.StepDownOnRemoval` (`raft.go:282-287`,
     "removed from the group or demoted to a learner").
2. **Original.** It is a permitted subset (it never demotes), not wrong. It is incomplete for raft's
   API.
3. **Adversarial.** The change itself is safe. The leader case is where raft departs from the design:
   - Thesis §4.2.2 (p.39 [57]): "If the existing leader is asked to remove itself from the cluster,
     it must step down at some point ... a leader that is removed from the configuration steps down
     once the Cnew entry is committed."
   - raft steps down only `if r.stepDownOnRemoval` (`raft.go:1986-1997`). Otherwise a demoted or
     removed leader keeps leading indefinitely, replicating to a cluster whose quorum excludes it.
     The comment there says "We prevent demotions at the time writing". That is stale:
     `makeLearner` demotes, and the issue's test does it.
   - `StepDownOnRemoval`'s own comment says "This behavior will become unconditional in the
     future" (etcd-io/raft#83). That is an admission that not stepping down is not the intended
     design.
   - The existing model already encodes the non-stepping-down behaviour for `DeleteServer(i, i)`.

   A fix that makes demotion of the leader keep it leading would bake in that same deviation. It is
   safe, since the leader does not count itself (thesis: "it replicates log entries but does not
   count itself in majorities", the "awkward mode"), but it is not the design's endpoint.
   Recommendation: model demotion as above, and make the post-commit step-down at least *possible*
   in the model (`StepDownToFollower` already allows it nondeterministically). Do not state any
   property that relies on the leader staying.
4. **Verdict: design-justified** for the configuration change. Flag the leader-continuation
   behaviour as a raft deviation from thesis §4.2.2, tolerated but not intended.

## 3. raft-tla-snapshot-committed-follower

1. **Design.**
   - Paper Fig. 13 (InstallSnapshot receiver), the same as thesis Fig. 5.3: "6. If existing log
     entry has same index and term as snapshot's last included entry, retain log entries following
     it and reply. 7. Discard the entire log. 8. Reset state machine using snapshot contents (and
     load snapshot's cluster configuration)."
   - Thesis §5.1 (p.52 [70]): "Usually the snapshot will contain new information not already in the
     follower's log. In this case, the follower discards its entire log ... If, instead, the follower
     receives a snapshot that describes a prefix of its log ..., then ... entries following the
     snapshot are still valid and must be retained."

   The patch's `HandleSnapshotRequest` is exactly this case split, and so is `raft.restore`
   (`raft.go:1852-1913`).

   Two additions are permitted:
   - **Ignoring a snapshot at or below the commit index.** The log effect is the same as step 6:
     committed entries match by State Machine Safety, so the follower holds the last entry and keeps
     its log.
   - **Fast-forwarding the commit index to the snapshot's index when the last entry matches.** The
     thesis says only "reply". This is safe because a snapshot covers only committed state. By Log
     Matching, the follower's prefix equals the snapshot's, so it is the same knowledge transfer as
     `leaderCommit`.
2. **Original: wrong.** Encoding a snapshot as an append at index 1 means any follower with
   `commitIndex >= 1` reaches only `AppendEntriesAlreadyDone`, which does nothing and replies its
   commit index. This contradicts Fig. 13 steps 6-7. It is safe, but it is a liveness bug in the
   model: the leader can only keep resending the snapshot.
3. **Adversarial.** I see no raft bug hidden here.
   - raft's reply (`handleSnapshot`, `raft.go:1832-1847`: `lastIndex()` on restore, otherwise
     `committed`) equals the patch's `Max({commitIndex[i], last})` in each branch.
   - One model-level caveat: the patch leaves `config` unchanged and relies on a later
     `ApplySimpleConfChange` (or the traced `ApplyConfChange`). Step 8 of the thesis and
     `raft.restore` switch the configuration atomically with the log. The model therefore admits an
     intermediate state (new log, old configuration) that raft never has. That is fine for
     conformance (a superset), but model checking may report spurious counterexamples from it.
4. **Verdict: design-justified.**

## 4. raft-tla-snapshot-response-subtype

1. **Design.** The thesis's InstallSnapshot has its own reply (Fig. 13: "Results: term"); raft
   answers with `MsgAppResp`. The design does not care. The model's `HandleAppendEntriesResponse`
   ignores `msubtype`, so the subtype is only a label for trace matching.
2. **Original.** Equally permitted.
3. **Adversarial.** Nothing to hide: the subtype has no semantic effect.
4. **Verdict: implementation-choice.** It is subsumed by item 3's handler, which answers `"app"`.

## 5. raft-tla-readded-member-matchindex

1. **Design.**
   - `matchIndex` is volatile leader state. Fig. 3.1 / paper Fig. 2: "index of highest log entry
     known to be replicated on server (initialized to 0 ...)".
   - raft's `design.md:7`: "If leader knows nothing about follower's replication status, `match` is
     set to zero."
   - For a server that leaves the configuration, the design says nothing (the thesis's raft.tla has
     no membership). Resetting to 0 is the conservative choice: `matchIndex` is a lower bound, and
     lowering it only delays commitment.
2. **Original.** It is also sound in the thesis's world. Thesis §3.8 (p.27 [45]): "If a server loses
   any of its persistent state, it cannot safely rejoin the cluster with its prior identity." A
   re-added ID therefore keeps its durable log, and within the leader's term an acknowledged prefix
   cannot be lost:
   - acknowledgements are sent only after persisting;
   - a same-term leader sends only agreeing entries;
   - a higher-term contact makes the leader's later messages rejected.

   So the old value is still a valid lower bound. This is a permitted choice, not wrong, but raft
   does not take it.
3. **Adversarial.** The reverse risk is the real one, and raft's reset is what avoids it.
   - raft's heartbeat skips the consistency check and sends `min(pr.Match, committed)`
     (`raft.go:694-708`: "The leader MUST NOT forward the follower's commit to an unmatched index").
   - With a retained stale `Match`, a re-added ID backed by fresh storage would receive a commit
     beyond its log. That makes `commitTo` panic ("Was the raft log corrupted, truncated, or lost?").
     The thesis forbids such a rejoin, but raft resets anyway (`confchange.go:231-271`), which is
     strictly more robust.
   - The fix does not mask a bug; the original would have hidden one if raft had kept progress.
4. **Verdict: implementation-choice.** The model should allow, and here must take, raft's reset.

## 6. raft-tla-msgapp-commit-unclamped

1. **Design.** Paper Fig. 2, the same as thesis Fig. 3.1, AppendEntries: "leaderCommit: leader's
   commitIndex". Receiver: "5. If leaderCommit > commitIndex, set commitIndex = min(leaderCommit,
   index of last new entry)". raft does exactly this:
   - the sender puts `Commit: r.raftLog.committed` in the message (`raft.go:651-658`);
   - the receiver computes `lastnewi = a.prev.index + len(a.entries)` and calls
     `commitTo(min(committed, lastnewi))` (`log.go:116,129`).

   "Index of last new entry" correctly means the last entry *of the request*, not the follower's
   last index, and raft gets that right (including the empty `MsgApp`, where `lastnewi = prev`).
2. **Original.** Also permitted, with an equivalent state effect. Clamping at the sender to
   `Min(commitIndex, lastEntry)` gives the same receiver state because the receiver clamps again.
   The thesis's raft.tla clamps at the sender (`mcommitIndex |-> Min({commitIndex[i], lastEntry})`,
   raft.tla:223). The fix changes only the message field.
3. **Adversarial.** None. Heartbeats keep `Min(commitIndex, matchIndex)` (raft's deviation from the
   thesis's heartbeat-as-empty-AppendEntries, discussed under item 5). The snapshot branch is
   unchanged.
4. **Verdict: design-justified.**

## 7. raft-tla-vote-refused-known-leader

1. **Design.**
   - Thesis §3.4 (p.16 [34]): "Each server will vote for at most one candidate in a given term, on a
     first-come-first-served basis (note: Section 3.6 adds an additional restriction on votes)". The
     paper's Fig. 2 says the same ("If votedFor is null or candidateId, and ... up-to-date, grant
     vote").
   - raft additionally refuses when it has no vote but knows the term's leader (`raft.go:1214-1218`:
     "...we haven't voted and we don't think there's a leader yet in this term...").
   - The thesis endorses a time-bounded relative of this rule, §4.2.3 (p.42 [60]): "if a server
     receives a RequestVote request within the minimum election timeout of hearing from a current
     leader, it does not update its term or grant its vote. It can either drop the request, reply
     with a vote denial, or delay the request; the result is essentially the same."
   - Refusing a vote is always safe: it shrinks the set of possible winners.
2. **Original.** This is the thesis's rule verbatim (the thesis's raft.tla:290 has the same
   `votedFor[i] \in {Nil, j}`), and it is permitted.
3. **Adversarial.**
   - The refusal is not time-bounded, unlike §4.2.3, and `doc.go:337-340` does not mention it. But
     it only applies within the same term. A second candidate in a term that already has a leader
     cannot win: a majority voted for the leader, and every member of it refuses the other candidate
     (Election Safety, Fig. 3.2). So the refusal is neutral for both safety and liveness.
   - `lead` is set only by append-type messages of the current term, which only that term's leader
     sends. It is set even when the append is rejected for a log mismatch (`raft.go:1722-1733`),
     which is still correct. The patch mirrors this.
   - The only cost is that the fixed model is now raft-specific (a deterministic refusal) rather
     than a superset that allows nondeterministic refusal. That is fine for proving that raft
     conforms.
4. **Verdict: implementation-choice.**

## 8. raft-tla-leader-completeness-stale-leader (invariant)

1. **Design.**
   - Fig. 3.2 (p.14 [32]): "Leader Completeness: If a log entry is committed in a given term, then
     that entry will be present in the logs of the leaders for all higher-numbered terms." The term
     is the **commit** term.
   - The §3.6.3 argument (p.24-26 [42-44]) starts "Suppose the leader for term T (leaderT) commits a
     log entry from its term" and concludes "the leaders of all terms greater than T must contain all
     entries from term T that are committed in term T". Step 9 extends this to entries committed
     indirectly, which are committed in the later term.
   - Formally (App. B, p.222 [240]), Definition 1 defines `committed(t)` as "present in every
     leader's log following t", stated over the history variable `elections`.
2. **Original: wrong.** It guards on `entry.term`, the creation term. An entry from term 2 that is
   committed in term 4 need not be held by a (stale) leader of term 3. Fig. 3.2 says nothing about
   that leader.
3. **The repaired guard** is `currentTerm[l] > entry.term /\ currentTerm[l] >= currentTerm[i]`.
   - **It is sound, and it is essentially the thesis's own state invariant.** App. B Theorem 1
     (p.227 [245]):
     `∀ i : ∀ ⟨index,term⟩ ∈ log[i] : index ≤ commitIndex[i] ⇒ ⟨index,term⟩ ∈ committed(currentTerm[i])`.
     That is, leaders of terms **> currentTerm[i]** hold `Committed(i)`. The thesis's proof sketch:
     "Followers update their commitIndex from the leader's only when they have a prefix of the
     leader's log".
   - **The step from `>` to `>=` also holds in etcdraft.** A server's commit knowledge in term t
     comes only from the leader of t: an append, heartbeat or snapshot of its current term, or its
     own commit as that leader. Otherwise it was learned in an earlier term and is covered by `>`
     (`currentTerm` is monotonic, Lemma 1).
     Restart restores a commit index and term that were persisted together, so the property
     survives with the item 10 fix as well. The snapshot handler of item 3 commits only to the
     current-term leader's committed index.
   - **The `entry.term` conjunct only weakens the guard.** #549's form,
     `currentTerm[i] <= currentTerm[l] => IsPrefix(Committed(i), log[l])`, is slightly stronger and
     also true: an entry of term `currentTerm[l]` in `Committed(i)` was created by `l` itself. It is
     a cleaner transcription of Theorem 1, so I recommend it.
   - **It is strictly weaker than Fig. 3.2.** It says nothing about a stale leader whose term lies
     in `(T_commit, currentTerm[i])`. The thesis guarantees that leader holds the entry, but `i` has
     moved past its term.
     Capturing the full property needs what the thesis uses, a history variable (`elections` /
     commit term): record each entry's commit term when a leader's `commitIndex` first covers it,
     and guard `currentTerm[l] > commitTerm[idx]`, or `>=` together with `l` being that term's
     leader.
   - For State Machine Safety, Theorem 1 is what the thesis's own inductive proof uses (it is
     "equivalent to the State Machine Safety property"), so the weakening loses nothing that the
     safety proof needs.
4. **Verdict: design-justified.** Use #549's form (Theorem 1 with `>=`). Add the commit-term history
   version if the full Fig. 3.2 statement is wanted.

## 9. raft-tla-more-up-to-date-cut-batches (invariant)

1. **Design.** The thesis never claims "any log at least as up to date as j's contains j's committed
   entries". It uses the up-to-date check only for a voter that holds an entry of the **committing
   term**:
   - §3.6.3 step 7 (p.25 [43]): "the voter's last log term was at least T (it contains the committed
     entry from term T)";
   - App. B, Lemma 8 step 10(a) (p.225 [243]): "LastTerm(voterLog) ≥ term, since ⟨index, term⟩ ∈
     voterLog". There ⟨index, term⟩ is *immediately committed* (Definition 2: acknowledged by a
     quorum in its own term).

   §3.6.1 (p.22 [40]) states the property that is actually wanted: "every committed entry must be
   present in at least one of those servers. If the candidate's log is at least as up-to-date as any
   other log in that majority ..., then it will hold all the committed entries". That is a statement
   about a whole quorum, not about each voter.
2. **Original: wrong.** The invariant's comment ("i receives a vote from j only if i has all of j's
   committed entries") is not a Raft guarantee. A follower can know a commit index while its last
   entry is older than the commit term. Raft may grant such a vote; the candidate still cannot win
   without a voter holding the commit-term entry.

   It is false in the thesis's own raft.tla too. I traced this by hand and did not model-check it.
   With 5 servers, the thesis spec sends one entry per AppendEntries with
   `mcommitIndex = Min(commitIndex, lastEntry)`:
   - the leader of term 4 commits index 7 via nodes 3 and 4;
   - after a rejection, it sends x (term 2, index 6) alone to node 5 with `mcommitIndex = 6`;
   - node 5 then has commit 6 and last term 2. Node 2's log ends at y (term 3, index 6) and lacks x.

   This is not specific to raft's batching.
3. **Adversarial.** No raft bug: the scenario arises in the thesis's protocol.
4. **What a correct statement looks like.** Split the invariant in two:
   - **(a) Equal last term, history-free, should hold** (the thesis's step 9 of Lemma 8):
     `LastTerm(log[i]) = LastTerm(log[j]) /\ Len(log[i]) >= Len(log[j]) => IsPrefix(log[j], log[i])`.
     The whole log, not just the committed part. Both last entries come from the one leader of that
     term, whose log only grows during the term, and Log Matching does the rest.
     Check this with TLC: it relies on the leader's sent entries being durable, which etcdraft
     ensures by flushing messages at `Ready`.
   - **(b) Greater last term, needs the commit term** (Definition 2): if `log[j]` contains an entry
     of term ≥ `commitTerm` at or after the committed index, and `LastTerm(log[i]) > LastTerm(log[j])`,
     then `IsPrefix(Committed(j), log[i])`. The leader that created i's last entry has term greater
     than the commit term, so it holds the entries by Leader Completeness, and Log Matching follows.

   Without the history variable, drop (b). QuorumLogInv plus item 8's invariant carry the safety
   argument.
5. **Verdict: drop** (it is not a Raft property). Replace it with (a), and add (b) if the commit-term
   history is introduced for item 8.

## 10. raft-tla-restart-truncated-log

1. **Design.**
   - Persistent state includes `log[]`, "updated on stable storage before responding to RPCs" (paper
     Fig. 2; thesis Fig. 3.1).
   - Thesis §3.8 (p.27 [45]): "Each server also persists new log entries before they are counted
     towards the entries' commitment".
   - The thesis's raft.tla `Restart` keeps `log` unchanged: the log is modelled as always durable.
   - raft's contract, `doc.go:75-77`: "Write HardState, Entries, and Snapshot to persistent storage
     ... when writing an Entry with Index i, any previously-persisted entries with Index >= i must be
     discarded."

   So the durable log is a sequence that changes only at persistence points, and a restart restores
   exactly that sequence. The patch (`durableState.log` holds the log itself) is an instance of this.
2. **Original: wrong, and for more than the TLC evaluation error.** `SubSeq(log[i], 1, len)` restores
   a prefix of the *in-memory* log. Suppose a conflicting entry is truncated and a different entry is
   appended at the same index before any `Ready`. A restart then "restores" an entry that was never
   persisted, where storage still holds the old one.
3. **Adversarial.** No raft deviation is hidden.
   - The model persists at `Ready`, atomically with the hard state. That matches the synchronous
     `Ready` contract (with `AsyncStorageWrites` the timing differs, but the model is still a
     sound abstraction).
   - The durable `commitIndex` is never above the durable log's length (`CommittedIsDurableInv`).
   - The restored configuration is another matter (see item 1): raft restores the snapshot's
     `ConfState`, the model restores `durableState.config`.
4. **Verdict: design-justified.**

---

## Surprises

- **`MoreUpToDateCorrectInv` is false in Ongaro's own raft.tla.** I worked this through by hand: one
  entry per message plus the sender-side commit clamp reproduces the item 9 counterexample. The
  thesis never states the invariant. Its proof uses the up-to-date check only for a voter that holds
  the committing term's entry.
- **The thesis already has the repaired leader-completeness invariant.** App. B Theorem 1 guards on
  the server's `currentTerm`, not on the entry's term. #549's repair is that theorem with `>=`. The
  full Fig. 3.2 statement needs a history variable, as the thesis uses (`elections`).
- **Demoted or removed leaders keep leading.** Unless `StepDownOnRemoval` is set, raft departs from
  thesis §4.2.2 ("must step down at some point"). The option's own comment says the behaviour will
  become unconditional (etcd-io/raft#83). The `raft.go:1988` comment "We prevent demotions" is
  stale. Do not let the fixed model make continued leadership a guarantee.
- **Apply-time configurations are raft's largest standing deviation from the thesis.** The thesis
  makes a configuration take effect on append (§4.1). Raft makes it take effect on apply
  (`doc.go:263-270`, which claims this is "equivalent in terms of safety"). Yet the comment at
  `raft.go:1239-1240` points to the stale-configuration election bug discussion (etcd-io/etcd#7625,
  where tbg calls apply-time activation "undesirable (if not outright unsound)"). Both etcdraft.tla
  and the item 1/10 restore paths bear on it: the model restores the latest persisted configuration,
  raft the snapshot's. A conformance proof should keep this assumption explicit rather than inherit
  it from the model.
- **The original snapshot encoding is a liveness bug in the model.** A follower that has committed
  anything never installs a snapshot, so the leader can only resend it.
