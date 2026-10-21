# T-S, stage S-0: the D22 plan checked against the proofs and the Go code (2026-10-19)

Stage S-0 of track T-S (`notes/decisions.md`, "T-S: the snapshot path, scope and staging
(D22)"): a pen-and-paper check, no Lean change. Part 1 is item (1) of the stage (D22a (A)
against the receiving raft's proof; "last log term ≤ term"), part 2 items (2)-(5) (the sender's
facts, the buckets' writers, `srvWTPool`'s users, the backend's holders across the swap). What
it changes in the plan is in `notes/decisions.md`, "D22 S-0 carried out". All by reading the
code at the pins (etcd fork `8a24be2a3`, raft fork `c8217eb9`); nothing run.

## Part 1. S-0 (1): D22a (A) against the receiving raft's proof, and "last log term <= term"

Pen-and-paper check, no Lean edit. Paths: `P/` = `Proof/go_etcd_io/raft/v3/`. Go at the pins:
raft `c8217eb9` (`.lake/go-src/raft`), etcd `8a24be2a3` (`.lake/go-src/etcd`).

### Verdict

**D22a (A) as written does not work.** The leader-prefix facts (`leadPrefix`, `plogTermAt … =
some logterm`, `lpfull`) and `commitIn … m.index m.term` are used for much more than deriving
`isCommitted`. Two things depend on them: the acknowledgement invariants (log matching against
the term-`T` leader's log), and the bound that the commit fact's term is at most the node's term.
In finding 2's stale case these facts are not just unprovable. Several `ownLogGhost` invariants
become **false** of the receiver's state: `TermsLe`, `commitIn` at its term, `acksOk`/`ackAgree`,
`histsOk`, and the reply's `ackIn`. A later campaign then breaks `CampOk`, which drives the
induction in Leader Completeness. No proof of the receiving `raft.Step` survives without
redesigning the protocol's invariants. The restated clause therefore cannot be reached through
`isMessage_snap_recontent` as S-b plans.

**The Figure-8 variant, which the doc's D22a/(B) text also notes, breaks things too.** In it the
sender has stepped down, applied a prefix `P` committed at a later term, and `appliedt ≤ m.Term`,
so `TermsLe` survives. `commitIn` at `m.term`, the reply's `ackIn`/`hist`, and `restore`'s "no ack
of this term above the snapshot" are still false. A check on `appliedt ≤ m.Term` alone is
therefore not enough. (Example: S1, leader of 4, has `(2, j)` at index `j`. The leader of 5
commits `(3, j)` with an entry `(5, j+1)`. S1 applies up to `j` in one batch and then merges an
old `MsgSnap` of term 4 with `(j, 3)`.)

**Recommendation: replace (A) with (D), a fork fix on etcd's side.** In `applyAll`, just before
`createMergedSnapshotMessage` (`server.go:1002-1009`), send the merged snapshot only when raft,
read *after* the batch, is still leader at `m.Term`. For example:
`st := s.r.Status(); if st.Term != m.GetTerm() || st.RaftState != raft.StateLeader { drop }`.

Why this suffices: every applied entry is in raft's log. If raft is leader at `T = m.Term` at the
moment of the check, its current log is a `leadPrefix` of `T` (`leadLogOwn`). That log contains
`P` up to `appliedi`, and its commit index is at least `appliedi`. So the **existing `.snap`
clause** holds of the merged message unchanged: the leader prefix at `(appliedt, appliedi)`;
`commitIn` at `appliedi` and `T`, lowered from the leader's own `commitIn` at its commit index;
and `isCommitted`.

The doc's two objections to (B) do not apply to this check:
- *Racy:* the certificate is historical, like a raft-produced `MsgSnap` still in flight after its
  leader stepped down, which the current proof already handles. Leadership ending after the check
  changes nothing.
- *Figure 8:* that shape needs the sender to be at a later term, which the check excludes.

The check must compare raft's **term**. etcd's cached `s.isLeader()` (lead from `SoftState`) is
not enough: a re-election at `T2 > T` passes it, and `s.Term()` is the term of the last applied
entry. Dropping the snapshot is harmless for liveness, because a node that is no longer leader at
`T` has also dropped that peer's progress.

What it costs:
- a spec of `node.Status` and `getStatus`. `node__run.lean:917` models `<-n.status` as never
  happening, and `getStatus` copies the progress map and the config. `RawNode.BasicStatus` is
  already proved (`P/RawNode__BasicStatus.lean`);
- a handout of the leader's log facts (below);
- one fork commit in etcd.

The receiving side, `isMessage`, `StepC.snap*` and LC are then untouched. If the user rejects a Go
change, the alternative is (A″) below: a protocol redesign, large, which still needs the same
raft-term knowledge at the sender.

### (a) Every use of the dropped facts

`isMessage_snap_inv` (`P/Protocol/Refinement.lean:274`) unpacks the clause
(`P/Protocol/GhostState.lean:242-256`). Envelope = `isLeader`, `src ≠ 0`, `dst`/tracked. Content =
`isCommitted P`, plus `logRecs P`, `FullOk P` and `isSnapMeta`; (A) must add these three to the
content, since `isCommitted` does not give them.

| Use | Where | Fact used | Survives with envelope + content? |
|---|---|---|---|
| receiver is not leader | `P/raft__Step.lean:170,433` (`isMessage_snap_isLeader`, `not_leader_of_msg`) | `isLeader` | **yes** |
| physical proofs | `raft__Step/MsgSnap*.lean`, `raft__handleSnapshot.lean`, `raft__restore.lean`, `InvRestore.lean` | none of the message's facts (grep: no `isMessage`/`leadPrefix`/`commitIn`) | **yes** |
| learn the leader (`kl`, `bnd`) | `vote_excl`, `ownLogGhost_learn` in `Refinement.lean:2829-2832`, `:2992-2995`, `:446` | `isLeader` | **yes** |
| snapStale: reply's `ackIn γ T s.commit` | `ownRaftGhost_step_stale` (`Refinement.lean:405`, `:422` `isMessage_leadPrefix`, `:427-437` `commitIn_ackIn`, `:349`) | some leader prefix + `lpfull` of `T`, not tied to the snapshot | **yes, if the envelope keeps "some `leadFull` of T"** (the original raft message has one). The doc's envelope lacks it: add it |
| fastfwd: new `commitIn (fp++log) m.index T` | `Refinement.lean:2856-2861` (`commitIn_move` from the leader's full log, `HFeq`) | leader prefix at `m.index`, `commitIn … m.index m.term` | **no**. Needs a commit fact at term `≤ T` (`commitJ`, `P/Protocol/Ghost.lean:2556-2562`, `t ≤ tm`). False in the stale and Figure-8 cases (committed at `t_c > T`) |
| fastfwd: `isCommitted (cprefix)` | `Refinement.lean:2862-2867` (`full_take_eq` against the leader's log, then `Hmcm`) | `isCommitted` + records | **yes**: `full_take_eq` against `P` with `logRecs P` |
| fastfwd: new ack's `hist` | `Refinement.lean:2875-2880` (`hist_of_commit`, `StepGhost.lean:1265`) | the new `commitIn` at `T` | **no**, as above |
| fastfwd: reply's `ackIn γ T m.index` | `Refinement.lean:2885-2891` ("index in the leader's log, R8a") | `leadPrefix` with `m.index` in range | **no**. Replaceable by `commitIn_ackIn` only given `commitIn` at `T` |
| restore: the prefix `fp'`, `logRecs_take`, A3 | `isMessage_snap_prefix` (`Refinement.lean:2902`); `StepGhostMode.lean:562`; `RefinementDyn.lean:951-955`; `StepRInv.lean:632` | a recorded prefix ending at `(logterm, index)` | **yes**, from `P` |
| restore: `baseOk` | `Refinement.lean:2997` | `isSnapMeta` | **yes** |
| restore: "no ack of term T above the snapshot" | `Refinement.lean:2986-2991` (`ackAgree_term`, `Ghost.lean:2989`, with `Hp'`) | the T-leader's log has `(logterm, index)` | **no**. False in the stale and Figure-8 cases: the receiver may have acked `(T, j > idx)` to the old leader before |
| restore: `TermsLe` of the new full log | `Refinement.lean:3000-3010` (`HwLf.2`, the term bound of `lpfull`, `Ghost.lean:2235`) | `lpfull`'s "no term above t" | **no**. False in the stale case (`T' > T`) |
| restore: `commitIn` of the new log at `T` | `Refinement.lean:3013-3016` (`commitIn_agree`) | `commitIn … m.index m.term` | **no** (as fastfwd) |
| restore: old acks' `hist` moved to the new log | `Refinement.lean:3020-3040` (`hist_replace`, `StepGhost.lean:1374`, with `HLf`) | the leader's full log at T, which disagrees with the old log at idx | **no**. In the stale case no `okL` log (`Ghost.lean:2830`) covers `P` at the old acks' indices |
| restore: new ack's `hist` and `ackIn` | `Refinement.lean:3041-3061` | as fastfwd | **no** |
| static `GMode.SnapOk`, `SnapScope` | `StepGhostMode.lean:502`, `SpecResults.lean:116` | ConfState lists, `Index < 2^61` | content (D22b) |

Other things checked:
- `RInv_snapRestore` and `RInv_snapFastfwd` (`StepRInv.lean:622-660`) use no message facts.
- The model's `Step.snap*` rules (`P/Protocol/Model.lean:1847-1890`, `StepC.lean:563-590`,
  `StepR.lean:291-330`) carry no message facts either.
- `SnapOk` (`Model.lean:1527`) is the sender's side and is unaffected.
- `Results.lean` only prints axioms; nothing protocol-level reads `.snap`.
- With (A), these consumers downstream would also break: `heartbeat_commit_le_last`
  (`P/Protocol/Facts.lean:66`, which bounds `Commit` through `acksOk`), the leader's
  `ownRaftGhost_ackIn_le` (`PrvalsOk`), and the `cq` and LC lemmas that read `hist`.

**Replacement arguments, where one exists.**
- **snapStale:** keep a `leadFull` of `T` in the envelope.
- **`isCommitted` and records:** take them from `P`.
- **With `commitIn γ P idx T` kept in the content** (i.e. (A) minus only the leader prefix):
  - `ackIn` follows by `commitIn_ackIn` (LC).
  - `TermsLe` follows: the commit fact's `cq` log has terms `≤ t ≤ T`, and `P` agrees with it.
  - "no ack above the snapshot" follows: by LC, the old leader's log reaching `i ≥ idx` agrees
    with the commit fact's log at `idx`.
  - `hist_replace` can be redone against the commit fact's log.

  So the leader-prefix part is replaceable. **`commitIn` at `m.term` is not**: it is exactly what
  the stale and Figure-8 merged messages lack, and an apply thread cannot mint it without raft's
  term. (A) drops the one fact that matters.

### (b) "Last log term <= term": the invariants

All of these are ports of `election_proof/protocol.v`. For each: what finding 2's case does to
it, and what would have to change.

1. **`TermsLe s (fp ++ s.log)`** (`GhostState.lean:492-495`, in `ownLogGhost` `"%Hfull"`
   `:2023-2024`): every term in the full log is `≤ s.term`, and `<` for a candidate. **Broken** by
   the stale restore (base `(T', idx)`, term `T < T'`).
   - Established by: the restore from `lpfull`'s term bound (`Refinement.lean:3000-3010`); the
     append from the leader's bound (`Refinement.lean:2211-2217`, `2591-2613`).
   - Consumed by:
     - the campaign (`StepGhost.lean:919-931`, `973-977`), which builds `CampOk`;
     - `Step.win` (`Refinement.lean:651-673`: the last term of the winner's log `< T`, for its
       first entry);
     - `boot_term_le` (`StepGhost.lean:824-836`, `862`).
2. **`CampOk T F`** (`Model.lean:1291`, in `isCampK`, `Ghost.lean:674-676`): every term of a
   campaign log is `< T`. **Broken** as soon as the stale receiver campaigns at `T+1 ≤ T'`, which
   Go allows (`campaign`, no check). It is the measure of LC's induction:
   - `lc_adj_gen`'s case "later last term `tc`" applies the IH at `tc` because `tc < T` (`HtcT`,
     `P/Protocol/LeaderCompleteness.lean:287`, `:323`);
   - also `camp_last`, `CampOk.term_nz` (`ReadIndex.lean:638`), `lc_far_newer`/`lc_far_older`.

   A redesign needs `CampOk ∨ doomed`: the campaign carries a commit fact of a term `> T`, and
   `Step.win` refutes a win. Its quorum meets the commit quorum at some `v`; `v`'s acknowledgement
   of term `t > T` existed before the campaign record (the restore's certificate carries its
   `ackEv` lower bound). `v`'s vote at `T` would then be appended after it, against `EvSorted`
   and `AcksTerm`. Dynamic configurations need the reconfiguration overlap argument on top.
3. **`lpfull`'s "no term above t"** (`Ghost.lean:2231-2235`) and **`leadFull_wf`** (`:2265`):
   true of every real leader in Go. Under the redesign they would have to be re-derived from (2).
   Unaffected by (D).
4. **`commitJ`'s `t ≤ tm`** (`Ghost.lean:2556-2562`), with `commitIn (fp++log) commit s.term`
   (`GhostState.lean:2019`), `witsB`'s bound `tm+1`, and **`campDyn`'s `tm < T`**
   (`GhostState.lean:157-159`, consumed by `lc_far_newer`, `LeaderCompleteness.lean:466-468`):
   the term of a node's commit justification is at most its term. **Broken** by both the stale
   and the Figure-8 merged snapshot.
5. **`ackOk`/`ackAgree`** (`GhostState.lean:439`, `Ghost.lean:2973`), **`ackIn`**
   (`Ghost.lean:1574`) and **`hist`/`okL`'s bound** (`Ghost.lean:2830-2846`): these are not term
   bounds as such, but they are what the stale restore breaks (above).
6. Not affected: `AcksTerm`, `VoteHistOk`, `vlogsOk`, `Hcamps_ok`
   (`GhostState.lean:337,434,534,2028`) bound recorded *events'* terms, not log terms. The
   physical invariants (`InvRawnode.lean:312-316` `PendingOk`, `InvRaftPhys.lean:298,319`) bound
   message terms. `Plog.lean:139` is `isUpToDate`. `StoredSnapOk` (`InvRaftlog.lean:416`) concerns
   the sender's own storage.

**Finding 2's argument, checked against raft `c8217eb9`.** Conclusion: **no safety bug, and no
reachable panic.** It holds, with these refinements:
- **Acceptance.** `Step` (`raft.go:1089-1130`) adopts `m.Term` with `lead = m.From` for a
  `MsgSnap`. `stepFollower`/`stepCandidate` then call `handleSnapshot` (`:1735-1738`).
  `restore` (`:1857-1945`) checks only `index > committed`, the follower state, and the id in the
  ConfState. It never compares `Metadata.Term` with `r.Term`. So the receiver holds `(T', idx)` at
  term `T`. **Confirmed.**
- **Cannot lead.** The receiver cannot lead at any term **≤ `T'`** (the doc says "before `T'`";
  it should say "at or before"):
  - below `T'`: the quorum that acknowledged at a term `≥ T'` drops votes of a lower term
    (`:1130-1180`, the `m.Term < r.Term` arm ignores `MsgVote`);
  - at `T'`: the leader of `T'` exists, and election safety forbids a second;
  - above `T'`: `CampOk` holds again.

  This assumes the committing quorum and the receiver's electing quorum intersect: static here,
  and under reconfiguration the usual I1 overlap.
- **Stale `MsgApp` of term T.** `m.Index < idx` takes the `prev.index < committed` exit
  (`:1793-1796`) and replies `MsgAppResp{Index: idx}`: an *acceptance* at `T`, ignored by the old
  leader, which is at a term `≥ T'`. At `m.Index = idx`, `LogTerm ≤ T < T'` mismatches. Above
  `idx` it is out of range. Both of these reject.
- **Stale heartbeat of term T** (`handleHeartbeat` → `commitTo`, `:1832`, which panics past
  `lastIndex`). It carries `Commit ≤` the old leader's committed index `c`. And `c < idx`: if
  `c ≥ idx`, that leader's committed entry at `idx` (term `≤ T`) would contradict `P`'s committed
  `(T', idx)`. So `commitTo` is a no-op. This is the argument the ghost would need:
  `isCommitted_agree` plus `lpfull`'s term bound. `heartbeat_commit_le_last`'s route through the
  acks no longer works.
- **Figure-8 variant.** Same conclusions: the replies at `T` go to a leader that has moved on, and
  heartbeat commits are below the first disagreement.

### (c) Stages S-b..S-d

- **S-b is underestimated under (A).** It is a protocol redesign ((A″): items 1, 2, 4, 5 of (b),
  LC's induction, a "leader of T has left T" disjunct on acks with a per-node term lower bound or
  the sender's later ack, and its refutation in the leader's `MaybeUpdate`/`cq` formation). Very
  large, not medium. It still needs a raft handout of the sender's term at the merge.

  **Under (D), S-b shrinks to:**
  - the clause unchanged;
  - a re-content lemma `isMessage_snap_recontent m k` that keeps `m`'s envelope and takes the
    content from a leader handout;
  - the handout: a spec of `node.Status` and `getStatus` (or an etcd-side record of raft's
    term/role per `Ready`). When leader at `T` it gives `leadPrefix`, `lpfull`, `commitIn` at its
    commit index, and `isCommitted (cprefix)`, plus `applied ≤ commit`;
  - a lemma lowering `commitIn` to a smaller index (`commitJ` by `full_match`, `witsB` monotone);
  - `prev.index ≤ appliedi` (compaction stays at or below the applied index), for
    `plogTermAt bL l appliedi`;
  - D22b's configuration certificate.

  One etcd fork commit (which S-h needs).
- **`raftSnapCert` (`P/SnapConf.lean:147`) predates D19p.** Its static part lacks the
  tracked-bound conjunct that `GMode.SnapOk` now has (`StepGhostMode.lean:502-505`). Add it in
  S-b.
- **`SnapScope`'s `Index < 2^61`** (`SpecResults.lean:123`, `SnapListsOk`) for a merged
  `appliedi` needs a cluster-level bound (D22h/`rnLogFits`). List it as a premise S-h must
  discharge.
- **`scfg.Has id`**, the `!found` exit of `restore` (`raft.go:1873-1904`): the clause gives
  `dst ∈ reTracked`, not `dst ∈` ConfState. Describe the exit as a new protocol rule (reply
  `MsgAppResp{Index: committed}` with `m.index > commit`; ghost as `ownRaftGhost_step_stale`,
  i.e. `commitIn_ackIn`) instead of a premise. Cheap; S-b or S-c.
- **S-c.** If (D) goes through `node.Status`, `node.run`'s status branch (`node__run.lean:917`,
  "never") becomes live: add it to S-c or S-b.
- **S-d.**
  - Cover **both** `MsgStorageAppendResp` snapshot arms: the equal-term one (`raft.go:1194-1201`)
    and the **lower-term** one (`:1170-1180`, `appliedSnap` "even if the snapshot applied under a
    different term"). `InvRawnode.lean:792` (`MsgStorageAppendResp → sn = none ∧ Term ≤ s.term`)
    must be relaxed for both.
  - **A second restore between `Ready` and `Advance`** is reachable: `node.run` steps `recvc`
    while waiting on `advancec`. The stage must allow a pending snapshot `s2` while the
    application holds `s1`'s handout and `stepsOnAdvance` carries `s1`'s response. Then
    `stableSnapTo(i1)` is a no-op, `appliedTo(i1)` is in range (`applied < i1 ≤ committed`,
    `log.go:332-345`), and `delivered`/`applying` jump twice. Not a Go bug.
  - `PendingOk`'s `appendAck` (`InvRawnode.lean:316`) is about `stored`, which a restore does not
    change, so it survives. `unstable.stableTo`'s miss exits are already specified.
## Part 2. S-0 (2)-(5): the etcd side of D22 checked against the code

Pins: etcd fork `8a24be2a3`, raft fork `c8217eb9`. Go paths are under `server/` unless they say otherwise.
Lean paths are under `Proof/go_etcd_io/etcd/server/v3/etcdserver/` (P) and
`Spec/go_etcd_io/etcd/server/v3/etcdserver/` (S). All of this is from reading the code; nothing was run.

### Summary

- **(2)** The sender's four facts hold in the runs covered (a fresh cluster, ci₀ = ai₀ = 0, a static
  configuration). The proofs state only one of them as is: that the applied prefix is committed.
  The other three are not in the invariants yet:
  - that `ep.appliedt` is the last applied entry's term;
  - what `ep.confState` contains (and Go's validation-failure path can leave it empty);
  - that `ciEff = ai`.

  `ep` is never written from another goroutine.
- **(3)** D22c (A)'s claim holds for the buckets restore reads, with seven exceptions. None of them
  applies to putget's workload, but D22c must say which buckets are a function of the log, and when.
- **(4)** Only the M3 cap uses `srvWTAt`. `srvWTPool` holds the *backend's* write-back tokens, so a
  backend swap breaks it however the applied index moves. The revision and change-count bounds do not
  go through `srvWTPool` at all: they use the index writer's receipts, which a restore breaks
  (D22h has to cover them).
- **(5)** A new Go bug, likely reachable (from code reading, not reproduced): an auth-enabled member
  can panic during `applySnapshot`, because `authStore` keeps the old, closed backend until
  `authStore.Recover`, which runs after `oldbe.Close()` has started. There are also two narrower
  crash windows of the same class (`store.hash`, the maintenance `Snapshot` RPC). The proof itself
  holds `s.be` as `↦□` (D19i part 2), which S-j has to undo.

### (2) What the sender knows at the `msgSnapC` receive

Go: `server.go:978-1009` (`applyAll`). `createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState)`
runs after `applyEntries`, `<-notifyc`, `<-raftAdvancedC` and `snapshotIfNeededAndCompactRaftLog`.
`snapshot_merge.go:36-53` does `KV().Commit()`, then `s.be.Snapshot()` (`backend.go:380-388`: another
`batchTx.Commit()`, then `db.Begin(false)`), and then overwrites `m.Snapshot` with
`(snapi, snapt, proto.Clone(confState))`.

#### (a) Is the applied prefix committed? Yes, already in the proofs.

- `applyAll`'s post (S `EtcdServer__applyAll.lean:70-78`) gives `kvApplied γr.raft γr.kv (A ++ unapplied ai ms) x'`.
- `kvAppliedL` (P `InvRequest.lean:1337`) contains `srvRLogLb γ A`, which is raft's `isCommitted` of
  `pre ++ A` (`:234`), and `x.log = kvModel γk A`.
- `applyRes` (P `InvRun.lean:244-256`) carries `uint.Z ai = ai₀ + A.length`, and `appliedLogAt γr ai x.log`.
- So D22a (A)'s `snapContent_mint` has the committed prefix of length `ai` and its KV model at the receive.

#### (b) Is `ep.appliedt` the last applied entry's term? True in Go, not kept in the proofs.

- Go: `apply` (`server.go:1944`) sets `appliedi, appliedt = e.GetIndex(), e.GetTerm()`.
  `applyEntries` (`:1211`) assigns both only for a non-empty batch.
- `apply`'s post gives `(ms.getLast?).map term = some appliedt` (P `EtcdServer__apply.lean:213-220`).
- `applyAll`'s post and `applyRes` existentially quantify `at'` and drop that fact.
- **Amend:** add `at' = lastTerm (pre ++ A)` to `applyRes` and to `applyAll`'s post (term 0 at `A = []`
  on a fresh start, `at₀ = 0`).

#### (c) Is `ep.confState` the static configuration? True in Go when `ai ≥ 1` and validation succeeds; the proofs know nothing about it.

- **At start:** `run` reads it from `raftStorage.Snapshot()` (`server.go:802-811`). On a fresh member that
  is `NewMemoryStorage`'s `EnsureSnapshot` (raft `storage.go:124`): an *empty*, non-nil ConfState with
  no voters.
- **Updates:** only `applyConfChange` writes it, `ep.confState = s.r.ApplyConfChange(cc)` (`:2033`),
  and only when validation succeeds and `shouldApplyV3`.
  - On a validation failure (`:2015-2027`) it is left unchanged.
  - The server's policy admits only `AddNode`s of existing voters (`ccApplyOk`, P `InvRequest.lean:276`),
    so a successful update is raft's static configuration: `node.ApplyConfChange`'s `confstateP` gives
    `confstateS γ c` in static mode (raft `P/InvNode.lean:711-716`).
- **When a `MsgSnap` can be pending:** raft panics on an empty snapshot (`maybeSendSnapshot`), and the
  storage snapshot comes from `CreateSnapshot(ep.appliedi ≥ 1)`. So whenever a `MsgSnap` is pending,
  `ai ≥ 1` and the first boot entry has been applied.
- **What the proof has:** only `epCsOk` (P `InvApplier.lean:371`): `nil` or some read-only ConfState.
  `applyConfChange.spec` (S `:76-77`) returns an arbitrary `cs'`.
- **The gap:** `ValidateConfigurationChange` reads the backend's `members` bucket
  (`membership/cluster.go:306-391`), which is not modeled (`ccContextOf` is opaque). So the proof
  cannot exclude "every boot entry failed validation", which leaves `ep.confState` empty.
- **Amend (pick one):**
  - (i) Strengthen `epConfState` to `content ∈ {empty, cfg}`, and let the merged message carry either
    one. The receiving raft then needs `restore`'s `!found` exit (today the premise `scfg.Has id`,
    inventory) and `isSnapMeta` has to admit it. Cheaper.
  - (ii) Model `members` enough to prove the boot entries pass validation.
- **No mutation elsewhere:** `ep.confState`'s object is never mutated (`DFrac.discard`; raft's answer is
  a fresh object), and the merged message clones it (`snapshot_merge.go:48`).

#### (d) Is the db's consistent index `= ep.appliedi` after `KV().Commit()`? True in the runs, but the invariant only has `≤`.

- **Go:** only the apply thread moves the in-memory ci, through these writers:
  - the post-lock hook: `getTxPostLockInsideApplyHook`, `server.go:2461`, which sets ci from
    `ConsistentApplyingIndex`;
  - the deferred `SetConsistentIndex` in `applyEntryNormal` (`:1952-1960`), which covers the no-data
    and skip cases;
  - the validation-failure branch (`:2022-2025`);
  - `SetBackend`, which resets ci to 0 (`cindex.go:124-129`).
- **At the receive:** every entry `≤ ai` is fully processed, so in-memory `ci = max(ci₀, ai) = ai` in
  fresh runs. `store.Commit` (`mvcc/kvstore.go:286-290`, under `s.mu`) leads to `ForceCommit`, then
  `OnPreCommitUnsafe` (`storage/hooks.go:45-54`), then `UnsafeSave`, which stores (ci, ci's term).
- **No later entry can leak in:** commits by other goroutines between `Commit()` and `Snapshot()`'s
  `Begin` save the same ci, because no entry is in flight. Only non-apply writes can enter the image
  (the storage version, (3)). No window exists in which an applied entry is in the image but its ci is
  not, or the reverse: the hook sets ci inside the same batch-lock critical section as the writes,
  which is the protocol's `eff ≤ meta ≤ p`.
- **The term is right:** the stored term is ci's entry's term (`SetConsistentApplyingIndex(e.Index, e.Term)`,
  `:1916`).
- **Proof gap 1:** `applyRes` keeps only `ciJ (ciEff …) c₀ ai` (P `InvRun.lean:52`), which says
  `ciEff = c₀` or `ciEff ≤ ai`. `apply`'s post has `ciEff' = max(ciEff, appliedi)`, but `applyAll`'s
  post keeps a disjunction (S `:77-78`).
  **Amend:** carry `uint.Z (ciEff) = max c₀ ai` in `applyRes` (true at start, `ai₀ = c₀ = 0`, and kept
  by every batch).
- **Proof gap 2:** the consistent-index ghost state tracks the index only (`ciIdx`, P `InvCindex.lean:119`).
  The stored term (`metaAfterSave`, `:88`) is not related to raft's log. Nothing in the restore path
  reads the term (`SetBackend` reloads the index; the term is read at bootstrap/verify only).
  **Amend:** `dbImage`'s meta clause needs only the index, so drop "and its term" from D22c (A).
- **The image is at `ai` exactly:** no entry `> ai` has run. The one asynchronous writer driven by an
  applied entry is the mvcc compaction job (`kvstore_compaction.go:69-95`), and compaction is off in
  the runs (`dispatchOk`, `backendNoCompaction`).
- **`ep` is not shared:** it is a local of `run` (`server.go:802`), passed by pointer to `applyAll`
  jobs, which the FIFO scheduler runs one at a time. No goroutine reads or writes it; the merged
  message gets the values. This fork's `processMessages` (`raft.go:358-400`) puts the same
  `*Message` in `msgSnapC` and leaves it out of the transport batch, so there is no shared mutation of `m`.

### (3) Which entries write the buckets restore reads (D22c (A)'s determinism claim)

**The writers, all on the apply thread:**

| bucket / key | writers | how | determinism |
|---|---|---|---|
| `meta/consistent_index`, `term` | `cindex.UnsafeSave` from every commit's `OnPreCommitUnsafe` (`hooks.go:46`) | in-memory ci at commit, below | function of entries ≤ i (fresh runs) |
| `meta/confState` | `MustUnsafeSaveConfStateToBackend` on the next commit after `SetConfState` (`hooks.go:49-53`, `server.go:2035`) | exc. 1 | see exc. 1 |
| `meta/scheduledCompactRev` | `updateCompactRev` (`kvstore.go:191-203`; apply `Compaction`) | | function of entries |
| `meta/finishedCompactRev` (and the key-bucket deletions) | the async compaction job (`kvstore_compaction.go:69-95`), and its resumption by `restore` | exc. 2 | timing |
| `meta/storageVersion` | `UpdateStorageVersion` → `UnsafeMigrate` (`adapters.go:76-85`, `schema/migration.go:101`) from `monitorStorageVersion` (`server.go:2239-2252`) | exc. 3 | not entry-driven |
| `key` | `mvcc` txns from `apply.Apply` (Put/DeleteRange/Txn), lease revoke's `rd` (`lessor.go:326-359`) | | function of entries |
| `lease` | `Grant`/`Revoke`/`Checkpoint` (`apply/backend.go:84,95,101`; `lessor.go:281-382`, `lease.go:55-61`) | exc. 4, 5 | config-dependent |
| `auth*` | `authStore` methods from `applierV3`'s auth requests; `commitRevision` (`auth/store.go:999-1002`) | exc. 6 | mostly |
| `members`/`members_removed` | `AddMember`/`RemoveMember`/`PromoteMember`/`UpdateRaftAttributes` (`applyConfChange`, `server.go:2048-2079`), `UpdateAttributes` (`ClusterMemberAttrSet`, `apply/backend.go:288`) | exc. 7 | function of entries in the runs |
| `cluster` (`clusterVersion`, `downgrade`) | `SetVersion` (`ClusterVersionSet`, `apply/backend.go:273`, `cluster.go:589-623`), `SetDowngradeInfo` (`DowngradeInfoSet`, `:303`, `cluster.go:811-818`) | | function of entries |
| `alarm` | `AlarmStore.Activate`/`Deactivate` (`Alarm` request, `apply/backend.go:119,126`) | | function of entries |

**The other writers, checked:**
- The NOSPACE and CORRUPT alarms, lease expiry (`revokeExpiredLeases` → `expiredC` → `LeaseRevoke` proposal),
  lease checkpoints (`checkpointScheduledLeases` → `le.cp`, a proposal), the cluster version
  (`monitorClusterVersions` → proposal) and the compactor all go **through raft**: no direct writes.
- `lessor.Promote`/`Demote` write nothing.
- The quota applier applies regardless and only changes the error (`apply/quota.go:36-61`), so the KV
  is deterministic.

**The bootstrap state (same on every fresh member):**
- every bucket is created: `CreateMetaBucket` (`bootstrap.go:266`), `NewStore` (`kvstore.go:122-125`),
  lease (`lessor.go:812`), `CreateAuthBuckets` (`auth/store.go:960`), `MustCreateBackendBuckets`
  (`cluster.go:249`), `CreateAlarmBucket`;
- **`authRevision := 1`** is written by `NewAuthStore` at startup (`auth/store.go:982-984`): a
  non-entry write, but the same on every member, so it belongs to the initial state.

The `SetBackend`/`Recover` steps on the receiver write only buckets (idempotent) and ForceCommits.
`lessor.Recover` commits with ci = 0 (skipped, `cindex.go:116-120` → `schema/cindex.go:69`), as the
comment at `server.go:1062-1066` intends.

**Exceptions** (the bucket at consistent index i is not a function of entries ≤ i, plus the boot state):
1. **`meta/confState` lags or leads ci.**
   - It leads: `SetConfState` (`server.go:2035`) runs before the entry's hook (`AddMember`'s
     `LockInsideApply`), so a periodic commit in between saves ci = i-1 with entry i's confState.
   - It goes stale on the receiver: a dirty confState can be written onto `newbe` by `lessor.Recover`'s
     `ForceCommit` (`lessor.go:834`); since `beHooks` is shared, it is the receiver's own, staler
     confState, not the image's.
   - Nothing in the server reads it (`UnsafeConfStateFromBackend` has no non-test caller at the pin).
     **D22c: leave it out of `dbImage`.**
2. **The compaction keys and the key bucket's physical content** depend on the async compaction job's
   progress. `store.restore` resumes an unfinished job (`scheduled > finished`), so the logical view is
   determined, the physical one is not. Excluded in the runs; S-g has to state it.
3. **`meta/storageVersion`** is written locally and periodically (and on cluster-version change) by each
   member's monitor. It is a function of the cluster version, the WAL's minimal version and timing,
   not of ci. Restore never reads it; only the monitor and the maintenance RPCs do. **`bkRestAt` must
   leave it free (or "any version").**
4. **The lease bucket's `TTL`** is clamped to the member-local `minLeaseTTL`
   (`lessor.go:301-303`, from `ElectionTicks`·`TickMs`, `server.go:344-349`).
5. **The lease bucket's `RemainingTTL`** is persisted only if `checkpointPersist` (a member-local flag)
   or the cluster version is ≥ 3.6 (`lessor.go:372-374,385-388`).
6. **`auth`'s `users`:** a legacy entry with a plaintext `Password` is hashed *at apply* with a random
   bcrypt salt and the member-local cost (`auth/store.go:412-419`), so every member stores a different
   hash. (`v3_server` hashes before proposing for new requests.)
7. **`UpdateAttributes`** writes only if the member is in the *in-memory* `c.members`
   (`cluster.go:467-496`). On a fresh member that holds the initial config before the boot entries
   apply; on a joining member it is whatever was bootstrapped. Deterministic in fresh static runs
   (the boot `AddNode`s are entries 1..n, before any publish).

**Amend D22c (A):**
- `bkRestAt i` should be stated per bucket: `lease`, `auth*`, `members*`, `cluster`, `alarm` are a
  function of (the boot state, entries ≤ i, and each member's configuration).
- The configuration enters only through exceptions 4-6. Add the premise "the members agree on
  `ElectionTicks`/`TickMs`/`checkpointPersist`" to the axiom, or restrict it to workloads without
  leases or auth (putget's `noGrant`, auth off). Then the lease and auth buckets are the boot state,
  which is what `bkFresh` says today.
- `meta` minus (ci, compaction keys) is free.

### (4) The users of `srvWTPool`/`srvWTAt`

**Where they occur** (definitions in P `InvApplier.lean:647-761`: `srvWTPool`, `srvWTAt`, `_alloc`, `_take`, `_take_at`, `_bound`):

| place | uses | bounds |
|---|---|---|
| P `EtcdServer__start.lean:419` | `srvWTPool_alloc` from the `N` tokens `bootstrap` gives (`receiptBound ≤ N+1`), the counter at `0 = ai₀` | creates both |
| P `EtcdServer__start.lean:496`; S `EtcdServer__monitorStorageVersion.lean:36`; P `InvStorageVersion.lean:25-29` | the pool (no counter) for the monitor's `Unlock`s, through `srvWTPool_take` | the backend's write-back budget |
| P `InvRun.lean:235,252,383`; P `EtcdServer__run.lean:65` | `ApplyCtx.wt`; `applyRes`'s `srvWTAt C.wt ai`; `isServerRun`'s `HWB` | the loop invariant carries the counter |
| S `EtcdServer__applyAll.lean:64,73`, S `EtcdServer__applyEntries.lean:59,67`, S `EtcdServer__apply.lean:62-63,72` | pass the pool, `srvWTAt` in and out | the counter |
| P `EtcdServer__apply.lean:205,212,333-341` | `srvWTPool_take_at` per entry, with the receipt of the `zap.Uint64` step | (i) the entry's `mvcc.storeWT E.γ` = `backend.wbTok` (P `storage/mvcc/BackendBridge.lean:1777`): one per batch-tx `Unlock`, so that the read buffer's `uint64` version does not wrap (P `storage/backend/InvBackend.lean:23-24`); (ii) the counter advanced |
| P `EtcdServer__snapshotIfNeededAndCompactRaftLog.lean:44`, S `:29-38` | `srvWTPool_bound`: `ai < receiptBound ≤ scu + 1` | M3's raft-storage cap (`compactRaftLog`'s `… ≤ γs.cap = 1`) |
| S `NewServer.lean:137`, S `EtcdServer__Start.lean:38`, S `EtcdServer__start.lean:29-47` | comments, and the pool in the post | |

**What does not use them:**
- **Revision overflow:** the store's revision tokens (`txn/SoleWriter.lean:58,93`, `2^63 - 3 - |log|`).
- **The "fewer than 2^48 changes" bound** (`srvApplyKV_small`, `entryOk_of_shape`, `storeSmall_of_receipts`):
  the **index writer's** receipts, `⧗ (logCh ilog + pend.length)` in `idxWriter`/`idxWriterSealed`,
  giving `idxSealed`'s `logCh log < receiptBound` (P `storage/mvcc/InvIndex.lean:970-1001`), together
  with `receiptBound ≤ 2^48`.
- **The id generator:** its own receipts.
- **raft's indices:** `rnLogFits` (pure, P `InvRaftNode.lean:262`).

**After a jump `ep.appliedi := snapi`:**
- **`srvWTAt γp snapi` cannot be had:** `snapi` is above the tokens taken. Its only consumer is
  `srvWTPool_bound` → M3's cap, which S-l removes (`γs.cap = 2^64`). D22h (A) for it: **drop
  `srvWTAt` and the counter** (back to the pre-M3 pool) once the cap goes. Nothing else needs the
  applied index below `receiptBound`. `take_at`'s `v + 1 < 2^64` comes from `entriesFrom`, which is unaffected.
- **`srvWTPool` survives the jump, not the swap:** its invariant does not mention `ai`, but it holds
  `storeWTs E.γ n`, the *old* backend's `wb` tokens. The new backend comes with a fresh
  `ownToks γ.wb wbInit` (P `storage/backend/InvNew.lean:66`). After the swap:
  - a new pool must be allocated over the new backend's tokens (`srvWTPool_alloc` needs
    `receiptBound ≤ wbInit - k + 1`, as at boot);
  - the monitor, which shares the pool, must switch with it.

  So **`E.γ` (the store names, with `kb`) and `isServer`'s fixed `E`/`applyBackend γ ci b`
  (S `EtcdServer__applyAll.lean:55-63`) must become per-backend-epoch.** This is not in the stages today.
- **The index writer's receipts break:** the restored treeIndex's log is the image's (other members'
  changes), and this member holds no `⧗ (logCh …)` for it. So `idxSealed_small` and `soleWriter`'s
  `logCh < 2^48`, both used by every apply after the restore, need a cluster-level source. The number
  of committed entries does not bound the changes (a txn has up to `putMax ≥ 2^56`).
  **Amend D22h (A):** keep `⧗ (logCh (kvModel A))` once for the cluster, in `kvCertInv`/`kvInv`, paid by
  the first member to apply each change, or by the proposer per op. Then a restore takes from there
  `logCh (kvModel A') < receiptBound ≤ 2^48` for the image's log, and re-makes the index's and the
  store's token authorities from it (revs: `|log| + ntok + 3 ≤ 2^63`).
- **Survive unchanged:** `rnLogFits`; the id generator; raft's own bounds; and `entriesFrom`'s
  `f0 + |ms| < 2^64`.

### (5) Who holds a backend across `applySnapshot`'s swap

The order in `applySnapshot` (`server.go:1011-1159`):
- `bemu.Lock` (`:1048`);
- `OpenSnapshotBackend` (`:1056`; hooks are set only after the initial empty commit, `backend.go:273-277`,
  so nothing is written to `newbe` before `SetBackend`);
- `consistIndex.SetBackend` (`:1067`);
- `lessor.Recover` (`:1077`);
- `kv.Restore` (`:1084`, under `store.mu`; it stops the old FIFO, which waits for a running compaction);
- the hook (`:1088`);
- the log line that reloads ci from `newbe` (`:1090`);
- the swap and `bemu.Unlock` (`:1092-1095`);
- **`go oldbe.Close()`** (`:1100-1108`);
- `restoreAlarms` (`:1112`, `ForceCommit` with an fsync on `newbe`, `alarms.go:112`);
- **`authStore.Recover`** (`:1121`);
- `cluster.SetBackend` and `Recover` (`:1126-1130`);
- `NewUberApplier` (`:1158`).

`oldbe.Close()` (`backend.go:481-487`) runs `CommitAndStop`, which resets `readTx` (`tx = nil`,
`read_tx.go:133-137`), then closes bolt. Any later use of the old backend crashes:
- a `ReadTx` range misses the empty buffer and calls `nil.Bucket()` (`read_tx.go:103`), a nil-pointer panic;
- a `Commit` either does an `UnsafePut` on the committed tx (when ci ≠ 0, a panic in bbolt) or calls
  `begin` on the closed DB, which is `lg.Fatal` (`backend.go:1101-1107`).

| holder | updated in `applySnapshot`? | a stale one is a bug? |
|---|---|---|
| `consistIndex.be` | yes, before the swap (`:1067`) | no; the old backend's final commit writes the current ci into the unlinked old file, harmless |
| `s.lessor` (`le.b`) | yes, before (`:1077`, under `le.mu`); its other users are on the apply thread | no |
| `s.kv` (`store.b`) | yes, before (`:1084`, `kvstore.go:292-314`, under `s.mu`; reads hold `s.mu.RLock`) | no, except `store.hash()` (below) |
| `watchableStore` | uses `s.store.b` under `ws.mu`, which `Restore` holds | no |
| hash KV / `corruptionChecker` (`srv.kv.HashStorage()`, `server.go:371`) | same store object, in place | `HashByRev` holds `s.mu` while taking the read tx and `tx.RLock` while using it: no. **`store.hash()` (`kvstore.go:156-163`) reads `s.b` twice without `s.mu`**: below |
| v3rpc quota (`quota.go:93-95`) | no | finding 1 (filed) |
| v3rpc maintenance `Snapshot` (`maintenance.go:140-146`), `Status` (`:280-281`) | uses `s.Backend()` per call, but keeps the result after `bemu.RUnlock` | `Status`: no (atomic sizes, stale); `Snapshot`: a crash window, below |
| `Defragment` (`server.go:965-976`), `StorageVersion` (`:2202-2213`), `UpdateStorageVersion` (`adapters.go:76-85`), compaction `ForceCommit` (`v3_server.go:410-413`) | hold `bemu.RLock` across the use | no |
| `monitorKVHash` `VerifyBackendConsistency(s.be, …)` (`server.go:2275`) | reads `s.be` without `bemu` | a data race; does something only under `ETCD_VERIFY`, so test-only |
| `applyAll`'s `VerifyBackendConsistency(s.Backend())` (`:981`), `createMergedSnapshotMessage`'s `s.be` (`snapshot_merge.go:37`), `restoreAlarms`, `NewUberApplier` | run on the apply thread, the only writer of `s.be` | no |
| `s.alarmStore` | replaced (`:1112`) by a store on `newbe`; the old one is only read in memory by `s.Alarms()` until then | no (a briefly stale alarm list) |
| `NewUberApplier`'s appliers (`options.Backend` → the apply-level quota, `AlarmStore`, `AuthStore`, `Lessor`, `Cluster`) | rebuilt at `:1158`; unused in between (the apply thread is here) | no |
| `s.cluster` (`c.be`) | yes, after the swap (`:1126`); `c.be` is used only on the apply thread (`ValidateConfigurationChange`, the writers, `UnsafeLoad`) | no |
| **`s.authStore` (`as.be`)** | **yes, but after the swap and after `go oldbe.Close()` (`:1121`)** | **yes: new bug, below** |
| `compactor` | holds `s.kv`/`s` (no backend); off in the runs | no |
| `beHooks` | shared by both backends | exception 1 of (3) only |

**New bug (not filed; from code reading, not reproduced): an auth-enabled member panics on a
permission check during `applySnapshot`.**
- **Where:** `authStore.isOpPermitted` (`auth/store.go:859-899`), `IsAdminPermitted` (`:913-933`),
  `CheckPassword` (`:364-393`) and `Authenticate` (`:333-338`) read `as.be` with no lock and run on
  gRPC goroutines. For example, `s.Range` → `doSerialize` → `IsRangePermitted`.
- **The window:** from `bemu.Unlock()` (`server.go:1094`) to `authStore.Recover` (`:1121`; which itself
  writes `as.be` without a lock, `:397`), `as.be` is still the old backend. The goroutine at `:1100`
  closes that backend concurrently, and the apply thread meanwhile runs `restoreAlarms`, whose
  `ForceCommit` fsyncs `newbe`.
- **The interleaving:** the old backend's close (one commit and fsync, then `db.Close`) can finish first.
  A permission check after that does `as.be.ReadTx()`, `RLock`, then `UnsafeGetUser` →
  `UnsafeRange(AuthUsers)`. The read buffer is reset, so it misses, and `baseReadTx.tx.Bucket(…)`
  (`read_tx.go:103`) is called with `tx == nil`. The result is a nil-pointer panic in a gRPC handler,
  which etcd does not recover, so the process dies.
- **Scenario:** auth enabled; a lagging follower installs a leader snapshot; a client sends any Range
  (or `Authenticate`, or an admin RPC) to that follower within those milliseconds.
- **Fix:** `authStore.Recover` before the swap (or before `go oldbe.Close()`), and `as.be` under a lock.
- **Check upstream** before filing: a quick search found nothing; upstream `main`'s `applySnapshot` has,
  as far as I recall, the same order.

**The same class, narrower windows** (each needs the goroutine to be descheduled for the whole restore
right after loading the backend pointer):
- **`store.hash()`** (maintenance `Hash` RPC, `maintenance.go:232-233`): load `s.b`, then
  `kv.Restore` + swap + close, then `ForceCommit` on the closed old backend: Fatal or panic. If the
  `t.lock()` is blocked behind `CommitAndStop`, it proceeds right after and crashes.
- **Maintenance `Snapshot`**: `ms.bg.Backend()` returns the old backend, then the close completes, then
  `ReadStorageVersion` (panic) or `Snapshot()` (`Commit`/`Begin`: Fatal).

### Proposed amendments to the stages

- **S-f:**
  - `dbImage γ i D`: the key view = `kvModel` of the committed prefix, the meta *index* = i, and the
    compaction keys. No meta term, no confState, `storageVersion` free.
  - `bkRestAt i` per bucket, with the premise "configuration agreed (exceptions 4-6), or no leases and
    no auth". Under putget it is exactly the boot state (`bkFresh`'s content).
  - Name the boot write `authRevision = 1` (`NewAuthStore`) in the boot state.
- **S-g:**
  - restore resumes an unfinished compaction (exception 2); state it, or keep it excluded.
  - Re-make the index's and the store's token authorities for the image's log, from D22h's
    cluster-level change receipts (not from this member's `idxWriter` receipts).
- **S-h:** before the merged content can be minted, three things must be added:
  - `applyRes` and `applyAll`'s post: `at' = lastTerm`, `uint.Z ciEff = max c₀ ai`, and `epConfState`
    content `∈ {empty, cfg}`;
  - `applyConfChange.spec`'s post: `cs'` = node's `confstateS` on success, unchanged on a validation failure;
  - `store.Commit`'s contract: it saves ci (the protocol's `commit_save_au`).

  Then mint with ConfState "empty or cfg" (D22c (i)), or model `members` enough to prove validation succeeds.
- **S-b/S-d:** raft's receiver needs `restore`'s `!found` exit described (an empty or foreign ConfState
  is ignored) if S-h takes (i).
- **S-j:**
  - **`s.be` is `↦□` today** (P `NewServer.lean:863-866`, P `InvStorageVersion.lean:16-18,70`: D19i
    part 2), so the swap is unprovable as the plan stands. Return it to "half in `bemuP`, half the
    apply thread's" (the apply thread is the sole writer and reads it without `bemu`:
    `createMergedSnapshotMessage`, `restoreAlarms`, `NewUberApplier`).
  - Restate `srvSVRes` and the `monitorStorageVersion` contract over the backend current under `bemu`
    (Go holds `bemu.RLock`), with a per-backend write budget.
  - Make `E` / `applyBackend γ ci b` / `srvWTPool E.γ` per backend epoch (a ghost variable for the
    current backend's names).
  - The `authStore.Recover` window: either fix it in the fork (move `Recover` before the swap) or state
    the auth contract only with auth off (it is off in the runs).
- **S-k:** add the auth-store bug next to finding 1 (same class; the D22g (A)/(B) choice applies the same
  way). Note `store.hash` and maintenance `Snapshot` as names-only/unverified paths with a crash window.
- **S-l / D22h:**
  - drop `srvWTAt` and the counter when the cap goes (its only use);
  - re-allocate `srvWTPool` per backend;
  - replace the index writer's per-member change receipts by a cluster-level one (above). That last
    piece is the substance of D22h, not `rnLogFits`.
