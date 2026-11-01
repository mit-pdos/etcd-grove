# Review of the unified node-API candidate 7, round 7

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-7.md`, one text. It is a design,
  not yet implemented, so no finding can be stale against `HEAD` (`9ad6f9a3de`).
- **Compared with**:
  - today's API at `eb59bb8d1b`: `interface/Proof/go_etcd_io/raft/v3/{InvNode,ApiVocab}.txt` and
    `interface/Spec/go_etcd_io/raft/v3/{node__Advance,node__ApplyConfChange,node__ProposeConfChange,node__Tick,MemoryStorage__CreateSnapshot}.txt`;
  - the protocol at `HEAD`: `Protocol/StepR.lean`, `Protocol/Ghost.lean` (`SnapListsOk`), `CCModel.lean`,
    `Spec/google_golang_org/protobuf/proto/MarshalConfChangeV2.lean`;
  - the clients at `eb59bb8d1b`: the server's `InvNet.lean`, `InvBuild.lean` and `NewServerAlloc*.lean`;
    kv's `Defs.lean`.
- **Go**:
  - raft a2, `.lake/raft-fork` `565c2bd`: `node.go`, `raft.go`, `storage.go`;
  - kvreconf at `HEAD`: `examples/kvreconf/{kv,cluster,reconf}.go`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md` (the worktree has no `spec/` skill).
- **Not run**: lake build, lean-check, Go tests.

Each finding is classified as either:
- **[spec]**: a defect of the specification itself, which the candidate must change; or
- **[obligation]**: a proof obligation. Each says whether the candidate's §0 or `notes/raft-unified-plan.md`
  (at `HEAD`, unchanged in the worktree) carries it.

## Summary

Candidate 7 fixes E1, E3 (in §0), E4, E5, E7, E9, E10, E12, E13 and E14 of review 6. Two of review 6's fixes
moved the defect instead of removing it:
- **E2 → F1**: the length bound left `readyFits` for an unconditional `isCommittedLogLb_length` at `2^61`. That law
  is false in a cluster without a bootstrap log.
- **E8 → F3**: `storAppended` is now defined, but as a persistent fact about storage state that changes. It cannot
  carry the snapshot index bound, nor the term at `i`, that `CreateSnapshot` needs.

Two new false or unusable statements:
- **E11 → F2**: `clamp_eq` is false as written.
- **E6 → F4**: the E6 fix does not keep the axiom out of kvreconf. `ConfRule.validated` still needs `ccDecodeV2 []`.

One scope restriction is not filed:
- **F5**: newcomers must start at `c0`, which needs a Go change. It departs from how etcd starts a joiner, and is
  filed nowhere.

**Tier 1 (3)**: F1, F2, F3.
**Tier 2 (3)**: F4, F5, F6.
**Tier 3 (8)**: F7-F14.
**Go defects**: none new. Nothing to file in `issues/`. The one panic I re-checked is already filed:
`CreateSnapshot` below the storage's first index panics (`storage.go:250-257`, `ms.ents[i-offset]` with
`i < offset`). It is reachable only if the log is compacted past the snapshot, which is
`issues/raft-compact-past-snapshot.md`.

---

## Review 6's findings: fixed?

| review 6 | candidate 7 | status |
|---|---|---|
| E1 certificate at every term | `snapshotCert_make` at `(t, i)`, with `t` the last term of committed `l`, `l.length = i` | **Fixed** (forces `i > 0`; `snapshotCert_made` returns the term). Its `CreateSnapshot` half rests on `storAppended`: F3 |
| E2 `readyFits` unbounded | `readyFits` only when `boot ≠ []` | **Fixed there, moved elsewhere**: `isCommittedLogLb_length` now claims `2^61` for every cluster (F1) |
| E3 U6m | §0: `CCDecision`, `StepR.reject`, `applyConf` "no undecided conf entry between" | **Carried by §0; not by the plan.** The plan's U6 still reads "`nodeConfig_reject`, `nodeConfig_skip`; …". It does two things where one would do (F12) |
| E4 pre-vote premise | dropped from `stepIn_intro`; §0 U4 carries "granted at term 0" | **Fixed.** `bootedCluster` is kept with no consumer left (F9). Plan U4 does not name the obligation |
| E5 `MsgTransferLeader`'s `From ≠ To` | exempted; "no term or the sender's" | **Fixed** (sound, slightly weaker than needed: on the wire it always has the sender's term, `raft.go:542-544`) |
| E6 empty bytes | axiom `ccDecodeV2_nil` proposed for approval; kvreconf Go change | **Axiom right. The Go change does not do what it claims** (F4) |
| E7 credits | none in any client-facing spec; `Tick` is `isNode → unit` | **Fixed.** Provable in principle: each method call is a Go instruction step and issues a receipt (Perennial `PERENNIAL_PROOF_REFERENCE.md`, "Time receipts"). That the receipt reaches `run` is U7's, as §0 says |
| E8 `storAppended` | defined | **Defined unsoundly** (F3) |
| E9 one text | one text | **Fixed** |
| E10 `opsOf γ.rule γ.c0` | yes | **Fixed in the candidate.** The plan's "The spec" still says "persistent proposal updates", "the automatic leave a filler", and `msgCredits_readIndex/_prop` (U7) |
| E11 `clamp_eq` | `r.Ok → clamp r = r` | **False** (F2) |
| E12 `RaftLeave` invariant | §0 U5 | **Carried by §0**, not by the plan |
| E13 one `msgCredits` law | `msgCredits_intro` | **Fixed** |
| E14 `al` | `m.autoLeave` | **Fixed** |
| E15 stopped specs | a second spec file per method, `<M>.stoppedSpec`, checked by `--layout` | **A convention change** (F13) |

---

## Findings, ranked

### Tier 1

#### F1. [spec] `isCommittedLogLb_length` at `2^61` with no premise is false when `boot = []`

**Principle**: *Sound*.

**Evidence**
- An entry's index is below `receiptBound GF + γ.reBoot.length` (`Protocol/GhostState.lean:947, 957`;
  `LeaderCompleteness.lean:892`). Nothing else bounds the committed log.
- `cluster_alloc`'s `boot = []` branch assumes only `receiptBound GF ≤ 2^64 - 2`. So a committed log may be
  about `2^64` entries long, and `↑l.length + 1 < 2^61` cannot be proved.
- Today's law is `readyFits ∗ isCommittedLogLb ⊢ < 2^64` (`InvNode.txt`).
- The candidate (§2) says that "a cluster without a bootstrap log gets the length bound from
  `isCommittedLogLb_length`". It cannot.

**Callers**
- kv (`boot = []`) today takes `2^61` from its storage floor (`kvStorFloor`, `kv/Defs.lean:166-171`), and its
  `receiptBound` is `≤ 2^63` (`kv/Main.lean:10`). It does not need the law, and could not meet a `2^61` premise
  without weakening its adequacy.
- kvreconf and the server (`boot ≠ []`) have `readyFits`.

**Restatement**: `isCommittedLogLb_length : readyFits γ N ∗ isCommittedLogLb γ l ⊢ ⌜↑l.length + 1 < 2^61⌝`.
Optionally, also give `isCluster ∗ isCommittedLogLb ⊢ < 2^64` for every cluster. Drop the §2 sentence.

#### F2. [spec] `ConfRule.clamp_eq : r.Ok → clamp r = r` is false

**Principle**: *Sound*.

**Evidence**
- `ConfRule.Ok` constrains `r` only at valid memberships: `∀ pre m e o, m.Valid → r pre m e = some o → …`.
- `clamp r` filters at every `m`. At an invalid `m` where `r` gives `some o` with `applyChange o m = none`,
  `clamp r pre m e = none ≠ r pre m e`.
- So the two functions differ.

**Caller**: etcd's server and kv, to discharge `ApplyConfChange`'s `γ.rule … = some o'` (review 6's E11).

**Restatement**: state it pointwise:
`r.Ok → m.Valid → ConfRule.clamp r pre m e = r pre m e`.
The callers get `m.Valid` from `committed_fold`/`nodeConfig_fold`. Alternatively, drop `m.Valid` from `Ok`. That is
stronger, but `validated` would not obviously satisfy it.

#### F3. [spec] `storAppended` as a persistent fact cannot hold, and cannot give `si < i` (E8 not fixed)

**Principles**: *Sound*; *read the definitions of the resources a spec takes*; *every premise has a source*.

**Evidence**: `storAppended st i t si` is declared "persistent until compaction". An Iris persistent proposition
holds forever. Each of its three claims changes after it is made.

1. **The term at `i`.** It comes from `appendReceipt` of any appended entry, but a later `Append` overwrites an
   uncommitted suffix (`storage.go`, `Append`: `ms.ents = append(ms.ents[:offset:offset], entries...)`). After
   that, the storage's term at `i` is no longer `t`.
2. **"The storage holds the log up to `i`".** `ApplySnapshot` empties the storage (`ms.ents = [dummy at j]`).
   That is not a compaction, and it happens in kvreconf (`kv.go:322`).
3. **"Its snapshot at index `si`".** The snapshot index grows with every `CreateSnapshot` and `ApplySnapshot`. A
   fact fixed in the past can give only a lower bound on it. `CreateSnapshot` needs the opposite: an upper bound,
   `ms.snapshot.index < i`, otherwise it returns `ErrSnapOutOfDate` (`storage.go:246-248`).

kvreconf knows that upper bound only because it is the storage's only writer: its local `snapIndex` (`kv.go:310`,
`:323`, `:337-340`) tracks both `CreateSnapshot` and `ApplySnapshot`.

`CreateSnapshot` needs four facts at the call:
- `snapIdx < i`;
- `offset ≤ i`: `ms.ents[i-offset]`, given by the `Compact` spec's `ci ≤ snapshot index`;
- `i ≤ lastIndex`, which raft panics on (`storage.go:251-253`);
- the storage's term at `i` equal to the committed log's.

**Callers**
- kvreconf's `maybeSnapshot` (`kv.go:367-379`), called inside the committed-entries loop, before `Advance`, as
  well as after it;
- kv's snapshot path (`KV__run.lean:597-603`).

**Restatement**: split the predicate into two.
- **An exclusive token** for the snapshot index, `memSnapIdx γs si`, owned by the storage's writer. `CreateSnapshot`,
  `ApplySnapshot` and `InitialState`'s allocation take it and give it back updated. The spec takes `si < i`.
- **A persistent fact about committed entries only**: "if the storage holds index `i`, its term is the committed
  log's". It is provable because raft never hands the storage an entry that conflicts with a committed one. Get
  it from `deliveredLogLb`/the `Ready`'s `isCommittedLogLb` together with `appendReceipt`. Add
  `i ≤ lastIndex` as "every committed index above `si` is held", which is invariant across `Append`, `Compact` (at
  or below `si`) and `ApplySnapshot` (which moves `si`).

Say which resources the new `CreateSnapshot` takes (today's `memSnapRO`, `memKey`, the `cs` and `data` arguments).
The candidate lists only the premises.

### Tier 2

#### F4. [spec + trust base] The E6 Go change does not keep `ccDecodeV2_nil` out of kvreconf

**Principles**: *Know what it rests on*; *after a change, drop what existed only for it*.

**Evidence**
- kvreconf's rule is `ConfRule.validated := clamp fun _ _ e => ccDecode e` (§1, "kvreconf's `validConf`").
- With §5's Go change, kvreconf builds the empty `ConfChangeV2` for an empty type-2 entry without unmarshaling.
- To call `ApplyConfChange` on it, kvreconf must show `γ.rule … e = some o'`, where `o'` has the same effect as
  the empty change. That `o'` is `ccDecodeV2 []`, which nothing determines without the axiom (`CCModel.lean:52`,
  opaque). So kvreconf's proof needs the axiom anyway, or a rule of its own that special-cases empty data, which
  the candidate does not define.
- In both cases kvreconf's adequacy rests on the axiom through raft's U5 (§0: "Without it U5 cannot be proved").
  The Go change removes nothing from the trust base.
- It also makes kvreconf, which is meant as "a specification of how an application may use raft" (`kv.go:1-5`),
  special-case raft's encoding of its own leave.

**Restatement**: drop §5's `applyEntry` change. kvreconf unmarshals as today (`kv.go:443-447`), and its proof uses
`ccDecodeV2_nil` through `proto.Unmarshal`'s spec. Say in §0 that the axiom is in the trust base of every result
over raft, not only of U5.

The axiom itself is sound. `ConfChangeV2M` has proto2 presence, and the empty encoding decodes to every field
unset (`MarshalConfChangeV2.lean:27-37`). It still needs the user's approval.

#### F5. [spec, scope] Newcomers must start at `c0`: a Go change and an unfiled scope restriction

**Principles**: *No unneeded premise* (a scope restriction must be marked and filed); *Complete* for etcd's
pattern.

**Evidence**
- `RestartNode.spec` requires `confStateIs cs γ.c0` for every node, `nodeJoin` included.
- kvreconf today starts a newcomer on a fresh `MemoryStorage`, whose `InitialState` is an empty `ConfState`
  (`cluster.go:166-176`). etcd does the same for a member that joins an existing cluster (`RestartNode` on a
  fresh storage).
- §5 changes kvreconf's Go to give newcomers the bootstrap voters instead. Neither §6 nor `issues/` records that
  the API excludes an empty-configuration joiner.
- I believe the restriction is not needed for soundness:
  - a node with an empty configuration is never promotable, so it never campaigns or leads;
  - its votes do not depend on its own configuration (`raft.go`, `Step`'s `canVote`);
  - applying the bootstrap `AddNode`s from the empty configuration reaches `c0` once they are all applied.
- Supporting it would need `nodeConfig`'s fold relation relaxed for a joiner at `applied = 0`. That is real work,
  so a restriction may be the right call, but it must be stated.

**Restatement**: either
- record the restriction (§6, and a decision entry: "a joiner starts from the cluster's initial `ConfState`;
  etcd's empty-`ConfState` joiner is outside the API"), and keep §5; or
- add `RestartNode`'s second start for `nodeJoin`, `cs = ∅`, with `nodeConfig` given only after the bootstrap
  prefix is applied.

The kvreconf rows of the exclusion table below depend on this choice.

#### F6. [obligation, partly carried] The plan does not match the candidate's prerequisites

`notes/raft-unified-plan.md` at `HEAD` disagrees with §0 in six places:
- it has no U6m: its U6 lists only the client laws;
- U5 lacks the `RaftLeave` invariant;
- U4 lacks the "term 0 ⇒ every pre-vote granted" argument;
- U7 still has `msgCredits_readIndex/_prop` and "persistent proposal updates";
- "The spec" still has "the automatic leave a filler";
- U11 keeps "bounded ticks, campaigns and `MsgTimeoutNow` deliveries: the term budget", which the removal of
  credits makes unnecessary in Go.

None of these is a defect of the candidate; §0 carries U6m, U5 and U4. But the plan is what the stage agents will
read. Update it when the candidate is adopted.

### Tier 3

- **F7. [spec] `stepIn_intro`'s first premise is derivable.** `(st.msg.Type' ≠ MsgProp → SentMsgShape st)`
  follows from `sentMsg_shape`, and the premise also takes `sentMsg γ N src st`. Drop it.
  - Today's premise was `NetMsgOk` (`ApiVocab.txt:61-71`), which is not derivable.
  - Check that `SentMsgShape ∧ To = id` gives raft's `Step` proof what `NetMsgOk` gave it. One difference is
    known: `NetMsgOk` takes `MsgTransferLeader` as unstamped (`UnstampedType`, `ApiVocab.lean:275-277`), but the
    wire copy carries a term. U7 carries this ("`MsgTransferLeader` stepped", plan U7; §0 U7).
- **F8. [spec] `sentMsg_noTransfer` could also exclude `MsgTransferLeader`.**
  - It is true: no `TransferLeadership` call means no such message.
  - The server today uses both facts (`InvNet.lean:88-89`, `SentMsgOk.ne_timeoutNow` and `.ne_transferLeader`).
  - Without the second, the server's proof of `Step` depends on U7's new `MsgTransferLeader` handling.
- **F9. [spec] Drop `bootedCluster`** (§2, "kept"). Its only consumer was `stepIn_intro`'s pre-vote premise. The
  server's six uses (`NewServerAlloc.lean:230-233`, `NewServerAllocOn.lean:115-118`, `SrvRaftLog.lean:650`) all
  serve that premise. Drop `nodeBoot_booted` with it.
- **F10. [spec] `fold_total`'s decode premise has no stated reason.** With `r.Ok` and `c0.Valid`, a fold
  that consults only the rule is total. The premise matters only if `fold` returns `none` on an undecodable entry.
  Give `fold_snoc_conf`'s statement so the reader sees which; drop the premise if it is not needed.
- **F11. [spec] The stopped `Step` result is imprecise.** `node.Step` returns `nil` for a local type only when
  `!IsLocalMsgTarget(m.From)` (`node.go:480-483`). A local type from a local target goes on to `step` and returns
  `ErrStopped` or `ctx.Err()`. It returns an error for `m == nil` (excluded by the ownership of the argument; say so).
- **F12. [obligation, carried by §0] U6m adds two mechanisms where one would do.** Either `StepR.reject`, or
  `applyConf`'s "no undecided conf entry between", suffices. `advance`'s `NoConfIn r.full r.cidx a`
  (`StepR.lean:399`) needs the same treatment as `applyConf`'s (`:415`), or the reject steps must fire first
  (in `ApplyConfChange` or `Advance`). Pick one and apply it to both rules. Also, `nodeConfig_reject` is `|==>`
  but `nodeConfig_skip` is `⊢`; make them the same unless the update is needed.
- **F13. [spec, convention] Stopped specs as second spec files contradict CLAUDE.md** ("`Spec/<pkg>/<fn>.lean`:
  the one Hoare triple of a Go function").
  - They do have callers. kvreconf, after an `ApplyConfChange` that returned `null`, sets `r.cs = nil`
    (`kv.go:466-469`). It can then no longer meet the live specs' rule premises (`ApplyConfChange`, `Advance`'s
    `NoConfChangeIn`), so it needs the stopped ones.
  - The layout change (`etc/gen-interface.py --layout`) is carried neither by §0 nor by the plan's U9.
  - It changes a repository convention: ask the user. Review 6's alternative avoids the change: one triple, with
    precondition `isNode ∗ (live ∨ nodeStopped ∗ args)`.
- **F14. [spec] `snapshotCert_make`'s `SnapListsOk` premise is mostly derivable.**
  - Most of it follows from `m.Valid` (from `fold`) and `confStateIs cs m`: well-formedness, the `2^62` size, and
    `outgoing = [] → al = false` (`Ghost.lean:605-611`).
  - What remains is `i < 2^61`, and the lists' `Nodup` if `confStateIs` does not give it.
  - Take those two premises and prove `SnapListsOk` inside: fewer glue lines in kv and kvreconf.

## What is good

- **The certificate (E1)** has the right shape. It sits at the committed term, which `l.getLast?` forces to have
  `i > 0`. `snapshotCert_made` returns the term, the fold and `snapMade`. It is TaDa (`ownSnapsMade`/`snapMade`,
  `noSnapsEver` for clients that make none) with no caller predicate.
- **Credits are gone (E7, E13).** No client threads a resource only raft's bookkeeping needs. One
  `msgCredits_intro` covers duplication: each delivered `MsgProp` copy carries a fresh update per entry, minted
  from `proposalReg`.
- **`RaftLeave` and `opsOf`.** Raft's own leave, and a client's explicit `ConfChangeV2{}` at a joint
  `autoLeave` configuration, have the same bytes. Both are dropped from `opsOf`, so no update ever needs to
  fire for them. Not firing an at-most-once update is sound.
- **`ApplyConfChange`'s disjunctive post** is right. Once `run` has received the change from `confc`, it blocks
  on `confstatec` until the caller takes it: `done` is closed only by `run` itself (`node.go:343-`, `562-573`).
  So a `null` result means the change was never taken, and `nodeConfig v` is correct.
- **`ConfRule` over `(prefix, membership, entry)`** with `clamp`/`validated` matches kvreconf's `validConf`
  (`kv.go:205-229`). Every client's rule meets `Ok` for free.
- **One allocation** with two start kinds, `joinAuth`/`nodeJoin`, and `transferChoice` as a one-shot choice in
  place of two allocation variants: "one general spec".

## kvreconf's Go still excluded

| behaviour | where | excluded by | kind |
|---|---|---|---|
| a newcomer with an empty initial `ConfState` (today's Go, etcd's pattern) | `cluster.go:166-176` | F5 (§5 changes the Go) | spec scope, unfiled |
| `CreateSnapshot`, before and after `Advance` | `kv.go:316-317, 328-330, 367-379` | F3 (`storAppended`) | spec |
| unmarshalling raft's automatic leave | `kv.go:443-447` | the axiom's approval; F4 (the Go change does not help) | trust base |
| a joiner at `c0`; pre-votes at term 0 | `cluster.go:163-176` | U4 (§0) | obligation |
| `ApplyConfChange` after a rejected entry in the same `Ready` | `kv.go:455-470` | U6m (§0) | obligation |
| raft's automatic leave | `raft.go:740-760` | U5 (§0) | obligation |
| a forwarded or re-forwarded `MsgTransferLeader`; `MsgTimeoutNow` | `reconf.go:104` | U7 (§0) | obligation |

**Not excluded** (checked):
- the stopped paths, including `r.cs = nil` after a `null` `ApplyConfChange`, through the stopped specs;
- duplicated `MsgProp`;
- retried `Propose`;
- `ReadIndex`;
- `Campaign` and `ForgetLeader`;
- `TransferLeadership` with `lead = 0` (a local message, dropped by a follower that knows no leader);
- compaction, given `Compact`'s spec premise `ci ≤ snapshot index`;
- the storage wrapper's `ErrSnapshotTemporarilyUnavailable`, through the wrapper law. It is uncertain whether
  the `Storage` contract allows an `InitialState` fixed after `ApplySnapshot`; raft reads it only in `newRaft`.

## Ranking (most in need of revision first)

1. **Storage and `CreateSnapshot`**: F3.
2. **Laws that are false**: F1 (`isCommittedLogLb_length`), F2 (`clamp_eq`).
3. **Trust base and kvreconf's Go**: F4, F5.
4. **Plan alignment**: F6.
5. **Messages**: F7, F8, F9, F11.
6. **Vocabulary and model tidiness**: F10, F12, F14.
7. **Layout convention**: F13 (the user's decision).

## Uncertain

1. **F5**: that an empty-configuration joiner is sound under raft's protocol invariant as it stands. I argued it
   from the Go only.
2. **F3**: that raft's invariant ties the storage's entries at or below `commit` to the committed log, which the
   restated persistent fact needs. I did not check `InvStorage.lean`.
3. **F8**: whether the server's transport proof (`InvBuild.lean:163-185`) consumes the exclusion of
   `MsgTransferLeader` beyond `stepIn_of_recv`.
4. **E7**: that the receipt issued by `Tick`'s method call can be carried to `run` through `tickc`. Receipts come
   from Go instruction steps, so one exists in the caller's thread. U7 settles it.
