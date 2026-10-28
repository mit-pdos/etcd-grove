# Review of the unified node-API candidate 6 (candidate 5 + "Candidate 6 amendments"), round 6

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-5.md`, with its section "Candidate 6
  amendments" (D1-D11) taking precedence over the body. It is a design, not yet implemented, so no finding can be
  stale against `HEAD` (`0bc6998d9e`).
- **Compared with**:
  - today's API at `eb59bb8d1b`: `interface/Proof/go_etcd_io/raft/v3/InvNode.txt`, `InvNode.lean`, `ApiVocab.lean`,
    `interface/Spec/go_etcd_io/raft/v3/node__{Tick,Propose,ReadIndex}.txt`, `MemoryStorage__CreateSnapshot.txt`;
  - the protocol at `HEAD`: `Protocol/{Ghost,Model,CfgOverlap,StepR}.lean`, `InvRawnode.lean`, `CCModel.lean`, and
    `Spec/google_golang_org/protobuf/proto/{Marshal,Unmarshal}ConfChangeV2.lean`.
- **Go**:
  - raft a2, `.lake/raft-fork` `565c2bd`: `node.go`, `raft.go`, `storage.go`;
  - kvreconf at `HEAD`: `examples/kvreconf/{kv,cluster,reconf}.go`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md`. The worktree's own `.claude/skills/` has
  no `spec/`, so I used the main checkout's copy.
- **Not run**: lake build, lean-check, Go tests.

Each finding is classified as either:
- **[spec]**: a defect of the specification itself, which the candidate must change; or
- **[obligation]**: a proof obligation, saying whether the plan (`notes/raft-unified-plan.md`, U0-U11) or the
  candidate's prerequisites already carry it.

## Summary

Candidate 6 settles review 5's D4, D5, D6, D9, D10 (mostly) and D11. D1's direction is right: a decision type with
`reject`. D2's direction is right as well: raft pays its own receipts.

Two amendments overcorrect and introduce false laws:
- **D3**: a certificate at every term;
- **D7**: `readyFits` with no bound.

**D1**'s model change is incomplete. `StepR.applyConf` still requires no conf entry between `cidx` and the change
it applies, so a conf change applied after a rejected one in the same `Ready` is unprovable.

Three smaller defects:
- **D8**: the pre-vote premise is kept with a law that cannot hold, and the premise is unneeded;
- **`SentMsgShape`**: inherits a "`From ≠ To`" clause that a forwarded `MsgTransferLeader` breaks in kvreconf;
- **`ccDecode`**: decodes empty data "by definition", which hides a missing trust-boundary fact about `proto.Unmarshal`.

**Tier 1 (3)**: E1 (D3), E2 (D7), E3 (D1/U6m).
**Tier 2 (5)**: E4 (D8), E5 (`SentMsgShape`), E6 (empty bytes), E7 (D2 and `Tick`), E8 (§4's `storAppended`).
**Tier 3 (7)**: E9-E15.
**Go defects**: none new. I found no bug in raft or kvreconf's Go this round; nothing to file in `issues/`.

---

## Review 5's findings: fixed?

| review 5 | candidate 6 | status |
|---|---|---|
| D1 rejection not in the model | U6m: `CCDecision := apply op \| reject`; `entStep` keeps the state; `advance` moves past a rejected entry | **Half.** `entStep` is right. `StepR.applyConf` keeps `NoConfIn r.full r.cidx k` (`StepR.lean:414`), so a rejected entry still blocks the next applied one (E3). U6m is not in the prerequisites line (candidate l.15-18) nor in the plan |
| D2 receipts | raft takes its own; `readCredit`/`readCredits`/`tickCredit` leave | **Fixed in direction.** The body still has `Tick` "today's" (with `tickCredit γ 1`), `tickCredit` "kept", and `MsgTimeoutNow` "takes `tickCredit γ 1`" (E7) |
| D3 term of the certificate | `□ ∀ t, snapshotCert …` | **Regressed**: false in the dynamic mode (E1). Candidate 5's one-term form was right; what was missing was `CreateSnapshot`'s premise |
| D4 stopped `TransferLeadership` | unit | **Fixed.** `node.go:601-608` |
| D5 `committed_type2` vacuous | `committed_confDecodes` | **Fixed.** True: bootstrap by `BootLog`; proposals by `stepLeader`'s panic on undecodable data (`raft.go:1327-1338`). But see E6 for raft's own leave |
| D6 undefined names | `ConfEntryDecodes`, `SentMsgShape` defined | **Fixed as definitions.** `SentMsgShape`'s new clause is incomplete (E5); `ccDecode`'s empty-data clause needs a fact (E6) |
| D7 `2^61` with no bootstrap log | the bound only when `boot ≠ []` | **Wrong fix**: the post still gives `readyFits` unconditionally (E2) |
| D8 pre-vote premise | kept, plus a law giving `bootedCluster` from a non-empty log | **Wrong fix** (E4) |
| D9 `2^62` bound | in `Valid` and the `confchange` laws | **Fixed** |
| D10 clamp | `ConfRule.clamp`, `clamp_ok` | **Mostly.** `clamp_eq` is missing (E11) |
| D11 explicit leave | documented | **Fixed as documentation.** The U5 invariant behind `RaftLeave` is not listed (E12) |
| D12 text | not addressed | **Open** (E10) |

---

## Findings, ranked

### Tier 1

#### E1. [spec] `snapshotCert_make` at every term is false in the unified mode (D3 overcorrected)

**Principle**: *Sound*. The law must be provable from the protocol the candidate maps onto.

**Evidence**
- The API's certificate rests on `raftSnapCert` (`Protocol/Ghost.lean:1552-1557`). Its dynamic clause says:
  for every node, every `D` with `γ.dyn = some D`, and every recorded full log `fp` with `FullOk k.sid fp`,
  `D.fold fp = some k.cfgM`.
- `FullOk` (`Protocol/Model.lean:1135-1137`) requires `plogLast base0 fp = k.sid`, that is, the term **and** the index.
- At a term `t` other than the committed entry's term at `i`, such an `fp` is another log: for instance an older
  leader's, whose entry at `i` was overwritten. That log may contain conf entries that never committed, so its fold
  may differ from `m`. From `isCommittedLogLb γ l` nothing can be proved about it.
- The static mode had `∀ t` (`snapshotCert_static`; `storageCert_registerAny`, `InvNode.txt:11-46`) only because the
  dynamic clause is vacuous there: `raftSnapCert_static` needs `γ.dyn = none` (`Ghost.lean:1579-1590`).
- The unified mode is the dynamic one, so `□ ∀ t, snapshotCert …` cannot be proved. U2 ("`snapshotCert_make` over the
  dynamic clause of `raftSnapCert`") would find this.
- The amendment's justification ("the storage fixes the term: `CreateSnapshot` reads `Term(i)`", `storage.go:257`) is
  a true fact, but it belongs in `CreateSnapshot`'s spec, not in a certificate at every term.

**Callers**
- kv: `KV__run.lean:597-603` (`snapshotCert_static`, then `storageCert_registerAny`);
- kvreconf: `maybeSnapshot` (`kv.go:378`).

**Restatement**
1. Go back to candidate 5's form with the term named: `snapshotCert γ N {sid := ⟨lastTerm l, i⟩, …}`, for `i > 0`,
   where `lastTerm l` is the term of `l`'s last entry.
2. Drop `storageCert_registerAny`, or restate it at one term. `storageCert_register` already takes one `k`.
3. State `CreateSnapshot`'s premise to match (this was review 5's D3 restatement): from
   `storAppended st i ∗ deliveredLogLb n γ N l` with `l.length = i`, the caller learns that the storage's term at
   `i` is `lastTerm l`. The update asks `memStorCert γs (… i (lastTerm l) …)` at that term only, not `∀ t`.

#### E2. [spec] `cluster_alloc` gives `readyFits` with no bound when `boot = []` (D7 overcorrected)

**Principle**: *Sound*.

**Evidence**
- `readyFits γ N := ⌜receiptBound GF + γ.bootLen ≤ 2 ^ 61⌝` (`InvNode.lean:269-270` at `eb59bb8d1b`).
- After D7, a `boot = []` allocation assumes only `receiptBound GF ≤ 2^64 - 2`. Its post (candidate l.122) still
  gives `readyFits γ N` unconditionally, which cannot be proved from that premise.

**Callers**
- the server and kvreconf allocate with `boot ≠ []` and use `readyFits`;
- kv (`boot = []`) does not need it: it bounds its indices through its storage (`kvStorFloor`, `kv/Defs.lean:166-170`).

**Restatement**: in the post, `(if boot = [] then emp else readyFits γ N)`. Equivalently, review 5's form:
`⌜receiptBound GF + boot.length ≤ 2^61⌝ → readyFits γ N`. The fix is trivial, but the law as written is false.

#### E3. [obligation, not carried] U6m does not let `ApplyConfChange` follow a rejected conf entry before `Advance` (D1 incomplete)

**Principle**: *Sound/provable* from the declared prerequisite.

**Evidence**
- The amendment changes `entStep`, and lets `StepR.advance` move past a rejected entry.
- `StepR.applyConf` (`StepR.lean:407-417`) still requires `NoConfIn r.full r.cidx k`: there must be no conf entry
  between the model's `cidx` and the change applied at `k`.
- The model's `cidx` moves past a rejected entry only at `advance`, that is, at `Advance`.
- So in a `Ready` whose committed entries are `[A (rejected), …, B (applied)]`, kvreconf's `ApplyConfChange(B)`
  (`kv.go:346`, then `:466-470`) runs while `cidx ≤ A`, and `applyConf` cannot fire. The client already holds
  `nodeConfig` at `B`'s position, since `nodeConfig_reject` moved it past `A`. Without a model step, raft's proof of
  `ApplyConfChange` has no way to follow.
- This is reachable. The leader appends `B` only after it has applied `A` itself (`pendingConfIndex`,
  `raft.go:1340-1356`). But a follower that lags receives both committed in one `Ready`. kvreconf proposes
  unserialized changes, and rejects them in joint configurations as well (`reconf.go:41-71`).

**Restatement**: U6m must also do one of the following:
- add a step `StepR.rejectConf` (`cidx := k + 1`, `cfg` unchanged, at a committed conf entry decided `reject`); or
- weaken `NoConfIn` in both `advance` and `applyConf` to "every conf entry in `[cidx, k)` is decided `reject` at its
  prefix".

Also:
- put U6m in the prerequisites line (candidate l.15-18);
- add U6m to the plan, which lists only U6, "Rejection. `nodeConfig_reject`, `nodeConfig_skip`; …".

### Tier 2

#### E4. [spec + obligation] D8: the law it promises is false, and the premise is unneeded

**Principles**: *Sound*; *no unneeded premise*.

**Evidence**
- `bootedCluster γ := ⌜γ.raft.reBoot ≠ []⌝` (`InvNode.lean:486`). It is a fact about the cluster. In a `boot = []`
  cluster it is false whatever logs the nodes hold. So "`nodeRestartBoot`/`nodeJoin` give `bootedCluster` once the
  node holds a non-empty log" is false unless `bootedCluster` is redefined, and the candidate gives it no new definition.
- The premise exists because a pre-vote **rejected** at term 0 is sent with `Term: r.Term = 0`, and `send` panics on
  that (`InvRawnode.lean:2156-2159`; `raft.go:518-532`).
- That rejection never happens in any cluster:
  - a node at term 0 has an empty log: every entry carries a leader's term, which is at least 1, and taking an entry
    (`MsgApp`/`MsgSnap`) raises the receiver's term;
  - at term 0 with an empty log, a `MsgPreVote` (whose term is at least 1) passes `canVote` and `isUpToDate`, and is
    granted with `Term: m.Term` (`raft.go:1232-1240, 1270`).
- The existing argument ("in a booted cluster every node is past term 0", `ownLogGhost_boot`) is already false for
  kvreconf's joiners: `RestartNode` on an empty storage, at term 0, in a booted cluster (`cluster.go:163-176`). U4
  must re-prove `stepIn_intro` for them whatever is decided here. The plan's U4 ("a joiner admitted") does not name it.

**Callers**
- kvreconf (`PreVote` one time in two, `cluster.go:93`) holds `bootedCluster` from its founders, so the premise costs
  it nothing. It is the proof that breaks.
- kv (`boot = []`) could never deliver a pre-vote.
- The server uses `bootedCluster`/`nodeBoot_booted` six times. Those uses go away.

**Restatement**
- Drop the premise from `stepIn_intro`, and drop `bootedCluster` and `nodeBoot_booted`.
- Obligation for U4/U7: "term 0 implies an empty log, which implies every pre-vote is granted".

#### E5. [spec] `SentMsgShape`'s `MsgTransferLeader` keeps `SentMsgOk`'s `From ≠ To`, which kvreconf violates

**Principle**: *Sound* (`sentMsg_shape` must hold of every sent message).

**Evidence**
- `SentMsgOk` requires `From' ≠ To'` for every type but `MsgReadIndex` and the vote responses (`ApiVocab.lean:95-96`).
- `TransferLeadership` builds `{From: transferee, To: lead}` (`node.go:601-608`).
- A follower forwards it with `m.To = r.lead` (`raft.go:1757-1763`). `send` keeps a non-zero `From`
  (`raft.go:515-517`) and stamps the follower's term (`:542-544`).
- kvreconf passes a random transferee (`reconf.go:104`), which is often the leader. The wire then carries
  `From = To = leader`. The leader's `stepLeader` ignores it ("already leader", `raft.go:1666-1669`).
- So "today's `SentMsgOk` with `MsgTransferLeader` added" is false.
- The wire message's `From` is the transferee, not the sender. "No term" never occurs on the wire.

**Restatement**: `SentMsgShape`'s `MsgTransferLeader` clause is: `Term' ≠ 0`, `From' ≠ 0`, `To' ≠ 0`, no entries.
Exempt it from the `From ≠ To` clause.

U7's re-forward obligation stands. I checked it: a forward reaches `send`'s `Panicf` only if its target is a follower
at the same term that knows a leader, which would be a second leader of that term.

#### E6. [obligation, not carried; trust base] Empty conf-change bytes decode: a missing `proto` fact

**Principles**: *Know what it rests on*; *every premise has a source*.

**Evidence**
- `ccDecodeV1`/`ccDecodeV2` are opaque (`CCModel.lean:47, 52`). The `proto` specs say only that `Marshal`'s output
  decodes back (`MarshalConfChangeV2.lean:43-48`) and that `Unmarshal` computes `ccDecodeV2`
  (`UnmarshalConfChangeV2.lean`). Nothing says `ccDecodeV2 [] = some ⟨⟩`.
- Raft's own leave carries `nil` data (`raft.go:748`). Three places need that fact:
  - raft's own `stepLeader` unmarshals it and panics on failure (`raft.go:1333-1337`): U5;
  - kvreconf unmarshals it and panics on failure (`kv.go:445`);
  - etcd's server uses `MustUnmarshal`.
- The amendment's `ccDecode` ("empty data to the empty change") decides the case by definition. So
  `committed_confDecodes` holds of `ccDecode`, but a client cannot transfer it to the Go `proto.Unmarshal` it calls.

**Restatement**
- Add the trust-boundary fact: `proto.Unmarshal` of empty bytes gives the zero message, for `ConfChange` and
  `ConfChangeV2`. It is true of protobuf-go. It needs the user's approval, since it touches the trusted statements.
- Define `ccDecode e` by type: type 1 is `.v1 <$> ccDecodeV1 e.data`, type 2 is `.v2 <$> ccDecodeV2 e.data`, anything
  else `none`. With the fact above, the empty-data clause can go.

#### E7. [spec] D2 half-applied: `Tick`, and the body's credit clauses

**Principles**: *Complete* (the spec of a function every client calls must be determinate); *after a change, drop
what existed only for it*.

**Evidence**
- The amendment removes `tickCredit` from the API. But the body still has:
  - §3: `node.Tick` "today's", which takes `tickCredit γ 1` (`node__Tick.txt`);
  - §2: "Kept with their laws: … `tickCredit` (`⧗n ⊢ tickCredit γ n`)";
  - l.202: `msgCredits_readIndex` with `⧗1`;
  - l.212-213: `MsgTimeoutNow` "takes `tickCredit γ 1`";
  - l.249-250: `Campaign` "paid … `tickCredit`".
- `Tick` is called by every client's ticker (kvreconf `kv.go:285`; the server, through `tickCredit_intro`).

**Restatement**
- `node.Tick`: `{isNode} … {True}`, its receipt taken in raft's proof. The `select` has a pure step before it, and
  `default` drops the receipt. Whether that step exists is uncertain; U7 settles it.
- Drop `tickCredit`, `tickCredit_intro` and `tickCredit_zero` everywhere.

#### E8. [spec] §4's `CreateSnapshot` over an undefined `storAppended`

**Principle**: *every premise has a source*.

**Evidence**: `storAppended` exists nowhere at `HEAD` or `eb59bb8d1b`. A client needs three things from it:
- **the storage's term at `i`**, for E1;
- **an index bound below `2^61`**, for `snapshotCert_make`'s `SnapListsOk`. kv takes it today from `kvStorFloor`'s
  bound (`kv/Defs.lean:166-170`). A `boot = []` client has no `readyFits` (E2), and `isCommittedLogLb_length` gives
  only `< 2^64`;
- **the storage's snapshot index below `i`**. kvreconf panics on any error (`kv.go:378-379`), and `ErrSnapOutOfDate`
  is returned when `i ≤` the snapshot's index (`storage.go:246-247`). kvreconf rules that out with its local
  `snapIndex`; the spec must relate that to the storage.

**Restatement**: define `storAppended st i` (from `appendReceipt`) to carry:
- the storage's entries up to `i`, equal to the delivered log's;
- `i < 2^61`;
- the storage's snapshot index, so that the caller can know it is below `i`.

### Tier 3

- **E9. Consolidate.** The body contradicts the amendments in at least eight places:
  - l.15-18 (U6m missing);
  - l.116 (`2^61` with no condition);
  - l.127-129 (`committed_type2`);
  - l.134 (`tickCredit`);
  - l.164-170 (`snapshotCert_make`);
  - l.202, l.212-213, l.249-250 (credits);
  - and §3's `Tick`.

  Before U1, write candidate 6 as one text: a reader of the future `interface/` sees only the result.
- **E10. Review 5's D12 is still open.**
  - `ownCommittedOps_get_lb`/`_lb_prefix` must read `opsOf γ.rule γ.c0`, not `opsOf l` (`InvNode.txt:50, 161`).
  - The plan's "The spec" still says "the automatic leave a filler" and "persistent proposal updates".
- **E11. D10: add `clamp_eq`**:
  `(applyChange o m).isSome → r pre m e = some o → clamp r pre m e = some o`. etcd's and kv's proofs need it to
  discharge `ApplyConfChange`'s `γ.rule … = some o'` without unfolding `clamp`.
- **E12. D11 [obligation, not carried].** `RaftLeave` must hold of raft's own leave wherever it commits; otherwise
  `ownCommittedOps` (`opsOf`) would hold an entry for which no client update fired. Review 5 showed that it holds:
  `appliedTo` proposes only when `applied ≥ pendingConfIndex`, and the tracker equals the fold of the applied prefix.
  With rejections, it holds because the tracker follows the rule's decisions. List it with U5, whose text names only
  `c.autoLeave → role ≠ leader`.
- **E13. One law for `msgCredits`.** After D2:
  - `msgCredits_readIndex` is free;
  - `msgCredits_none` (`≠ MsgReadIndex`, `≠ MsgProp`) and `msgCredits_snapshot` were already redundant with each other.

  Replace all three with `st.msg.Type' ≠ MsgProp → ⊢ |==> msgCredits γ N st`.
- **E14. `snapshotCert_make`'s free binder `al`.** `SnapListsOk` is stated with `al`, but the certificate uses
  `m.autoLeave`. Use `m.autoLeave` in both. `SnapListsOk` includes `outgoing = [] → al = false`.
- **E15. Two triples per method against CLAUDE.md's "the one Hoare triple" per spec file.** Review 4 found the second,
  stopped spec to be a case split on the node's state, which the principles allow. Say how it is written so that it
  passes `--layout`: one triple whose precondition is `isNode ∗ (live resources ∨ nodeStopped ∗ arguments)`, with the
  post matching.

## What is good

- **D1's decision type** (`apply op | reject`, `entStep` keeping the state): this is the right repair. A rejection in
  a joint configuration becomes expressible, and `QOverlap` holds trivially across it (`QOverlap.refl`).
  `ConfRule ↦ CCDec` is computable: compute the fold of the prefix, then the rule.
- **D2** removes three resources (`readCredit(s)`, `tickCredit`, the `⧗1` of `msgCredits_readIndex`) that only raft's
  bookkeeping needed, and the allocation's read pool with them. The `Tick`/`select` provability is uncertain, but
  U7 settles it.
- **D4** is right (`node.go:601-608`).
- **D5** states what clients use: kvreconf panics on undecodable conf entries (`kv.go:439, 445`).
- **D9** and **D10's** `clamp_ok`: every client's rule can meet `ConfRule.Ok` without writing its own wrapper.
- **The rest of candidate 5** stands, as review 5 checked it:
  - one allocation with two start kinds;
  - the TaDa registries;
  - the stopped specs (re-checked: `node.go:331-341, 458-465, 514-608`);
  - `nodeConfig_reject`/`_skip` as client-side entailments, which is the right shape once E3 is fixed.

## kvreconf's Go still excluded

| behaviour | where | excluded by | kind |
|---|---|---|---|
| `CreateSnapshot` at the applied index | `kv.go:378` | E1 (no provable certificate at every term), E8 (`storAppended`) | spec |
| `ApplyConfChange` after a rejected conf entry in the same `Ready` | `kv.go:346, 466-470` | E3 (`applyConf`'s `NoConfIn`) | obligation (U6m incomplete) |
| unmarshalling raft's automatic leave (empty bytes) | `kv.go:445` | E6 (no `proto` fact) | trust base (needs approval) |
| `TransferLeadership` to the current leader, forwarded | `reconf.go:104` | E5 (`sentMsg_shape` false as defined) | spec |
| pre-votes to a joiner at term 0 | `cluster.go:163-176` | E4 (the proof's argument fails; the client has the premise) | obligation (U4) |
| a joiner at `c0` | `cluster.go:163-176` | U4 (declared) | obligation |
| `ApplyConfChange` after a concurrent restore | `kv.go:470` | U0 (declared) | obligation |
| a re-forwarded `MsgTransferLeader`; `MsgTimeoutNow` | `reconf.go:104` | U7 (declared) | obligation |

**Not excluded** (checked): duplicated `MsgProp` (both kinds) and `MsgReadIndex`, retried `Propose` (the client
mints the update per call), `ReadIndex` with fresh contexts, `Campaign`/`ForgetLeader`/`Status().Lead`, every call
after `Stop`, compaction (`Compact` errors are excluded by `first ≤ … ≤ hi`, `kv.go:392-397`), and
`ErrSnapshotTemporarilyUnavailable`.

§5's Go list is complete: the newcomer/founder `Storage`, and `r.cs` starting at `c0`.

## Ranking (most in need of revision first)

1. **The snapshot certificate and `CreateSnapshot`**: E1, E8.
2. **Rejection in the model, U6m**: E3.
3. **Allocation**: E2.
4. **Message vocabulary**: E5, E4, E13.
5. **The trust base for empty conf-change bytes**: E6.
6. **Credits and `Tick`**: E7.
7. **Text and laws**: E9-E12, E14, E15.

## Uncertain

1. **E7, D2**: that `Tick`, `ReadIndex` and `Step` each have a deterministic pure GooseLang step before their channel
   hand-off, and that the receipt can travel with the message to `run`. Not checked in the translation.
2. **E1**: I assume the API's `snapshotCert` keeps `raftSnapCert`'s dynamic clause, as U2 says. If it were redefined
   to depend on the term, for example "only if the term is the committed one", the leader's send path would have to
   discharge that condition from its storage's entries. That is a redesign the candidate does not describe.
3. **E8**: how kvreconf's proof would learn the storage's snapshot index under the new token. Today's spec shows it
   only inside the atomic update (`σt.ss.index'`).
4. **E4**: that every entry's term is at least 1 in a `boot = []` cluster. It follows from leaders' terms being at
   least 1 (`campaign` raises the term), but I did not find a lemma stating it.
