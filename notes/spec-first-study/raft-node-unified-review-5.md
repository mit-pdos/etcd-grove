# Review of the unified node-API candidate 5, round 5

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-5.md` (consolidated). It is a
  design, not yet implemented, so no finding can be stale against `HEAD`.
- **Compared with**:
  - today's API, `eb59bb8d1b`: `interface/Proof/go_etcd_io/raft/v3/InvNode.txt`, `interface/Spec/go_etcd_io/raft/v3/*.txt`,
    `NodeApiVocab.lean`;
  - the protocol at `HEAD` `421cfdadc5`: `Protocol/CfgOverlap.lean`, `Protocol/StepR.lean`,
    `Protocol/RefinementDyn.lean`, `InvConfchange.lean`, `InvApiDyn.lean`, `InvNode.lean`, `StepGhostMode.lean`.
- **Go**:
  - raft a2: `.lake/raft-fork`, `565c2bd`;
  - kvreconf at `HEAD`: `examples/kvreconf/*.go`;
  - kv: `examples/kv/kv.go` and its proof;
  - etcd's server: `server.go` at `a20f6760ff43`;
  - Perennial's receipts: `Receipts.lean`, `PostLifting.lean`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md`.
- **Not run**: lake build, lean-check, Go tests.

## Summary

Candidate 5 fixes review 4's findings in substance. The C1 race is gone in kvreconf's Go
(`cluster.go:255-275`: the duplicate is cloned and the type and target are read before `Step`), and the
kept-message contract is recorded in `issues/nonissues/raft-step-writes-caller-message.md`.

What is left:

**Tier 1 (one finding)**
- **D1. Rejecting a conf change is not a step of the protocol model.** The model's decoder cannot express
  "rejected: the configuration stays". In a joint configuration no change is a no-op, and `StepR.advance`
  cannot move past a conf entry that was not applied. So `nodeConfig_reject`, `Membership.fold`'s meaning of
  a rejection, and `Advance` past a rejected entry cannot be proved until the model changes, as `ApplyConfChange`
  could not before U0. The candidate does not list this as a prerequisite. kvreconf rejects changes all the
  time, in joint configurations too.

**Tier 2 (three findings)**
- **D2.** `ReadIndex` still takes `readCredit γ`, and with the allocation's read credits removed nothing gives
  one any more. More generally, raft's own proofs can take their time receipts from their own steps, as
  `Campaign` already does. That would make `readCredit`, `tickCredit` and the receipt in `msgCredits_readIndex`
  premises no caller needs to supply.
- **D3.** `snapshotCert_make` now certifies a snapshot only at the term of its last entry, but
  `storageCert_registerAny` and today's `CreateSnapshot` work at every term. The change to `CreateSnapshot` in
  section 4 has to fix the storage's term at `i`, and it does not say how. kv's snapshot path breaks here.
- **D4.** The stopped `TransferLeadership` returns an error in the candidate. In Go it returns nothing. This
  went backwards since review 4's C4.

**Tier 3**: text and small gaps (D5-D12):
- `committed_type2` says nothing (its weaker side always holds);
- `ConfEntryDecodes` and `SentMsgShape` are not defined;
- the receipt bound of `2^61` is required even with no bootstrap log;
- the pre-vote premise for clusters not started from a bootstrap log;
- the F9 laws against raft's `2^62` bound on tracked ids;
- a clamp for rules, so that every client's rule meets `ConfRule.Ok`;
- a client's explicit leave being taken for raft's own leave;
- the `ownCommittedOps` text.

**Go defects**: none new. The C1 race is fixed. The raft documentation gap is recorded as a non-issue
(`issues/nonissues/raft-step-writes-caller-message.md`).

---

## Review 4's findings: fixed?

| review 4 | candidate 5 | status |
|---|---|---|
| C1 kvreconf race | Go fixed (`15851e8158`) | **Fixed.** `cluster.go:255-264` clones `dup` before `step`, and `step` reads `typ, to` before `Step` (`:270-272`). Raft's documentation gap is filed as a non-issue |
| C2 `boot = []` branch unusable | `BootLog` only under `boot ≠ []` | **Fixed.** Leftover: D7 (the `2^61` bound) and D8 (`bootedCluster`) |
| C3 registry by bytes | split by type; `ProposeConfChange` takes no registration | **Fixed in shape.** `ConfEntryDecodes` is not defined (D6) |
| C4 stopped answers | `ctx.Err()`; `Step` of a local message `nil` | **Mostly fixed.** Checked against Go: `node.go:475-483` and `514-550`. `TransferLeadership` is now misstated (D4) |
| C5 a2 window | U0 listed as a prerequisite | **Fixed as text.** At `HEAD`, `applyConf` still requires `r.snap = false` (`StepR.lean:410`), and the `snapRestore` docstring still says it moves `cidx` (`:38-43`). U0 is unfinished, but it is now declared |
| C6 read credits | "all from time receipts" | **Half.** No law gives `readCredit γ`, which `ReadIndex` needs (D2) |
| C7 transfer | exclusive `transferChoice`; U7 owns the re-forward `Panicf` | **Fixed** |
| C8 joiner | U4 prerequisite | **Deferred as declared.** Still uncertain |
| C9 register-everything | `proposals_all` | **Fixed.** Sound: `proposalReg` asserts nothing raft relies on, and `ownProposals γ ∅` is consumed |
| C10 learners' tokens | restart tokens for `c0.ids` | **Fixed** |
| C11 Restore law | "any `cs` with `confStateIs cs m`" | **Fixed.** Missing: a premise on the size bound (D9) |
| C12 `ownProposals γ ∅`, elem law | both present | **Fixed** |
| C13 stopped `ApplyConfChange` | ownership returned | **Fixed.** Go: `node.go:562-573`. After `Stop`, `confc` and `confstatec` have no receiver, so the result is `nil` |
| C14 text | `committed_type2` with named predicates | **Named, but the statement says nothing** (D5) |

---

## Findings, ranked

### Tier 1

#### D1. A rejected conf change is not a step of the protocol model (unprovable until the model changes)

**Principle**: *Sound/provable* from the protocol's machinery; declare the prerequisite, as for U0 (C5).

**What the candidate says**
- `ConfRule`: `none` means "reject it without calling `ApplyConfChange`".
- `Membership.fold`: "rejections and other entries leaving it".
- `nodeConfig_reject`; `Advance` with `NoConfChangeIn` from `v.applied`, which `nodeConfig_reject` lets the
  client move past a rejected entry.
- Section 6: the protocol "fixes the configuration function in its ghost names (`RaftNames.reDyn`)".

**Evidence: the protocol cannot express a rejection**
- `reDyn` is `DynCfg.ofFold dec c0`, with `dec : CCDec = List EntryM → EntryM → Option CCOp`
  (`CfgOverlap.lean:233`).
- Its step is `entStep dec pre s e := if IsConfEnt e then (dec pre e).bind (ccStepB · s) else some s`
  (`:237-239`).
  - A conf entry that `dec` maps to `none` makes the fold `none`: there is no configuration after it.
  - A rejection must therefore be a `CCOp` that leaves `s` unchanged.
- In a joint configuration no such `CCOp` exists:
  - `simpleM` and `enterJointM` both fail when `s.cfg.outgoing ≠ ∅` (`InvConfchange.lean:178, 189`);
  - `leaveJointM` changes the configuration (`:210-213`);
  - `ccApplyM` has no other case (`CCApply.lean:60-66`).
  - etcd's `NodeID = 0` trick (`CfgOverlap.lean:229-231`) works only in a simple configuration.

**Evidence: the protocol cannot move past one**
- `StepR.advance` needs `NoConfIn r.full r.cidx a` (`StepR.lean:399`).
- `StepR.applyConf` needs `dec … = some op ∧ ccStepB op r.cfg = some cs'` (`:415-416`).
- No step moves `cidx` past a conf entry without changing `cfg`. So a node whose application rejects an entry
  can never `Advance` past it in the model.
- Today's dynamic `Advance` avoids this: it requires every delivered conf entry to be applied
  (`node__Advance.txt`, `dynamicSpec`).

**Callers**
- kvreconf rejects whatever `validConf` refuses (`kv.go:455-463`). That includes, in a joint configuration,
  every simple change and every `EnterJoint` (`reconf.go:41-71` proposes them at random), and a leave of a
  configuration that is not joint.
- kv's rule must reject type-2 entries (kv applies only type 1, `kv.go:279-285`).

**Restatement.** Add to the candidate's prerequisites a model change in the style of U0. For example:
- `entStep` with a skip: `dec : List EntryM → EntryM → Option (Option CCOp)`, where `some none` keeps `s`.
  Alternatively, build `DynCfg` directly from `Membership.fold`. `DynCfg` needs only `fold` and `adj`, and
  `adj` survives a skip because `QOverlap c c` holds;
- a `StepR.rejectConf` (`cidx := k + 1`, `cfg` unchanged, at the next conf entry, committed), or let `advance`
  move past entries the decoder skips.

`RInv` ("the configuration is the fold of the first `cidx` entries") then carries over. List it as a
prerequisite of `nodeConfig_reject` and of `Advance`'s spec. (The plan's U6 names the laws but not the model
change.)

### Tier 2

#### D2. `ReadIndex` has no source of `readCredit`, and raft can pay its own receipts

**Principles**:
- *Complete*: the caller can establish the precondition;
- *No unneeded premise*;
- *Do not make callers thread a resource only the proof's bookkeeping needs*.

**Evidence**
- `node.ReadIndex` is "today's". Today's version takes `readCredit γ` (`node__ReadIndex.txt`), and
  `readCredit_eq : readCredit γ ⊣⊢ readCredits γ 1` (`InvNode.txt:249`).
- The candidate removes "`readCredits` at allocation" and lists no `⧗1 ⊢ readCredit γ`. Only
  `msgCredits_readIndex` (for a message stepped from the network) and `tickCredit_intro` are kept.
- So no caller can call `ReadIndex`: kvreconf (`kv.go:576`), kv, and the server (whose reads today come from
  the allocation's split, `SrvRaftLog.lean:1572`).
- Raft's own proofs can take receipts from their own steps: any deterministic pure Go instruction gives a
  `⧗ 1` (`wp_go_step_receipt`, `Perennial/Golang/Theory/PostLifting.lean:378`). The candidate already pays
  `Campaign`'s term increase this way ("paid by the call's receipt").

**Restatement**
- At least add `readCredit_intro : ⧗1 ⊢ readCredit γ`.
- Better: let each raft spec take its own receipt from its own steps:
  - `ReadIndex` without `readCredit`;
  - `Tick` without `tickCredit γ 1`;
  - `Step` of a `MsgReadIndex` or `MsgTimeoutNow` without `msgCredits_readIndex`'s `⧗1` or `stepIn_intro`'s
    `tickCredit`.
- `readCredit`, `tickCredit` and their laws then go ("after a change, drop what existed only for it").
- **Uncertain**: whether each function has a pure step before its hand-off on which the proof can take the
  receipt. `Tick`'s and `stepWithWaitOption`'s `select` are preceded by such steps in GooseLang. I did not
  check that the hand-off can carry the receipt to `run`.

#### D3. `snapshotCert_make` only at the last entry's term; the `CreateSnapshot` premise to match is unstated

**Principle**: *Complete* for kv; *every premise has a source*.

**Evidence**
- `snapshotCert_make` gives `□ ∀ t, ⌜last term of l = t⌝ → snapshotCert γ N {sid := ⟨t, i⟩, …}`.
- Today's `snapshotCert_static` gives the certificate at every `t`, and so does `storageCert_registerAny`
  (`InvNode.txt:11-46`).
- Today's `MemoryStorage.CreateSnapshot` asks the caller for `□ ∀ t, memStorCert γs (… i t …)`
  (`MemoryStorage__CreateSnapshot.txt`), because the term is chosen inside the storage (its entry at `i`).
- With a certificate at one term only:
  - the caller must call `storageCert_register` at that `t`;
  - `CreateSnapshot`'s new spec must take `memStorCert` only at the storage's term at `i`;
  - it must relate that term to the committed log's.
- Section 4 says only "`storAppended st i` … instead of the floor token". It does not say that the token pins
  the storage's entry `i` to the delivered log, nor at which term the certificate is asked for.

**Callers**
- kv: `KV__run.lean`'s docstring: "certified (`snapshotCert_static`) and registered at any term
  (`storageCert_registerAny`)".
- kvreconf: `maybeSnapshot`, `kv.go:375`.

**Restatement.** State `CreateSnapshot`'s pre as:

> `storAppended st i` gives the storage's term `t_i` at `i`, equal to the delivered log's entry `i`; the
> caller's `memStorCert γs (… i t_i …)` at that term only.

Drop `storageCert_registerAny`, or restate it with the conditional term. Alternatively, say why the term
became restricted. If the protocol accepts any term, as the static mode did, keep `∀ t`.

#### D4. The stopped `TransferLeadership` is given an error result

**Principle**: *Sound*.

**Evidence**: section 3 lists `TransferLeadership` among the methods that return "`ErrStopped` or `ctx.Err()`".
`node.TransferLeadership` returns nothing (`node.go:601-608`). Review 4's C4 had it right ("unit"); the
consolidation moved it.

**Restatement**: the stopped `TransferLeadership` returns unit, like `Advance`, `Tick` and `Report*`.

### Tier 3

- **D5. `committed_type2` says almost nothing.**
  - Every committed type-2 entry's data decodes as a `ConfChangeV2`, raft's own leaves included:
    `confChangeToMsg(nil)` (`raft.go:748`), whose `[]` is the empty `ConfChangeV2`. So `ClientConfEntry`
    always holds, and the `RaftLeave` disjunct adds nothing (*no vacuous guarantee*).
  - What clients use is "every committed conf entry decodes":
    - kvreconf panics on undecodable type 1 or type 2 (`kv.go:437-447`);
    - etcd's server unmarshals with `MustUnmarshal`.
  - State it as `committed_confDecodes : isCommittedLogLb γ l ⊢ ⌜∀ e ∈ l, e.isConfChange → ∃ o,
    MarshalsConfChange (some o) e.data ∧ e.type = confChangeEntryType (some o)⌝`.
  - It is true:
    - bootstrap entries satisfy it by `BootLog`;
    - `ProposeConfChange` entries by their marshaling;
    - raft's leave decodes;
    - a refused conf proposal becomes a normal filler (`raft.go:1359`).
  - Keep `RaftLeave` for `opsOf`.
- **D6. `ConfEntryDecodes` (in `sentMsg_prop`), `SentMsgShape` and `ClientConfEntry` are not defined.**
  `SentMsgShape` does not exist at `HEAD` (only `SentMsgOk`, `ApiVocab.lean:91`). Define `ConfEntryDecodes`
  with the type tied to the change kind, as review 4's C3 restatement did, or kvreconf cannot build the
  update of a duplicated copy.
- **D7. `receiptBound GF + boot.length ≤ 2^61` even when `boot = []`.**
  - Its only consumer is `readyFits` (`InvNode.lean:262-270`).
  - Today's `cluster_alloc_static` needs only `≤ 2^64 - 2`. kv's `Main` gives `≤ 2^63`
    (`kv/Main.lean:10`, `Adequacy.lean:144`), so kv's theorem would shrink to executions of fewer than `2^61`
    steps.
  - Fix: give `readyFits` under the premise (`receiptBound GF + boot.length ≤ 2^61 → readyFits γ N` in the
    post), and keep `receiptBound GF ≤ 2^64 - 2`, or whatever D2 leaves.
- **D8. Pre-votes in a cluster not started from a bootstrap log.**
  - Today `stepIn_intro` needs `⌜≠ MsgPreVote⌝ ∨ bootedCluster γ` (`InvNode.lean:495-504`).
  - `bootedCluster` comes only from `nodeBoot`. Its source is the mode flags of `NsLink`
    (`StepGhostMode.lean:275`), which the unified mode removes.
  - The candidate says `stepIn_intro` "admits every `SentMsgShape` message", without saying whether this
    premise goes.
  - If it stays, a `boot = []` cluster with `PreVote` cannot deliver pre-votes. kv runs without `PreVote`
    today, but the general spec should not split on it.
  - State that it goes (a U7 obligation), or that it stays, with the reason.
- **D9. The F9 laws and the bound on tracked ids.**
  - `Membership.applyChange` is `ccStepB`, which fails at `2^62` tracked ids (`CfgOverlap.lean:224-225`,
    `InvApiDyn.lean:73`). `confchange` and kvreconf's `validConf` have no such bound.
  - So "`Simple`/`EnterJoint`/`LeaveJoint` succeed exactly when `applyChange` is `some`" needs the premise
    "the result tracks fewer than `2^62` ids".
  - kvreconf has at most 9 replicas, so the premise is easy, but the law as stated is false.
- **D10. A clamp for rules.**
  - `ConfRule.Ok` ranges over every valid `m`, joint ones included. etcd's rule ("the change, or its `NodeID`
    0 copy") fails on a joint `m`, and so does kv's (decode every type-1 entry).
  - Each client would write its own clamp. Generalize `validated`:
    - `ConfRule.clamp r := fun pre m e => (r pre m e).bind fun o => if (applyChange o m).isSome then some o
      else none`;
    - with `clamp_ok`;
    - and `clamp_eq : (applyChange o m).isSome → r pre m e = some o → clamp r pre m e = some o`;
    - then `validated = clamp ccDecode`.
  - This also corrects the `ConfRule.Ok` docstring, which says etcd's rule "may produce others".
- **D11. A client's explicit leave counts as raft's.**
  - kvreconf proposes `&pb.ConfChangeV2{}` one time in eight (`reconf.go:40-42`). Its bytes are `[]`, the
    same as raft's leave.
  - Committed where the fold is joint with `autoLeave`, it is a `RaftLeave` and outside `opsOf`, so the
    client's `ProposeConfChange` update never fires, although the entry is applied.
  - This is sound: the update promises nothing. Say so in `opsOf`'s or `RaftLeave`'s docstring.
  - I checked that raft's own leave is always a `RaftLeave` where it commits:
    - `appliedTo` proposes it only on a leader with `applied ≥ pendingConfIndex` (`raft.go:741-760`);
    - `pendingConfIndex` covers every conf entry appended since `becomeLeader`, and the log at
      `becomeLeader`;
    - so the log has no conf entry after `applied`, and the fold of the prefix is the tracker's joint
      configuration with `autoLeave` set.
  - That is a U5 obligation; list it with U7's.
- **D12. Text.**
  - "Kept with their laws: `ownCommittedOps` (its meaning: `opsOf γ.rule γ.c0` of the committed log)". Today's
    `ownCommittedOps_get_lb`/`_lb_prefix` mention `opsOf l` with no rule (`InvNode.txt:50, 161`). Restate both.
  - The plan (`notes/raft-unified-plan.md`, "The spec") still says "the automatic leave a filler" and
    "persistent proposal updates".

## What is good

- **One cluster, one allocation, two kinds of start.** The `boot = []` branch is now usable. There are restart
  tokens for every id of `c0`, `joinAuth` starts at `c0.ids`, and the client's resources (`ownProposals γ ∅`,
  `ownSnapsMade γ []`, `transferChoice`) come at allocation.
- **The registry split by type** matches what raft knows:
  - every type-0 `MsgProp` entry comes from `node.Propose` (`node.go:471-473`);
  - every conf entry comes from `confChangeToMsg` (`:487-494`);
  - a leader's refusal rewrite (`raft.go:1359`) never forwards.
  - `proposals_all` keeps the server and kv free of the registry.
- **The stopped specs are sound** (except D4), checked against `node.go:331-341, 458-465, 514-550, 555-608`. A
  `nil` from `ApplyConfChange` means "not applied": once `run` takes the change it always sends the
  `ConfState`, because only `run` closes `done`.
- **`RaftLeave`** classifies raft's leave by position, which makes `opsOf` monotone in the log, and the
  invariant behind it is provable (D11).
- **The decision on `γ.rule`** (section 6) is stated as a departure, and etcd's `shouldApplyV3` scope is
  correct: `server.go:2047-2053` skips `ApplyConfChange` only when the entry is at or below the consistent
  index, which needs a restart.
- **`Status`** with no content: enough for kvreconf, which only passes `Status().Lead` to
  `TransferLeadership`, whose spec accepts any `lead` (`reconf.go:104`). `Dump` is test-only.

## kvreconf's Go still excluded

| behaviour | where | excluded by | finding |
|---|---|---|---|
| a committed conf change rejected (`validConf` false), above all in a joint configuration | `kv.go:455-463`; `reconf.go:41-71` | the model has no rejection step | D1 |
| `ReadIndex` (every read, retried) | `kv.go:576`, `cluster.go:325-333` | no source of `readCredit` | D2 |
| `CreateSnapshot` at the applied index | `kv.go:375` | certificate at one term; `CreateSnapshot`'s pre unstated | D3 |
| a joiner (`startNew`, `RestartNode` at `c0`) | `cluster.go:166-178` | U4 (uncertain); Go change listed (§5) | C8 |
| `ApplyConfChange` after a concurrent restore | `kv.go:463` vs `cluster.go:270` | U0 (declared) | C5 |
| forwarded `MsgTransferLeader`; `MsgTimeoutNow` | `reconf.go:104` | U7 (declared) | C7 |

**Not excluded** (covered by the candidate, checked):
- duplicated messages, of `MsgProp` (both kinds) and `MsgReadIndex`;
- every call after `Stop` (`kv.go:303-307`, `cluster.go:346-350`), with D4 fixed;
- `Campaign`, `ForgetLeader`, `Status().Lead`;
- joint configurations and automatic leaves;
- client explicit leaves (D11);
- snapshots between applied entries, and compaction (compaction is reached only after a non-snapshot
  `Advance`'s floor: after `ApplySnapshot`, `hi < first`, `kv.go:384-397`);
- `ErrSnapshotTemporarilyUnavailable`.

The counters `nextOp` and `nextRead` stay below `2^64` by receipts, as `idutil`'s do.

**§5's list** looks complete for raft's spec: the newcomer `Storage`, and `r.cs` starting at `c0`.
`validConf(nil, …)` (`kv.go:220`) is reached only after a stopped `ApplyConfChange` sets `r.cs = nil`, where the
stopped spec covers it. The plan's U11 items "bounded ticks, campaigns, `MsgTimeoutNow` deliveries" become
unnecessary if receipts pay for them (D2).

## Ranking (most in need of revision first)

1. The rejection semantics: `ConfRule`, `fold`, `nodeConfig_reject`, `Advance` (D1: an undeclared model change).
2. The credits: `ReadIndex`, `Tick`, `msgCredits_readIndex`, `stepIn_intro` (D2).
3. The snapshot certificate's term, and `CreateSnapshot`/`storageCert_registerAny` (D3).
4. The stopped specs (D4).
5. Allocation details (D7, D8); vocabulary (D5, D6, D9, D10); text (D11, D12).

## Go defects

None new. The review-4 race in kvreconf is fixed at `HEAD`. Raft keeping and writing the stepped message is
recorded in `issues/nonissues/raft-step-writes-caller-message.md`.

## Uncertain

1. **D2**: that each node method has a pure step before its channel hand-off from which raft's proof can take
   the receipt, and carry it to `run`.
2. **D3**: why the certificate's term became restricted. If the protocol tolerates any term, as the static
   mode did, the `∀ t` form can stay.
3. **D8**: whether the unified mode drops the pre-vote premise.
4. **C8**: a joiner at `c0` with an empty log beside founders, in `RInv`.
5. **Not checked**: the details of F9-F11 and of the storage wrapper law.
