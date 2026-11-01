# Review of the unified node-API candidate 13, round 12

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

## What was reviewed

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-13.md`. §13.1-13.4 are new, and I
  read them hardest. I then reread every candidate-12 statement below them, looking for any that still mention the
  rule. It is a design and nothing of it is implemented, so no finding can be stale against `d9cdd1e4e1`.
- **Feasibility study**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/tada-decisions-feasibility.md`.
- **Today's API**: read at `d9cdd1e4e1` with `git show`: `interface/Proof/go_etcd_io/raft/v3/{ConfRule,InvNode,NodeApiVocab,ApiVocab}.txt` and `interface/Spec/go_etcd_io/raft/v3/node__{ProposeConfChange,ApplyConfChange}.txt`.
- **Protocol**: read at `d9cdd1e4e1`:
  - `Protocol/CfgOverlap.lean` (`CCDecision` :237, `fold_adjacent` :372);
  - `Protocol/StepRInv.lean` (`RInv` :238-251, `RInv_init` :322);
  - `Protocol/GhostState.lean` (`dynEnv` :152);
  - `Protocol/Ghost.lean` (`cqAt`/`WitOk` :2505-2535, `Filler` :1022);
  - `CCModel.lean` (`MarshalsConfChange` :240);
  - `Spec/.../RawNode__ProposeConfChange.lean` (:77-100);
  - `Spec/google_golang_org/protobuf/proto/UnmarshalConfChangeV2Empty.lean:31`.
- **Go**:
  - raft at `.lake/raft-fork` `565c2bd`: `raft.go:737-763` (`appliedTo`), `raft.go:1325-1372` (`stepLeader`, `MsgProp`), `bootstrap.go` (`Bootstrap`);
  - kvreconf: `examples/kvreconf/{kv,reconf,cluster}.go`;
  - kv: `examples/kv/kv.go`;
  - etcd's server: `etcdserver/server.go:1920-2110` (module `server/v3@v3.0.0-20261027220749-a20f6760ff43`).
- **Clients' proofs**, read at `d9cdd1e4e1`:
  - kv: `Proof/github_com/mit_pdos/etcd_grove/examples/kv/Defs.lean:257-280`;
  - server: `Proof/go_etcd_io/etcd/server/v3/etcdserver/{InvApplier.lean:90-98,KVModelDefs.lean:160-200,InvCfgView.lean:1-130,NewServerAlloc.lean:216}`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md`. The worktree has no `spec/` skill.
- **Not run**: lake build, lean-check, Go tests.

## Summary

The decision design is right and it is TaDa:
- the library hands the client a one-shot, exclusive permission per log position;
- the client keeps whatever invariant it wants over the permissions;
- the library predicates take no client predicate.

What the protocol needs is checked when a decision is recorded (`d.step m = some m'`), so `ApplyConfChange` needs
only the recorded decision. I spot-checked the protocol's tolerance for arbitrary decisions and it holds:
- `CCDecision.step` takes any op (`CfgOverlap.lean:244`);
- `fold_adjacent` is proved for an arbitrary `dec` (`CfgOverlap.lean:372`);
- `dynEnv`'s `a` is the node's configuration index, which is decided (`GhostState.lean:152-165`).

Two problems are serious. A third statement is unprovable as written:
- **L1 (missing law).** Making `opsOf` a pure filter loses the only fact that tells a client where empty
  `ConfChangeV2`s sit in the log. etcd's server panics on any `EntryConfChangeV2` (`server.go:1957-1961`). Under
  candidate 12 it ruled them out through `RaftLeave` and its own ops; under candidate 13 nothing does.
- **L2 (false as written).** `confAt_normal` puts its entry premise inside a pure implication, with `e` free. Read
  literally, it gives `confAt` past any position, including past the committed log.
- **L3 (unprovable as phrased).** "`ProposeConfChange` of an empty `ConfChangeV2` takes no update" needs
  `Marshal(ConfChangeV2{}) = []`, and nothing states that.

**Tier 1 (2)**: L1, L2. **Tier 2 (3)**: L3, L4, L5. **Tier 3 (4)**: L6-L9.

## What is good

- **TaDa, one-shot, client-owned.** The design follows "TaDa, not HoCAP" and "a once-only resource is not spent
  per call":
  - `confDecideTok γ k` is exclusive and consumed;
  - `confDecided`/`confAt` are persistent and agreeing;
  - a token belongs to a position, so a retry or a second applier spends nothing.

  Any policy is a client invariant, the out-of-band random unanimous one included: the decider fires the token
  and the appliers read `confDecided`.
- **Smaller vocabulary.** `ConfRule`, `Ok`/`clamp`/`validated`, `Membership.fold` with its four laws, `RaftLeave`
  and `opsOf r c0` all go ("After a change, drop what existed only for what it changed"). `opsOf` becomes a
  decidable filter, which makes it testable.
- **Validity at record time.** `ConfDecision.step (.apply o) = (applyChange o ·).filter Valid` puts the protocol's
  bound in one place. `confAt_valid` then gives every client `m.Valid` (and so `WellFormed`, for
  `Restore`/`Changer`) without a rule-`Ok` premise.
- **etcd's rejection is modelled faithfully.** `server.go:2035-2036` zeroes `NodeId` and calls `ApplyConfChange`,
  and confchange skips `NodeID` 0. Recording this as `.apply` of the zeroed change is exact. The result is allowed
  because etcd's membership is never joint, so `Simple` succeeds.
- **kvreconf's concurrent appliers work.** At position `k` a replica holds:
  - `nodeConfig v` with `v.applied = k`, which gives `confAt γ k v.membership` (`nodeConfig_confAt`);
  - `deliveredLogLb ⊢ isCommittedLogLb` (`InvNode.txt:83`);
  - `committed_confDecodes`.

  It opens its invariant (`∀ k ≥ boot.length, tok k ∨ ∃ d, confDecided γ k d ∗ policy`). Either it fires
  (`confDecide`, a plain `==∗`, no mask), or it reads `d` and gets `d = validated m e` through `confAt_agree` and
  `isCommittedLogLb_agree` (`InvNode.txt:100`). That is what its own `validConf` returned (`kv.go:484`).

  A stopped replica (`ApplyConfChange` answered `nil`, `kv.go:488-490`) never needs to fire: it holds
  `nodeStopped`.
- **Raft's automatic leaves are no special case.** The client decides them like any entry.
  - Applying the leave is allowed exactly where the configuration is joint. The client checks this itself:
    `validConf` runs `LeaveJoint`, and `ccDecodeV2_nil` covers the decode.
  - Skipping one is safe for Go: the leader proposes the leave again on the next `appliedTo` while it is still
    joint (`raft.go:742-763`). Only liveness is at stake.

## Findings

### Tier 1

**L1 [spec + obligation]. Export where empty `ConfChangeV2`s can be committed.** (Complete: sufficient for every
caller.)

- **Evidence.**
  - etcd's `apply` panics on any entry type other than 0 or 1 (`server.go:1956-1961`, "unknown entry type").
  - Its proof keeps "every committed entry is normal or a v1 conf change" (`entriesFrom`, `InvApplier.lean:90-98`;
    `srvIdxOkW`, `KVModelDefs.lean:166-170`), from what its ops updates give (`srvIdxOkW_snoc`, :173-195). An
    entry outside the ops has so far been a filler (type 0).
  - Candidate 12 kept this argument: an empty V2 was dropped from ops only as a `RaftLeave`, that is at a joint
    configuration. The server's configurations are never joint (`srvCfgOk`: `Membership.simple W`,
    `InvCfgView.lean:121-125`), so every empty V2 stayed in ops, where the server's invariant excludes type 2.
  - §13.1 drops every empty V2 from `opsOf`. §13.3's U5 bullet makes "an automatic leave only at a joint
    configuration" raft's internal invariant. No law gives it to a client, so the server can no longer exclude a
    committed empty V2 and cannot prove its `apply` never panics.
  - kv has the same gap (`examples/kv/kv.go:280,364`: a V2 entry is never passed to raft). Without the law, kv must
    keep tokens and decide `.skip` for V2 entries it never proposes.
  - The same gap makes §13.2's claim "the configuration is joint there, so it is allowed" unprovable for a client.
- **Restatement.** Add to `InvNode`:

  ```lean
  /-- A committed empty `ConfChangeV2` sits at a joint configuration: raft's leader appends one only
  when its applied configuration is joint and no conf change is pending (raft.go:1344-1356, with
  `DisableConfChangeValidation = false`; the automatic leave of raft.go:742 only under `AutoLeave`). -/
  theorem committed_emptyV2_joint : isCommittedLogLb γ l ∗ confAt γ k m ⊢
      ⌜l[k]? = some e → e.isEmptyV2 → m.isJoint⌝
  ```

  It holds of a client's explicit leave as well as raft's automatic one, so it needs no "raft's leave" notion.
- **Obligation (U5, reworded).** The leader's tracker is `confAt` at its applied index. With `alreadyPending` false,
  no conf entry lies between the applied index and `lastIndex`: `pendingConfIndex` is set at `becomeLeader`
  (:976) and at every accepted conf proposal (:1361). So the configuration at the appended position is the
  tracker's. A leader never has a snapshot pending (`RInv.lead_snap`).
- **Affects**: etcd's server (no-panic in `apply`), kv, and §13.2's text.

**L2 [spec]. `confAt_normal` is false as written; `confAt_decided` is malformed in the same way.** (Sound.)

- **Evidence.** `⊢ ⌜l[k]? = some e → ¬ e.isConfChange⌝ → confAt γ (k + 1) m` has `e` free.
  - Choose any `e ≠ l[k]`, or any `k ≥ l.length` (where `l[k]? = none`): the pure premise holds vacuously and the
    law yields `confAt γ (k+1) m`.
  - At a conf entry later decided `.apply` (so `m' ≠ m`), `confAt_agree` then derives `False`.

  `confAt_decided` puts its premise in the same place. It is probably true, because `confDecided` already implies a
  committed conf entry, but it has the same shape.
- **Restatement.**

  ```lean
  theorem confAt_normal : l[k]? = some e → ¬ e.isConfChange →
      isCommittedLogLb γ l ∗ confAt γ k m ⊢ confAt γ (k + 1) m
  theorem confAt_decided : l[k]? = some e → e.isConfChange →
      isCommittedLogLb γ l ∗ confAt γ k m ∗ confDecided γ k d ⊢ ∃ m', ⌜d.step m = some m'⌝ ∗ confAt γ (k + 1) m'
  ```

  Optionally add `confAt_committed : confAt γ k m ⊢ ∃ l, isCommittedLogLb γ l ∗ ⌜k ≤ l.length⌝`, the invariant that
  makes this safe.
- **Affects**: every client that walks `confAt` past normal entries (kvreconf, kv, the server), and
  `committed_confAt`.

### Tier 2

**L3 [spec + obligation]. Say the empty-V2 case on the bytes, not on the change.** (Sound, and every premise has a
source.)

- **Evidence.**
  - `MarshalsConfChange (some (.v2 m)) bs` is `ccDecodeV2 bs = some m` (`CCModel.lean:240-243`).
  - `ccDecodeV2_nil` gives `[] ↦ empty`, but not the converse. Nothing says that marshaling `&ConfChangeV2{}`
    (kvreconf, `reconf.go:40`) gives `[]`.
  - "`ProposeConfChange` of an empty `ConfChangeV2` takes no update", read as a case split on `o`, therefore needs
    raft's proof to show `bs = []`, and it cannot. Without that it cannot show the entry is dropped by `opsOf`, and
    it would owe an ops update it was never given.
  - The converse direction is fine: by the axiom, `o ≠ empty` forces `bs ≠ []`.
  - The same goes for `msgCredits_intro`, which asks an update for every `MsgProp` entry, those `opsOf` drops
    included (fillers, empty V2s). That is not false, since an atomic update need not fire, but it is an unneeded
    premise.
- **Restatement.** Keep one update and put the case inside it, where raft's proof knows `bs`:
  - `AU <{ ∃∃ ops, ownCommittedOps γ ops }> … <{ ∀∀ t bs, ⌜MarshalsConfChange (some o) bs⌝ ∗ ownCommittedOps γ (ops ++ opsOf [⟨t, confChangeEntryType (some o), bs⟩]), COMM True }>`;
  - in `msgCredits_intro`, `[∗list] e ∈ opsOf st.ents`.

  A client that proposes a leave builds a trivial update.
- **Obligation.** The protocol's notion of an untracked entry must grow from type-0 fillers (`Filler`,
  `Ghost.lean:1022`; `ccPropArg`, `ApiVocab.txt:42`; `cc_propose_ghost`, `RawNode__ProposeConfChange.lean:91`) to
  include empty V2s. The feasibility study examined only the folds, not this registry, so this is unverified. It
  looks pure and local.

**L4 [spec]. Bootstrap decisions, and the token family.** (Every premise has a source; no unneeded premise; law
coverage.)

1. **The bootstrap change is not named.** "`.apply (the k-th AddNode)`" leaves the change open. kvreconf calls
   `ApplyConfChange` on each bootstrap entry with the change it unmarshals (`kv.go:455-460`). To meet
   `applyChange o m = applyChange o' m` it needs `o'` to be `BootLog`'s change. Write
   `confDecided γ k (.apply (.v1 ⟨W32 0, ps[k], ctxs[k], W64 0⟩))` (`NodeApiVocab.txt:22-33`).
2. **`confAt` is given only at `boot.length`.** Also give `confAt γ k c0` for every `k ≤ boot.length` (or say it
   follows from `nodeConfig_confAt` at `⟨0, c0⟩` and the no-op decisions). A founder starts at `nodeConfig ⟨0, c0⟩`
   and applies the bootstrap entries itself (`bootstrap.go`: "We do not set raftLog.applied").
3. **`positionsFrom γ := {k | boot.length ≤ k < 2^61}` has three problems:**
   - it names a `γ.boot` the API does not export;
   - it forces a cluster without `readyFits` (kv) to prove `k < 2^61` before taking a token (kv can, from
     `maxIndex = 1 << 61`, `kv.go:116`, and `fits`, but it is a bound no client needs);
   - it is a big finite set.

   Prefer an unbounded family: `confDecideToks γ k0` with
   `confDecideToks_split : confDecideToks γ k ⊢ confDecideTok γ k ∗ confDecideToks γ (k + 1)`.
4. **Laws to list**: `Timeless` for the token (it lives in clients' invariants), `confDecideTok_excl`, and the
   persistence/timelessness instances of `confAt` and `confDecided`.

**L5 [preference: one general spec, special cases as instances; caller burden]. Provide the policy invariant
once.**

- **Evidence.** Each of the three clients decides by a pure function:
  - kv: `.apply` of `RemoveMember`'s V1 change (`Defs.lean:264-280`);
  - kvreconf: `validated`;
  - the server: its checks, as today's `srvDec` (`InvCfgView.lean:11-14`).

  Each would write the same invariant over the tokens (token, or decided as `f`), with the same fire-or-read proof
  at its apply call.
- **Restatement.** A client-side module, layered on the API and outside its kernel, e.g. `ConfPolicy.lean`:
  - `confPolicy γ f`, persistent, for `f : List LogEntry → Membership → LogEntry → ConfDecision` with
    `∀ pre m e, m.Valid → ∃ m', (f pre m e).step m = some m'`;
  - `confPolicy_alloc : confDecideToks γ k0 ={E}=∗ confPolicy γ f`;
  - `confPolicy_decided : confPolicy γ f ∗ isCommittedLogLb γ l ∗ confAt γ k m ⊢ ⌜l[k]? = some e⌝ ={E}=∗ confDecided γ k (f (l.take k) m e)`.

  This restores the rule as an instance without putting it back in the API, as the user decided. kvreconf and kv
  each cost one line at the apply call.

### Tier 3

**L6 [spec]. Rule mentions that §13.3 forgot.**
- §0, U5: "`RaftLeave`, for `opsOf`" should become L1's law. U6m: "the protocol's decoder" should become "the
  recorded decisions".
- §1: the docstrings of `ConfRule` and `fold_total` ("Decoding is the rule's business") go with the vocabulary.
- §2: `cluster_alloc`'s `rule.Ok →` premise (§13.3 drops `rule`; say the premise goes too).
- §2: `snapshotCert_made`. Say that `confAt` replaces only the fold conjunct, and that `l.length = …`, the term,
  `snapMade` and `k.al = m.autoLeave` stay.
- §4b, first bullet: "a rule keeps results `Valid`: `ConfRule.Ok`" and "its answer is `ConfRule.validated`'s"
  should become "its answer is whether `(.apply o).step m` is `some`".
- §5, the `validConf` bullet: "so the answer is the rule's". The same stale wording is in Go, at
  `examples/kvreconf/kv.go:239-241`. The check is still needed, since `confDecide` requires `Valid`, which includes
  `< 2^62`.
- §6, first bullet ("`γ.rule` … a deliberate departure from TaDa") is now reversed. Record the TaDa decision in its
  place. Keep its `shouldApplyV3` restriction: with `shouldApplyV3 = false`, a validated change never reaches raft
  (`server.go:2044-2052`), and no recorded decision matches.

**L7 [spec text]. etcd's burden is overstated (uncertain).**
- The server's proof allocates the cluster itself (`NewServerAlloc.lean:216`), and its apply thread is the only
  applier. It can therefore own the tokens outright and fire the decision `applyConfChange` computes, before either
  `s.r.ApplyConfChange` call (`server.go:2036`, `:2052`). It needs no "deterministic over its replicated membership
  store" invariant. This is the main gain of the TaDa design for the server, so §13.3 should say so.
- If a multi-server proof is planned, determinism is needed there, and L5's layer provides it.
- Still an obligation either way: etcd's checks must imply that confchange accepts the change. This is the
  existing scope of `issues/raft-remove-last-voter-panic.md` (`StrictReconfigCheck`).

**L8 [spec text].**
- **The `ApplyConfChange` explanation.** "The change passed may differ … etcd zeroes `NodeID` for a rejection,
  which the decision records as that change" gives a case where they do not differ: etcd passes the recorded,
  zeroed change. kvreconf also passes its decoded change. Give the real reason: a decider that records one form,
  V2 for instance, while the applier passes another.
- **A garbled sentence in §13.2.** "a client may also fire one ahead of commit only once the entry is committed"
  should probably read "ahead of its application, once the entry is committed".
- **A decidability instance.** `opsOf`'s filter needs a decidability instance for `isEmptyV2`.

**L9 [preference: know the margin].** A client's explicit `ConfChangeV2{}` is no longer an operation, so no client
can learn from `ownCommittedOps` that its leave was committed. None of the three needs this: kvreconf never waits
(`reconf.go:85-92`), and kv and etcd never propose V2. Record it in §6 as a margin.

## Answers to the brief's questions

- **Is the decision design right, and is it TaDa?** Yes. The tokens are one-shot per position, and a committed
  entry is unique per position. They are client-owned. Every policy is a client invariant, the out-of-band random
  one included.
- **Is it usable by each client?**

  | Client | Who fires | Where, in the apply path | Notes |
  |---|---|---|---|
  | kvreconf | the first replica to apply position `k` | after `validConf`, before `ApplyConfChange` or the skip (`kv.go:484-488`); later replicas read the decision | works with concurrent appliers |
  | etcd | its apply thread | inside `applyConfChange`, before either `ApplyConfChange` (L7) | blocked on L1 until the law is added |
  | kv | its replicas, from an invariant | at the V1 apply (`kv.go:280-283`) | needs L1 to avoid deciding V2s it never proposes |
  | raft's automatic leaves | the client | wherever it decides the position | applying is allowed exactly at joint configurations; skipping is safe for Go |
- **Is anything false of Go or unprovable from the protocol?**
  - L2 is false as written.
  - L3 is unprovable as phrased.
  - L1's law is true of Go (`raft.go:1344-1361`, `:742`) but missing.
  - The protocol side is plausible. I spot-checked `fold_adjacent`, `CCDecision.step`, `dynEnv`, `RInv.cfg` and
    `RInv_init` (which folds the boot log, so recording bootstrap decisions at allocation fits). I did not verify
    the roughly 60 `CfgAt` sites or the parameterisation of `StepR`. The `opsOf`/registry change (L3) is outside
    the feasibility study.
- **What of kvreconf's Go is still excluded?** Nothing new from §13. The candidate's scope restrictions do not touch
  it:
  - newcomers at `c0` is what kvreconf does (`cluster.go:177-178`);
  - it has no restarts and makes no durability claim;
  - its unmarshal of empty data rests on the approved `ccDecodeV2_nil`.

  Only its drivers (`cmd/`, the tests) stay outside, as before.

No bug in the verified Go code was found. kvreconf's stale comment (L6) belongs to this repository's own example,
so it goes in no `issues/` file.
