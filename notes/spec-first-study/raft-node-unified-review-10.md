# Review of the unified node-API candidate 10, round 10

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-7.md`, titled "candidate 10", one
  text. It is a design and nothing of it is implemented, so no finding can be stale against `HEAD` (`bbc7ce9e61`).
- **Compared with**: today's API at `eb59bb8d1b`:
  - `interface/Proof/go_etcd_io/raft/v3/{InvNode,ApiVocab,NodeApiVocab,InvMemstorage,MemstorageAU}.txt`;
  - `interface/Spec/go_etcd_io/raft/v3/{MemoryStorage__*,node__Advance,node__ApplyConfChange,node__ProposeConfChange}.txt`;
  - `etc/api/raft.txt`;
  - `Proof/go_etcd_io/raft/v3/{InvStorage,InvApiDyn,Protocol/CfgOverlap}.lean`;
  - `Spec/go_etcd_io/raft/v3/MemoryStorage__SetHardState.lean`.
  - Also `notes/raft-unified-plan.md` in the worktree, and `issues/raft-committedentries-stable-storage-doc.md`.
- **Go**:
  - raft a2 (`.lake/raft-fork`, `565c2bd`): `storage.go`, `node.go`, `confchange/{confchange,restore}.go`;
  - kvreconf (`examples/kvreconf/{kv,cluster,reconf}.go`);
  - etcd's server (`~/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261027220749-a20f6760ff43/etcdserver/server.go`).
- **Clients' proofs**: the server's `SnapTake.lean`, `InvRaftNode.lean:363-371`, `InvRaftLoop.lean:61`, `EtcdServer__run.lean:69`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md` (the worktree has no `spec/` skill).
- **Not run**: lake build, lean-check, Go tests.

Each finding is marked **[spec]** (a defect of the specification) or **[obligation]** (a proof obligation),
and says whether §0 or `notes/raft-unified-plan.md` carries it.

## Summary

Candidate 10 fixes H1's soundness hole: `CreateSnapshot` is now bounded by a storage-side witness, `storHoldsLb`,
which the append receipt and `Advance` supply. It also fixes H3 (in the plan), H4, H5 and H7. H2 and H6 are only
partly fixed, and both of H2's repairs leave a false statement behind.

- **§1/§4b (J1).** H2's fix took the `2^62` cut out of `applyChange` and the "a voter" clause out of the
  well-formedness that §4b's specs assume. The definitions built on them did not follow:
  - `ConfRule.Ok` and `clamp` still only require `isSome`, so `applyChange_valid`, `fold_total` and
    `committed_fold` are false at the size bound.
  - `Membership.WellFormed` admits memberships on which `confchange.Restore` errors, so `Restore.apiSpec`'s
    `err = nil` is false of Go.
- **§4 (J2).** The written-out `CreateSnapshot` triple does not tie `err` to the branch the update took. kvreconf,
  the sole writer, therefore cannot rule out `ErrSnapOutOfDate`, nor the panic it turns that into
  (`kv.go:378-379`).

**Tier 1 (2)**: J1, J2. **Tier 2 (2)**: J3, J4. **Tier 3 (5)**: J5-J9.
**Go defects**: none new. The server's `nil` `ConfState` path (J3) cannot happen in the real server (the scheduler
stops before raft), so it is not filed. H7 is filed (`issues/raft-committedentries-stable-storage-doc.md`).

---

## Review 9's findings: fixed?

| review 9 | candidate 10 | status |
|---|---|---|
| H1 `CreateSnapshot` over the delivered log unsound; term has no source | persistent `storHoldsLb` from the append and from `Advance`; triple written out; term fixed in the post; `oc = some cs` | **Fixed in substance.** The sole writer's case is broken by how the triple is written (J2). `storHoldsLb`'s home, its law's receipt and its persistence against `ApplySnapshot` are not stated (J4) |
| H2(a) the iff false at `2^62` | `applyChange` is Go's; the cut moved into `Valid` | **Not fixed**: `Ok`/`clamp`/`applyChange_valid`/`fold_total` still assume the cut (J1) |
| H2(b) `Valid`-only shuts out `validConf(nil, …)` | `WellFormed` = `confchange`'s invariants without "a voter" | **Partly**: the empty membership is now covered, but so are memberships `Restore` rejects (J1(c)) |
| H2(c) no shape for the assembled tracker | `ownCfgPairM`, `ownTrackerM_assemble` | **Fixed**, with a wording problem: a value update, not "the same `trk`" (J8) |
| H3 server re-certification | plan U10 | **Fixed** (plan). §0 lists prerequisites only, so leaving it out of §0 is right. The `nil` `ConfState` case U10 mentions still has no way out (J3) |
| H4 `stepIn_intro`'s `MsgSnap` premise | in `SentMsgShape` | **Fixed** (spec). The source of the bound in a cluster with no bootstrap log is not given (J6) |
| H5 plan text | "The spec" and U8 rewritten | **Fixed**. U11 does not name `ownCfgPairM` (J8) |
| H6 nits | header claims fixed | **Partly**: line 17 still says "Reviews: …-{1..7}", "(F9)" is still in §1, §0 still cites a missing `notes/decisions.md` entry, and the `Step`/`Propose` nits remain (J9) |
| H7 doc issue | filed | **Fixed**: `issues/raft-committedentries-stable-storage-doc.md`, `upstream: unchecked` |

---

## Findings, ranked

### Tier 1

#### J1. [spec; U1/U11 in the plan, not the definitions] H2's fix leaves `Ok`, `clamp`, `applyChange_valid`, `fold_total` and `WellFormed` false

**Principles**: *Sound* (a law must be true); *the vocabulary is part of the spec*.

**Evidence (a): the size cut is gone from `applyChange` but still assumed by the laws.**
- §4b (lines 320-322) says `Membership.applyChange` is Go's `confchange`, with "no `2^62` cut; the cut is in
  `Valid`, and a rule must keep results `Valid`: `ConfRule.Ok`".
- But §1's `ConfRule.Ok` (line 88) asks only `(applyChange o m).isSome`, and `clamp` (line 89) filters on `isSome`.
- Go's `confchange` has no size check (`confchange.go:150-171`: `apply` checks only for a zero `NodeId` and for no
  voters left).
- Today's `applyChange_valid` (`InvNode.txt:323`), which §1 keeps ("Laws of `Membership`"), says
  `m.Valid → applyChange o m = some m' → m'.Valid`. With Go's `applyChange` it is false: a `ConfChangeIM` whose
  `Changes` add `2^62` fresh nonzero ids gives a `some` result that is not `Valid`.
- `fold_total` (`r.Ok → c0.Valid → … m.Valid`) and `committed_fold` (`… m.Valid`) are false for the same rule.
- The protocol does need the cut. `ccApplyM_overlap` takes `GMap.size s'.cfg.ids < 2 ^ 62`
  (`Protocol/CfgOverlap.lean`, above `ccStepB`), and `memApply` is `ccStepB` (`InvApiDyn.lean`).

**Evidence (b): reading `Ok` as the prose moves the problem to kvreconf.**
- If `Ok` means "results `Valid`" and `clamp` filters on that, then `ConfRule.validated` rejects exactly what Go's
  `confchange` accepts past `2^62`.
- kvreconf's `applyConf` calls `ApplyConfChange` once `validConf` is `true` (`kv.go:466-470`). The spec's premise
  `γ.rule (l.take v.applied) v.membership e = some o'` then needs `m'.ids.size < 2^62`.
- The API gives no source for that:
  - `ccDecode` is opaque;
  - conf proposals are not registered (`sentMsg_prop` gives only `ConfEntryDecodes`), so the client cannot know
    that every committed conf entry is one of its own small `randomChange`s.
- In practice the case cannot happen (`2^62` distinct nonzero ids need more than `2^63` bytes of data), but the
  proof cannot see that.

**Evidence (c): `WellFormed` is too weak for `Restore`.**
- "`confchange`'s invariants without 'a voter'" admits a membership with no incoming voter but some learners, or
  a joint one with an empty incoming half.
- `Restore` turns its `ConfState` into `Simple`/`EnterJoint` steps (`restore.go`, `toConfChangeSingle`, `chain`).
  `apply` then fails with "removed all voters" (`confchange.go:170-171`).
- So `Restore.apiSpec`'s `err = nil` is false of Go there.
- Only the fully empty `ConfState` works: no ops, so `chain` returns the fresh tracker's config and `nil`.
- §1's laws paragraph (lines 118-120) also still states `Restore` over `m.Valid`. That is a second, different
  version of §4b's spec.

**Callers**: every client of `committed_fold`/`nodeConfig_fold`/`fold_total` (kv, the server, kvreconf), and
kvreconf's `validConf` (`kv.go:219-240`) and `applyConf` (`kv.go:461-472`).

**Restatement**:
- `ConfRule.Ok r := ∀ pre m e o, m.Valid → r pre m e = some o → ∃ m', applyChange o m = some m' ∧ m'.Valid`.
- `clamp` filters on the same condition.
- `applyChange_valid : m.Valid → applyChange o m = some m' → m'.ids.size < 2^62 → m'.Valid`.
- `Membership.WellFormed m := m = ⟨∅,∅,∅,∅,false⟩ ∨ (Valid but for the size bound)`.
- Delete §1's old `Restore`/`Changer` paragraph in favour of §4b's.
- Make kvreconf match the rule in Go (a §5 change). `validConf` keeps the `prs` the `Changer` returns and also
  rejects when `len(prs) ≥ 1<<62`, or simply when it exceeds `maxReplicas`. A law `ownCfgPairM_len : ownCfgPairM
  cfg prs m ⊢ ⌜len prs = m.ids.size⌝` (over the map's `len` spec) lets kvreconf prove `validConf = true ↔
  ConfRule.validated … = some o`.
- The alternative is an axiom bounding `ccDecode`'s changes by the data's length. It is weaker, since a bound of
  `< 2^63` changes is not `< 2^62` ids, and it adds to the trust base.

#### J2. [spec; U8] `CreateSnapshot`'s post does not say which outcome goes with which branch

**Principles**: *Complete* (the post says what the caller inspects); *Linearizability is the caller's atomic
update, written in the triple*.

**Evidence**:
- §4's triple (lines 295-303) has the update `<{ ∃∃ si, memSnapTok st si }> <{ memSnapTok st (if si < i then i else
  si), COMM Q }>`, and a post of `Q ∗ (⌜err = nil⌝ ∗ ownSnapS … ∨ ⌜err = ErrSnapOutOfDate⌝)`.
- Nothing links the disjunct to `si`. Even with `Q` indexed by `si`, a sole writer that knows `si < i` cannot
  rule out `err = ErrSnapOutOfDate`.
- Go decides by `i <= ss.index` (`storage.go:245-247`), and today's spec gives one continuation per branch
  (`MemoryStorage__CreateSnapshot.txt`: `⌜i ≤ ss.index⌝ -∗ … Φ (null, eood)` and `∀ t, ⌜ss.index < i⌝ -∗ … Φ (snap',
  nil)`). The remark under the triple, "`si < i` decides the branch inside the update", is the intent, but the
  statement does not carry it.

**Smaller gaps in the same triple**:
- `memSnapTok st si` is not today's token `memSnapTokG γs σt`, over which `Compact`, `ApplySnapshot` and the
  server's shared invariant (`srvStorTokN`, `SnapTake.lean:139`) are written. The post state should be
  `memStorCreated σt i t (some cs) data`, not only the new index.
- The masks (`@ ⊤ \ ↑memSnapN, ∅`) and `memKey γs.ak` are missing.
- Dropping today's `σt.prev.index ≤ i` is right: `memCutInv` keeps `prev.index ≤ ss.index` (`InvMemstorage.txt`,
  `%Hcok`).

**Caller**: kvreconf's `maybeSnapshot` (`kv.go:378-379`, `panic` on any error). The server's call is fine either
way (it returns on `ErrSnapOutOfDate`, `server.go:2133-2137`).

**Restatement**: write the triple as today's, changing only three things:
- `memFloorTok` is replaced by `storHoldsLb st l`, with `uint.nat i = l.length` and `0 < l.length`;
- `oc = some cs`, with the certificate in the precondition;
- `t := (l.getLast).term` in place of `∀ t`.

```
AU <{ ∃∃ σt, memSnapTokG γs σt }> @ ⊤ \ ↑memSnapN, ∅
   <{ memSnapTokG γs (if uint.Z σt.ss.index' < uint.Z i then memStorCreated σt i t (some cs) data else σt),
      COMM (⌜uint.Z σt.ss.index' < uint.Z i⌝ -∗ ∀ snap, ownSnapS snap _ ⟨⟨t, i⟩, cs, data⟩ -∗ Q snap nil) ∧
           (⌜uint.Z i ≤ uint.Z σt.ss.index'⌝ -∗ Q null ErrSnapOutOfDate) }>
```

The two continuations make the error branch impossible for a writer that knows `ss.index < i`.
`spec_tok_of` is then re-derived as today.

### Tier 2

#### J3. [obligation; plan U10 mentions the `nil` but not the way out] The server reaches `CreateSnapshot(…, nil, nil)` after a stopped `ApplyConfChange`, and the API cannot exclude it

**Principles**: *Complete* (every caller); *an exclusive resource the code needs is covered by a token*.

**Evidence**:
- `ep.confState = s.r.ApplyConfChange(cc)` (`server.go:2052`) is `nil` when the node stopped before taking the
  change (`node.go:562-573`).
- The candidate's stopped disjunct is sound. If the run loop received `cc`, it blocks on `confstatec` until the
  caller reads it, and `n.done` is closed only by the loop itself (`node.go:430-431`, `450`).
- `applyAll` still goes on:
  - it waits on `notifyc`, which the raft goroutine sends independently of the node;
  - it waits on `raftAdvancedC`, since `Advance` returns unit when stopped;
  - it then reaches `snapshot`, which calls `CreateSnapshot(ep.appliedi, ep.confState, nil)` (`server.go:995-1006`,
    `2131`).
- The candidate's triple rightly takes `oc = some cs`. With `nil` the snapshot gets the storage's previous
  `ConfState`, which no API law can certify at `appliedi`.
- In the real server the case cannot happen: `run`'s deferred shutdown stops the scheduler, then waits for the
  wait group, and only then stops raft (`server.go:823-830`).
- The API gives no resource to show that. `Stop.spec` is `isNode → nodeStopped` (persistent), and anyone holding
  `isNode` may call it.

**Restatement**: decide this in U10. Either:
- (a) a one-line change in the fork, in `snapshot`: `if ep.confState == nil { return }`, as kvreconf's
  `maybeSnapshot` already does (`kv.go:371`). This is the cheaper fix and needs no API change; or
- (b) an exclusive `stopRight n` from `StartNode`/`RestartNode` that `Stop` consumes, with `stopRight n ∗
  nodeStopped n ⊢ False`. That threads a resource through every client only to exclude a path.

Uncertain: whether `raftNode.start` can stop the node on another path (an error exit) before `s.r.stop()`. I did
not trace it.

#### J4. [spec + obligation; plan U8 names the laws, not these] `storHoldsLb`: its home, its law's receipt, and its persistence against `ApplySnapshot`

**Principles**: *every premise has a source*; *read the definitions of the resources a spec takes*.

**Evidence**:
- **Home.** `storHoldsLb (st : Storage)` is over raft's abstract storage. `appendRight_holds` is a node law over
  any `StorageModel`, so `storHoldsLb` must be a new field of `class StorageModel`, like `storFloor`
  (`InvStorage.lean:206-240`). `isStorageWith` then needs a new clause, and every instance must prove it:
  `MemstorageInstance`, kv's `KVStorageInstance`, and the kvreconf wrapper. §4 does not say this.
- **The wrong receipt.** `appendRight st es` is the right to append, given before `Append` (`readyOut none`,
  `ApiVocab.txt:19-21`). After `Append` the client holds `appendReceipt st es` (`advReceipt none`,
  `ApiVocab.txt:197-200`), and `Advance` consumes it. So the law should be over `appendReceipt` and give it back.
- **Bad arithmetic.** `storHoldsLb st.storage (st.delivered ++ ce)` has `ce` unbound. After `node.wp_readyRecv`
  the driver's `delivered` is already `st.delivered ++ ce` (`InvNode.txt:103-112`), so it should be
  `storHoldsLb st.storage st.delivered`.
- **Not a persistent statement.** The docstring's "and will while the storage's writer does not compact past
  them" describes the future. The persistent statement is: `|l| ≤ lastIndex`, and the terms agree on `[first
  index, |l|]`. It survives `Compact`, because `Compact` requires `ci ≤ ss.index` (`MemoryStorage__Compact.txt`), so
  `CreateSnapshot` at `i < ci` answers out-of-date.
- **`ApplySnapshot`.** Today's `ApplySnapshot` accepts any certified snapshot with `σ.fl ≤ index`
  (`MemoryStorage__ApplySnapshot.txt`). One with `ss.index < index < |l|` would reset `ents` to its dummy entry
  (`storage.go:231-232`) and falsify `|l| ≤ lastIndex`; `CreateSnapshot(|l|)` would then panic
  (`storage.go:250-252`).
- The U8 proof needs an invariant that rules this out: every certified snapshot past `ss.index` lies beyond every
  length a `storHoldsLb` has been given for.
  - For raft's snapshots, `readySnap`'s `st.delivered.length < l.dlv.length` gives it.
  - The client's own snapshots end at or below `ss.index`, and `ss.index` only grows.
- Plausible, but unstated and unchecked.

**Callers**: kvreconf (`kv.go:343` then `349`; `355`), kv, the server (J7).

**Restatement**: say in §4 that `storHoldsLb` is a `StorageModel` field with a new `isStorageWith` clause. State
the law as `nodeDriver n γ N st ∗ appendReceipt st.storage es ⊢ nodeDriver n γ N st ∗ appendReceipt st.storage
es ∗ storHoldsLb st.storage st.delivered` (when `st.handling = some (es, none)`). Use the persistent statement
above as the docstring. Add the `ApplySnapshot` invariant to U8.

### Tier 3

- **J5. [spec] `SetHardState` is not importable.**
  - kvreconf calls `r.storage.SetHardState(rd.HardState)` (`kv.go:341`).
  - The spec exists (`Spec/go_etcd_io/raft/v3/MemoryStorage__SetHardState.lean:31`, over `memStorMeta`), but
    `etc/api/raft.txt:47-57` does not list it, and `interface/` has no file for it.
  - kv and the server's run loop do not call it, which is why it was never needed.
  - Add it to the importable list (and `memStorMeta`'s source in `NewMemoryStorage`'s post), and name it in §4 or
    U11.
- **J6. [obligation, U7] The source of `SentMsgShape`'s `MsgSnap` bound.**
  - With a bootstrap log, the bound follows from `readyFits`.
  - Without one (kv), `isCommittedLogLb` gives only `< receiptBound`, up to `2^64-2`. The bound must then come
    from the storage:
    - `Append`'s `e0.Index + |p| ≤ 2^61` keeps every durable index, and so the committed index, below `2^61`;
    - `HSnapshot`'s `index ≤ σ.fl` keeps raft's storage snapshots below it (`InvStorage.lean:474-497`).
  - For a generic `StorageModel` this is uncertain.
  - U7 says "`SentMsgShape` in every cluster" without naming the bound. Add it.
- **J7. [obligation, U10] Clients' storage witness.**
  - The server gets its snapshot right today as `memFloorAtLeast` over `raftAdvancedC` (`InvRaftLoop.lean:61`,
    `EtcdServer__run.lean:69`, `InvRaftNode.lean:365-367`). It must now carry `storHoldsLb` from `Advance`'s post
    through the same channel.
  - That works because the fork's `applyAll` snapshots only after `raftAdvancedC` (`server.go:997-1006`).
  - kv likewise.
  - U10 says "re-certifies its snapshots" but not this. Add a line.
- **J8. [spec] `ownTrackerM_assemble` as a value update.**
  - `MakeProgressTracker` returns a `ProgressTracker` value, and `trk.Config = cfg; trk.Progress = prs` writes the
    fields of a local variable (`kv.go:226-228`).
  - The law should be `ownTrackerM trk none ∗ ownCfgPairM cfg prs m ⊢ ownTrackerM {trk with Config := cfg,
    Progress := prs} (some m)`, a pure record update, not "the same `trk` after the field writes' specs".
  - `Changer{Tracker: trk, LastIndex: 1}` then carries it.
  - U11 should name `ownCfgPairM` and the law (H5 residual).
- **J9. [spec, nits]**
  - Line 17 still says "Reviews: …-{1..7}" (H6 says it was fixed), and §1's "(F9)" label remains.
  - §0's U4 cites a `notes/decisions.md` entry that does not exist yet; grep of the worktree's file, uncommitted
    edits included, finds none. §6 says the entry is to be written, so §0 should say "(§6, to be recorded)".
  - The stopped `Step` should say that a `nil` message is excluded by the argument's ownership.
  - `Propose` with `data = []` is a filler whose update never fires (`opsOf`). It is harmless but unstated.
  - `appendRight_holds`'s name should follow its receipt (J4).

## What is good

- **H1's repair is the right shape.**
  - The bound is in the storage's vocabulary, persistent, with two sources the clients already pass through:
    the append (`kv.go:343`) and `Advance`.
  - The sole writer's token and the server's two-writer atomic spec are kept.
  - The term is fixed in the post, so `snapshotCert_make`'s one-term certificate is enough. Today's "every term"
    registry (`SnapTake.lean`) goes away.
  - It handles the synchronous mode's committed-but-unappended entries (H7), which is exactly the case
    `server.go:991-995` documents.
- **`oc = some cs`** is right. It matches raft's own documentation (`storage.go:240-242`: "the result of the last
  `ApplyConfChange` must be passed in"). kvreconf already skips a `nil` `cs` (`kv.go:371`).
- **The stopped `ApplyConfChange` disjunct is sound**: `nil` implies the change was not taken (J3's evidence).
- **§4b now covers `validConf`'s path end to end**: the fresh tracker, `Restore` of a `nil` `ConfState` as the
  empty membership (correct: `restore.go`'s `chain` with no ops), the assembled pair, and `Changer` specs that
  are an iff by definition once `applyChange` is Go's.
- **`SentMsgShape` absorbs the `MsgSnap` bound**, so `stepIn_intro` is premise-free except for the target id. kv's
  Go check becomes unneeded for the proof.
- **The plan reads as the candidate does** (H5), and H7 is filed with a reproduction path.
- **Unchanged and still right**:
  - one parameterless `isCluster`, with `γ.c0` and `γ.rule`;
  - `RaftLeave`/`opsOf`, with the trust-base axiom's reach stated;
  - the TaDa `ownSnapsMade`/`ownProposals`;
  - no credits;
  - one triple per function with the stopped case as a case split on the input.

## kvreconf's Go still excluded

| behaviour | where | excluded by | kind |
|---|---|---|---|
| `CreateSnapshot`'s `panic` on error | `kv.go:378-379` | J2 (the post cannot rule out `ErrSnapOutOfDate`) | spec |
| `validConf` at the `2^62` boundary; `ApplyConfChange` after it | `kv.go:219-240`, `466-470` | J1(a)(b) | spec + §5 Go change |
| `SetHardState` | `kv.go:341` | J5 (not importable) | spec (API list) |
| a newcomer's `Storage` with `c0`'s `ConfState`; `Replica.cs` starting at it | `kv.go:244-254`, `cluster.go:174-175` | §5's Go change (not made); scope restriction in §6 | Go change |
| unmarshalling raft's automatic leave | `kv.go:443-447` | the axiom's approval (§0) | trust base |
| a joiner at `c0`; pre-votes at term 0 | `cluster.go:163-176` | U4 (§0, plan) | obligation |
| `ApplyConfChange` after a rejected entry; a snapshot pending | `kv.go:461-472` | U6m, U0/U3 (§0, plan) | obligation |
| raft's automatic leave | `raft.go:742-760` | U5 (§0, plan) | obligation |
| a forwarded `MsgTransferLeader` (also `From = To`); `MsgTimeoutNow` | `reconf.go:104` | U7 (§0, plan) | obligation |
| `storHoldsLb` after the append and after `Advance` | `kv.go:343`, `349`, `355` | J4 (a statement and an obligation, not an exclusion) | spec + U8 |

**Not excluded** (checked):
- `validConf(nil, …)` after a stopped `ApplyConfChange`: `WellFormed` covers the empty membership.
- `maybeCompact` (`kv.go:390-404`): `ci ≤ min(snapIndex, r.index)`, which is at most `ss.index` and the floor.
- Duplicated and delayed messages (`cluster.go:259-268`): `msgCredits_intro` per copy, `proto.Clone` before the
  first `Step`.
- `Status().Lead`, `TransferLeadership`, `Campaign`, `ForgetLeader` (`reconf.go:104-108`);
  `ReportSnapshot`/`ReportUnreachable` (`cluster.go:277-302`).
- The `Snapshot` wrapper's `ErrSnapshotTemporarilyUnavailable` (the wrapper law).

## Ranking (most in need of revision first)

1. **§1/§4b's vocabulary** (J1): `Ok`, `clamp`, `applyChange_valid` and `WellFormed` made consistent with Go's
   `applyChange`, plus kvreconf's size check. Each fix is a line, but as written the laws are false.
2. **§4's `CreateSnapshot` triple** (J2, J4): restore today's per-branch continuations; place `storHoldsLb` in
   `StorageModel`; correct its law; add the `ApplySnapshot` invariant to U8.
3. **The server's `nil` `ConfState`** (J3): a one-line fork change, recorded in U10.
4. **Records** (J5-J9): `SetHardState` importable, U7's and U10's missing lines, the assembly law's wording, and
   nits.

## Uncertain

1. J4: that raft's invariants give "every certified snapshot past `ss.index` is past every `storHoldsLb` length"
   (checked only against `readySnap` and the out-of-date check).
2. J3: whether `raftNode.start` can stop the node before `s.r.stop()` by another path.
3. J6: the `MsgSnap` bound for a generic `StorageModel` without a bootstrap log.
4. J1: whether the user prefers kvreconf's Go size check or a decode-size axiom. I recommend the former.
