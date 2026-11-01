# Review of the unified node-API candidate 8, round 8

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-7.md` (titled "candidate 8"), one
  text. It is a design, not implemented, so no finding can be stale against `HEAD` (`ee72b456ca`).
- **Compared with**: today's API at `eb59bb8d1b` (`interface/Proof/go_etcd_io/raft/v3/{InvNode,NodeApiVocab,
  ApiVocab,InvStorage}.txt`, `interface/Spec/go_etcd_io/raft/v3/{MemoryStorage__*,node__Propose,
  node__ProposeConfChange}.txt`, `etc/api/raft.txt`); `InvNode.lean`, `InvApi.lean`, `Protocol/GhostState.lean`
  at `eb59bb8d1b`; `notes/raft-unified-plan.md` at `HEAD`.
- **Go**: raft a2 (`.lake/raft-fork`, `565c2bd`): `storage.go`, `node.go`, `raft.go`, `raftpb/confchange.go`;
  kvreconf (`examples/kvreconf/{kv,cluster}.go`); kv (`examples/kv/kv.go`); etcd's server
  (`~/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261027220749-a20f6760ff43/etcdserver/{raft,server}.go`).
- **Clients' proofs**: kv (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/{Adequacy,KV__run,Cluster,
  deliverable}.lean`), the server (`etcdserver/{SnapTake,EtcdServer__compactRaftLog}.lean`), at `eb59bb8d1b`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md` (the worktree has no `spec/` skill).
- **Not run**: lake build, lean-check, Go tests.

Each finding is marked **[spec]** (a defect of the specification) or **[obligation]** (a proof obligation;
whether the candidate's §0 or `notes/raft-unified-plan.md` carries it).

## Summary

Candidate 8 fixes review 7's F2, F4, F7, F8, F9, F11 and F13. It fixes F1 at the cost of a new premise for kv,
and one law in it is off by one. It carries F6 and F12 in the plan. F5, F10 and F14 are partly fixed.
**F3 is not fixed**: `storAppended` was replaced, but the replacement fails in two ways:
- `storCommittedAt_of` is false as stated, and no client can use it for an entry committed in a later `Ready`
  than the one it was appended in, which is the usual case;
- the exclusive, non-atomic `storWriter` with no `ErrSnapOutOfDate` case shuts out etcd's server. The server's
  storage has two writer goroutines and handles `ErrSnapOutOfDate`, and its proof uses today's atomic specs.

**Tier 1 (3)**: G1, G2, G3. **Tier 2 (3)**: G4, G5, G6. **Tier 3 (7)**: G7-G13.
**Go defects**: none new; nothing to file in `issues/`.

---

## Review 7's findings: fixed?

| review 7 | candidate 8 | status |
|---|---|---|
| F1 `isCommittedLogLb_length` false at `boot = []` | `receiptBound + boot.length ≤ 2^61` for every cluster; `readyFits` always; the law over `readyFits` | **Fixed, but the law is off by one** (G3), and kv now pays a premise it did not need (G6) |
| F2 `clamp_eq` false | pointwise, under `m.Valid` | **Fixed** (true: `Ok` at a valid `m` makes the filter keep every `some`) |
| F3 `storAppended` | `storWriter` (exclusive) + `storCommittedAt` (persistent) | **Not fixed** (G1, G2) |
| F4 Go change to `applyEntry` | dropped; `kv.go:437-447` unmarshals as today | **Fixed**. §0 still does not say that the axiom reaches every result over raft (G12) |
| F5 newcomers at `c0` | a scope restriction in §0 U4 and plan U4 | **Partly**: the `notes/decisions.md` entry §0 cites does not exist, and §6 does not list it (G9) |
| F6 plan | U4, U5, U6m, U7, U8 updated | **Fixed**, except U11 (G11) |
| F7 `stepIn_intro` shape premise | dropped | **Fixed**. Its `MsgSnap` premise is now derivable too (G8) |
| F8 `sentMsg_noTransfer` | excludes `MsgTransferLeader` | **Fixed** |
| F9 `bootedCluster` | removed with `nodeBoot_booted` | **Fixed** (§1 labels the `Membership` laws "(F9)" by mistake) |
| F10 `fold_total`'s premise | explained | **Partly**: the explanation ("a rule decides from the decoded change") contradicts `ConfRule`'s type, which takes the entry; `fold_snoc_conf` is still not written out (G10) |
| F11 stopped `Step` | `nil` for a local type from a non-local sender, else `ErrStopped`/`ctx.Err()` | **Fixed** (matches `node.go:474-485`, `513-521`; a `nil` `m` is excluded by the message's ownership: say so) |
| F12 U6m | one mechanism, no reject step | **Fixed in §0 and the plan**. `nodeConfig_reject` is still `|==>` (G10) |
| F13 stopped specs | one triple, `P ∨ nodeStopped` | **Fixed** |
| F14 `SnapListsOk` | `cs.NoDupLists` | **Partly**: `cs.NoDupLists` is derivable as well (G7) |

---

## Findings, ranked

### Tier 1

#### G1. [spec] `storCommittedAt_of` is false as stated, and unusable where clients need it (F3 not fixed)

**Principles**: *Sound*; *Complete*; *every premise has a source the client sees*.

**Evidence: unsound.** The law is `appendReceipt st es ∗ isCommittedLogLb γ l ⊢ ∀ e ∈ es, ⌜e.Index ≤ l.length⌝ →
storCommittedAt st e.Index' e.Term'`, and `storCommittedAt` is documented as "a committed entry … term `t` at
index `i`". Nothing ties `l` to the time of the append. A counterexample:
1. A follower appends `es` and holds `appendReceipt es` until `Advance`.
2. Meanwhile `node.run` keeps stepping `recvc` (`node.go`, `run`'s select). A new leader's `MsgApp` truncates
   those in-progress entries, and a quorum without this node commits a different entry at index `i`.
3. The client takes `isCommittedLogLb γ l` of that log. It can: `ownCommittedOps_get_lb` gives the current
   committed log to any client whose invariant holds `ownCommittedOps`, as kvreconf's will.
4. The law then gives `storCommittedAt st i t_old`, a false claim that `t_old` is committed at `i`.

**Evidence: it consumes the receipt.** The law takes `appendReceipt` and does not give it back, but
`Advance.spec` needs it (`advReceipt st.storage es none = appendReceipt st es`, `ApiVocab.txt:197-199`).

**Evidence: unusable.** Even fixed, the law applies only while the receipt is held: between that `Ready`'s
`Append` and its `Advance`.
- An entry appended in `Ready` k and committed in `Ready` k+1 is the common case for a follower. Its receipt is
  gone by the time it is committed.
- kvreconf's `maybeSnapshot` (`kv.go:349`, `355`, `366-379`) and kv's `CreateSnapshot` after `Advance`
  (`examples/kv/kv.go:290-295`) snapshot at the applied index. So most of their snapshots cannot get
  `storCommittedAt st i t`.

**Evidence: other premises with no source.**
- `CreateSnapshot`'s `fi ≤ i ≤ li` has no source either. No `Append`, `ApplySnapshot`, `FirstIndex`, `LastIndex`
  or `NewMemoryStorage` spec over `storWriter` is given; §4 says only "each spec giving the new view".
- `i ≤ li` is the bound `CreateSnapshot` panics on (`storage.go:250-252`). A client knows it only through a law
  tying the storage to the delivered log, which the candidate does not state.

**Evidence: what the spec takes and gives is unstated.** The resources (`memSnapRO`, `memKey`, `memCsArg`, the
data slice) and the returned snapshot's ownership (`ownSnapM snap' …` today) are still not stated, as review 7's
F3 asked.

**Callers**: kvreconf, kv.

**Restatement**: drop `storCommittedAt`. Let `CreateSnapshot` take the node's view in place of a storage-side
term fact: `deliveredLogLb n γ N l` with `l.length = uint.nat i`, together with the fact that the storage holds
the delivered log up to `i`.
- The term is then `l`'s last, which `snapshotCert_make` already uses. Raft's storage invariant gives
  "`MemoryStorage`'s entries at indices in `(si, |delivered|]` are the delivered ones once that `Ready`'s entries
  are appended" (`isStorage`/`InvStorage`: uncertain, not checked).
- Give the `Append`, `ApplySnapshot`, `FirstIndex` and `NewMemoryStorage` specs their writer-view posts.
- Write out the full triple.
- If a storage-side fact is kept, give it the premise `l[uint.nat e.Index' - 1]? = some (LogEntry.ofEntryM e)`,
  and return the receipt.

#### G2. [spec] An exclusive, non-atomic `storWriter` without `ErrSnapOutOfDate` excludes etcd's server

**Principles**: *Complete* (all callers); *faithful to concurrency*; *one general spec; special cases are
instances*.

**Evidence: the server.**
- etcd's storage has two writer goroutines. The raft loop calls `ApplySnapshot` and `Append` (`etcdserver/raft.go:287`,
  `:292`); the apply goroutine calls `CreateSnapshot` and `Compact` (`server.go:2131`, `:2179`).
- The apply goroutine cannot know `si < i`: a leader's snapshot may be applied concurrently. So it handles
  `ErrSnapOutOfDate` (`server.go:2133-2137`: "raft might have already got a newer snapshot").
- Today's server proof uses the logically atomic specs over a shared token: `CreateSnapshot.wp_reg`, and
  `Compact.wp_shared` over `srvStorTokN` (`SnapTake.lean:10-12`, `EtcdServer__compactRaftLog.lean:50-51`).
- Today's `CreateSnapshot`/`Compact` are atomic updates over `memSnapTokG γs σt` with both outcomes
  (`interface/Spec/.../MemoryStorage__CreateSnapshot.txt`, `__Compact.txt`).

**Evidence: the candidate.** It gives one spec per function, taking an exclusive `storWriter` and returning only
`nil`. An exclusive non-atomic resource cannot be shared between two goroutines, and the error branch is gone. The
server's proof cannot be redone over it.

**Callers**: etcd's server (excluded); kv and kvreconf (single writers, so fine with either).

**Restatement**:
- Keep today's logically atomic specs, both outcomes included.
- Add a sealed, exclusive writer fragment, `storSnapIdx γs si`. It agrees with the atomic state
  (`memSnapTokG γs σt ∗ storSnapIdx γs si ⊢ ⌜σt.ss.index' = si⌝`) and is updated at the linearization point of
  each call that moves the snapshot index (`ApplySnapshot`, `CreateSnapshot`). A sole writer holds it and
  refutes the `ErrSnapOutOfDate` branch by `si < i`; the server ignores it.
- That makes kvreconf's use an instance of the general spec, not a second spec.

#### G3. [spec] `isCommittedLogLb_length`'s `↑l.length + 1 < 2^61` is off by one

**Principle**: *Sound*.

**Evidence**:
- `isCommittedLogLb` gives only `l.length < receiptBound + bootLen` (`InvApi.lean:135-137` at `eb59bb8d1b`).
- With `cluster_alloc`'s `receiptBound + boot.length ≤ 2^61`, that is `l.length ≤ 2^61 - 1`, so
  `l.length + 1 ≤ 2^61`, not `< 2^61`.
- Today's law gets `< 2^64` from the separate `receiptBound ≤ 2^64 - 2` (`InvNode.lean:804-809`). Review 7
  proposed the wrong form, and the candidate copied it.

**Callers**: kv's snapshot index (`KV__run.lean:596`, `< 2^61`); `ApplySnapshot`'s and `stepIn_intro`'s
`Index < 2^61`; `Append`'s `≤ 2^61`. All need only `l.length < 2^61`.

**Restatement**: `isCommittedLogLb_length : readyFits γ N ∗ isCommittedLogLb γ l ⊢ ⌜↑l.length < 2^61⌝`.
Alternatively, take `receiptBound + boot.length < 2^61` in `cluster_alloc`.

### Tier 2

#### G4. [spec] kvreconf's `validConf` calls raft functions whose specs are not in the API

**Principles**: *Complete*; *every premise has a source the client sees*; *the spec of an API*.

**Evidence**:
- `validConf` (`kv.go:219-240`) calls `confchange.Restore`, `tracker.MakeProgressTracker`,
  `Changer.{Simple,EnterJoint,LeaveJoint}` and `ConfChangeV2.{LeaveJoint,EnterJoint,GetChanges}`.
- `etc/api/raft.txt` lists `Spec.go_etcd_io.raft.v3.raftpb.*` but no `Spec…confchange.*` or `Spec…tracker.*`
  module.
- The only interfaces of those specs are internal (`interface/Proof/go_etcd_io/raft/v3/confchange/*.txt`,
  `tracker/*.txt`), stated over the tracker's internal ownership.
- §1's "Laws of `Membership` … over the `confchange` specs' models" names the laws but not the specs a client
  calls, nor the predicates they are stated in. Plan U11 says "`validConf` over the `confchange` specs" (an
  obligation, carried there), but the API part is a spec decision.

**Restatement**: add to §1/§3 the client-facing specs of these functions, over `Membership`. For example:
- `Restore` gives `ownChanger c m` from a `cs` with `confStateIs cs m`;
- each of `Simple`/`EnterJoint`/`LeaveJoint` returns `nil` exactly when `applyChange` of the matching
  `ConfChangeIM` is `some`;
- `MakeProgressTracker` gives an empty tracker.

List them in `etc/api/raft.txt` (U9).

#### G5. [spec] `Compact`: `fi`'s meaning, and the applied bound with no source

**Principles**: *No unneeded premise* (no stricter than the Go code); *every premise has a source*.

**Evidence: what `fi` means.**
- §4 calls `fi` the "first index". In `MemoryStorage` that is `ents[0].Index + 1` (`storage.go:203-205`).
- `Compact(c)` errs only for `c ≤ ents[0].Index` (`storage.go:271-273`).
- Under that reading, `fi < c` forbids `c = FirstIndex()`, which the Go accepts, and the post's new first index
  should be `c + 1`, not `c`.
- kvreconf compacts to any index in `[first, hi]` (`kv.go:390-403`, `first + below(hi-first+1)`). So kvreconf's
  `Compact(first)` is excluded under the literal reading. The formulas are right only if `fi` is the dummy entry's
  index.

**Evidence: the applied bound.**
- "`c ≤` the applied index raft knows" names no resource.
- Today that bound is `memFloorTok ms γs x`, moved by `Advance`'s post (`MemoryStorage__Compact.txt`).
- It is needed: compacting past `applied` makes raft panic (`issues/etcd-compact-past-raft-applied.md`).

**Restatement**:
- Define `fi` as the dummy entry's index (`FirstIndex() - 1`), and say so; or keep "first index" with
  `fi ≤ c` and post `storWriter st si (c+1) li`.
- Name the floor (`memFloorTok … x`, `c ≤ x`, from `Advance`'s post).

#### G6. [spec] `receiptBound ≤ 2^61` for every cluster weakens kv's adequacy, and the candidate does not say so

**Principles**: *No unneeded premise*; *know the margin*; a change to a trusted statement (the user's decision).

**Evidence**:
- kv's `Main.spec` takes `receiptBound ≤ 2^63`. Its adequacy is about executions of `n < 2^63` steps
  (`kv/Adequacy.lean:27-31`, `:135`, `:144`).
- kv's proof does not need `readyFits`: it takes `2^61` from its storage floor (`KV__run.lean:596`,
  `Defs.lean:171`).
- Under candidate 8, `kv_adequate` becomes `n < 2^61`. The apparent reason is that `snapshotCert_make` takes no
  index bound, but the candidate does not say so.

**Restatement**: either
- say it: §6 "every cluster's receipts' bound past its bootstrap log is at most `2^61`; `kv_adequate` moves to
  `n < 2^61`", and ask the user; or
- keep `cluster_alloc`'s `≤ 2^64 - 2`, give `⌜receiptBound + boot.length ≤ 2^61⌝ → readyFits γ N`, and let
  `snapshotCert_make` take `uint.Z i < 2^61`.

### Tier 3

- **G7. [spec] `snapshotCert_make`'s `cs.NoDupLists` is derivable.** `confStateIs cs m` makes each list a `Perm`
  of `elements` of a set (`NodeApiVocab.txt:76-80`), so each is `Nodup`. Drop the premise. The comment "what
  `SnapListsOk` adds" is then wrong: nothing is added beyond `m.Valid` and the length bound.
- **G8. [spec] `stepIn_intro`'s `MsgSnap` premise is now derivable.**
  - `sentMsg_snapshot` gives `snapshotCert`; `snapshotCert_made` gives a committed `l` with
    `l.length = Index`; G3's law then gives `< 2^61`.
  - With `readyFits` in every cluster, `stepIn_intro` can take `readyFits γ N`, or `isCluster` if `isCluster`
    implies `readyFits`, in place of the premise.
  - kv spends glue on it (`Cluster.lean:83`, `:222`; `deliverable.lean:120-121`).
- **G9. [obligation, carried by §0 U4 and plan U4; spec record missing] The newcomer-at-`c0` restriction is not
  recorded where §0 says.** §0 cites `notes/decisions.md` for "the protocol's invariant forbids a node at a
  configuration that is not a fold of its log". No such entry exists (grep for joiner/newcomer/"not a fold"
  finds only D22-era notes on etcd's empty `ConfState`, `decisions.md:12186`, `:12531-12552`). Add §6's
  decision and the entry. Without §5's Go change, kvreconf's newcomer (`cluster.go:163-176`, an empty
  `ConfState`) is excluded.
- **G10. [spec] `fold_snoc_conf` is still unstated, and `nodeConfig_reject` still updates (F10, F12
  residuals).**
  - `ConfRule` takes the `LogEntry`, so "a rule decides from the decoded change" is not something the type
    enforces.
  - Whether `fold_total` needs its decode premise depends on `fold_snoc_conf`. Write it out, and drop the
    premise if `fold` consults only the rule.
  - With U6m's "a rejected entry counts as decided" (the rule is pure), `nodeConfig_reject` needs no ghost
    update. Make it `⊢`, like `nodeConfig_skip`, or say what the update records.
- **G11. [obligation, plan] Plan U11 still says "bounded ticks, campaigns and `MsgTimeoutNow` deliveries: the term
  budget".** That contradicts §3's "No credits" and U7's "raft's proofs take their own time receipts". Either
  kvreconf's Go must bound them, or it need not; say which.
- **G12. [spec, trust base] Say that `ccDecodeV2_nil` reaches every result over raft.** U5 proves `appliedTo`,
  which runs on every `Advance` path (`raft.go:742-760`). So kv's and the server's results will rest on the
  axiom, not only kvreconf's. §0 says only that U5 needs it (F4's residual).
  - The axiom itself is sound: `MarshalConfChange(nil)` gives `EntryConfChangeV2` with `nil` data
    (`raftpb/confchange.go:40-45`), and the leader unmarshals it (`raft.go:1327-1337`).
  - It is consistent with `MarshalConfChangeV2.spec` (`MarshalConfChangeV2.lean:31-48`; decoding is not
    required to be injective).
  - It still needs the user's approval.
- **G13. [spec, nits]**
  - §1's "(F9)" label: F9 was `bootedCluster`.
  - The stopped `Step`: say that a `nil` message is excluded by the argument's ownership.
  - `Propose` with `data = []` gives a filler, which `opsOf` drops, so its update is never fired. Sound (fired at
    most once), but a margin to state.

## What is good

- **`clamp_eq` (F2)** is now true, and pointwise exactly where callers have `m.Valid`, from `committed_fold` or
  `nodeConfig_fold`.
- **kvreconf's Go is left as it is for the automatic leave (F4).** The trust base is the same either way, and
  kvreconf stays a plain user of raft.
- **The stopped case (F13)** is one triple per function, with a case split on the input. The answers match
  `node.go`:
  - `Step`: `474-485`;
  - `stepWithWaitOption`: `513-545`, `ErrStopped`/`ctx.Err()`;
  - `Advance`/`ApplyConfChange`/`Status`/`Report*`: `551-600`.
- **`bootedCluster` is gone (F9)**, and `stepIn_intro`'s shape premise with it (F7). `sentMsg_noTransfer`
  excludes both transfer messages (F8), which is what the server uses today (`InvNet.lean:88-89`).
- **The plan is in step with §0 (F6)**: U4 (joiners, pre-votes at term 0, the scope), U5 (`RaftLeave`, the axiom),
  U6m (one mechanism), U7 (receipts), U8.
- The rest is as review 7 found it:
  - the certificate at the committed term;
  - TaDa snapshot ownership;
  - no credits;
  - `RaftLeave`/`opsOf`;
  - `ApplyConfChange`'s disjunctive post;
  - one allocation with two start kinds and `transferChoice`.

## kvreconf's Go still excluded

| behaviour | where | excluded by | kind |
|---|---|---|---|
| `CreateSnapshot` at an index appended in an earlier `Ready` (in the loop and after `Advance`) | `kv.go:349`, `355`, `366-379` | G1 | spec |
| `Compact(first)`; the applied bound's source | `kv.go:390-403` | G5 | spec |
| `validConf` (`Restore`, `Changer.*`, `MakeProgressTracker`) | `kv.go:219-240` | G4 (plan U11 carries the proof) | spec + obligation |
| a newcomer on an empty `ConfState` (today's Go) | `cluster.go:163-176` | §5's Go change; G9 | scope restriction, not yet in `decisions.md` |
| unmarshalling raft's automatic leave | `kv.go:443-447` | the axiom's approval | trust base |
| a joiner at `c0`; pre-votes at term 0 | `cluster.go:163-176` | U4 (§0, plan) | obligation |
| `ApplyConfChange` after a rejected entry | `kv.go:455-470` | U6m (§0, plan) | obligation |
| raft's automatic leave | `raft.go:742-760` | U5 (§0, plan) | obligation |
| a forwarded `MsgTransferLeader`; `MsgTimeoutNow` | `reconf.go:104` | U7 (§0, plan) | obligation |

**Not excluded** (checked):
- the stopped paths, including `r.cs = nil` after a `nil` `ApplyConfChange` (`kv.go:470-472`, `r.cs = cs` at 472);
- duplicated and retried `MsgProp`, through `proposalReg` and `msgCredits_intro`;
- `ReadIndex`, `Campaign`, `ForgetLeader`, `Status().Lead`, `TransferLeadership`;
- `ApplySnapshot` and `install`, through `Advance`'s snapshot post;
- the `Snapshot` wrapper's `ErrSnapshotTemporarilyUnavailable`, through the wrapper law.

The wrapper law should also say how `storWriter` (or G2's fragment) passes through the embedding: kvreconf calls
the promoted `CreateSnapshot` on `*Storage`.

**Excluded elsewhere (not kvreconf)**: etcd's server's snapshot and compaction, by G2.

## Ranking (most in need of revision first)

1. **Storage** (G1, G2, G5): the storage section needs redesign, not patches. Keep the atomic specs, add a writer
   fragment, and take the term from the node's delivered log.
2. **False law** (G3): a one-character fix.
3. **API completeness for `validConf`** (G4).
4. **Trusted-statement cost** (G6, G12): the user's decision.
5. **Derivable premises** (G7, G8).
6. **Records and residuals** (G9, G10, G11, G13).

## Uncertain

1. G1's restatement: that raft's storage invariant (`InvStorage`) ties the storage's entries in
   `(si, |delivered|]` to the delivered log once a `Ready`'s entries are appended. I did not read `InvStorage.lean`.
2. G1's counterexample needs `node.run` to step a conflicting `MsgApp` while a `Ready` is being handled. I read
   that from `run`'s select (`recvc` is always enabled), not from a test.
3. G6: whether `n < 2^61` matters to the user; it is a factor of 4 in the adequacy bound.
