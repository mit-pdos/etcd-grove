# Review of the unified node-API candidate (candidate 1 + "Candidate 2"), round 2

Reviewer: fresh `spec-reviewer`, 2026-10-28. Read-only; nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate.md`. It is a design that is
  not implemented and not in the repository, so no finding can be stale against `HEAD`.
- **Compared with**: today's `interface/Proof/go_etcd_io/raft/v3/{InvNode,NodeApiVocab,ApiVocab}.txt` and
  `interface/Spec/go_etcd_io/raft/v3/*.txt`, at worktree `HEAD` `08b9b323b0`.
- **Go source**:
  - `.lake/raft-fork`, branch `raft37-goose-lean-a2`, `565c2bd`;
  - etcd's server as translated, `/home/ubuntu/etcd-grove/.lake/goose/etcd/server/etcdserver/server.go`;
  - `examples/kvreconf`, read in full, with `cmd/kvreconfcheck`.
- **Rubric**: `.claude/agents/spec-reviewer.md` and `.claude/skills/spec-repair/{SKILL,LESSONS}.md`. The
  brief's `.claude/skills/spec/PRINCIPLES.md` and `.claude/skills/spec/examples/README.md` **do not exist** in
  this worktree, and there is no `.claude/skills/spec/` directory, so I could not apply them.
- **Context**: review 1 (`notes/spec-first-study/raft-node-unified-review-1.md`). The worktree now has an
  untracked `issues/raft-applyconfchange-reject-doc-contradiction.md`. It files the doc defect that review 1
  said had no `issues/` file of its own.

## Summary

The candidate is the right overall shape:
- one cluster predicate;
- client-owned snapshot ghost state, TaDa style;
- `nodeConfig` for every node, with skip and reject laws;
- a join token;
- specs for `Stop`, `Campaign`, `ForgetLeader` and `Status`.

It answers most of review 1. But it has **four Tier-1 defects**, three of them new in this round:

1. **`γ.c0 = ∅` for `StartNode` clusters is false of Go and unprovable** (A1).
   - Go: `Bootstrap` installs every peer as a voter before any `ApplyConfChange`. So on a founder,
     `ApplyConfChange` of the first bootstrap entry returns all the peers, not `{p1}`.
   - Machinery: `DynCfg.ofFold` needs `CfgOk c0` (an incoming voter), and `adj` fails at the empty prefix.
   - Newcomers (`RestartNode` with an empty `ConfState`) also go through configurations that are not the
     fold, which today's `RInv` forbids.
2. **The persistent `Propose` update (F6) breaks etcd's server** (A2).
   - The server's contract is one-shot: `srvPropAu1`, `kvOpAu1`, "fired at most once".
   - Duplicate commits should be paid by the client, per copy, the way the candidate already pays for reads.
3. **Making an empty `EntryConfChangeV2` a filler (F5) breaks etcd's server** (A3).
   - etcd panics on any `EntryConfChangeV2` (`server.go:1950-1955`).
   - Once raft may commit such entries freely, the server can no longer exclude them.
   - The server's proofs also destructure `isFiller` as "type 0".
4. **`Advance` cannot be called on a snapshot `Ready`** (A4). Its `NoConfChangeIn st.delivered …` premise is
   over the snapshot's prefix (`delivered := strip l.dlv`), which the application never applied.

There is also a provability gap the candidate understates (A5). The appliedSnap semantics it assumes is
neither in the translated code (a1) nor in the protocol model:
- `StepR.snapRestore` sets `cfg` at restore;
- `StepR.applyConf` requires `snap = false`.

Of the questions:
- **(a) The rule**: fixing it at allocation is what today's machinery forces. The stated reason ("uncommitted
  prefixes included", "before anyone applies it") is overstated.
- **(b) Snapshots**: the design is TaDa and enough for both clients' data. But the certificate's `m.lists`
  must become any `ConfState` satisfying `confStateIs`.
- **(c) The join**: sound for `c0` clusters (kv). Broken for `StartNode` clusters (A1).
- **(d) Proposals and fillers**: A2 and A3.
- **(e) What kvreconf still cannot do**:
  - the bootstrap prefix (A1);
  - newcomers (A1);
  - snapshot `Ready`s (A4);
  - `Stop`: the candidate wrongly says `Main` never stops (A6);
  - the joint/auto-leave path in the a2 window (A5).

I found no new bug in the Go code (see "Go defects").

---

## Findings, ranked

### A1. `γ.c0 = ∅` for `StartNode` clusters: false of Go, unprovable from the machinery, and newcomers unsupported (Tier 1: true of the code; provable; sufficient for kvreconf and the server)

**The candidate's choice.** "`StartNode.spec`: … the storage empty with an empty initial `ConfState` and `γ.c0 =
∅` (the bootstrap's entries are the configuration); post `nodeConfig {applied := 0, membership := γ.c0}`".
`cluster_alloc` allows this through `(boot = [] → c0.voters ≠ ∅)`. Newcomers start with `RestartNode` on an
initial `ConfState` of `γ.c0`.

**It is false of Go.** `RawNode.Bootstrap` appends the peers' `AddNode` entries and then applies them to the
tracker at once (`.lake/raft-fork/bootstrap.go:77-80`; the comment says "these nodes will be added to raft
twice"). On a founder, `ApplyConfChange(AddNode p1)` of entry 1 therefore runs `Simple` on the full
configuration, a no-op, and returns every peer (`raft.go:1952-1980`). The candidate's `ApplyConfChange.spec`
promises `confStateIs cs m'` with `m' = applyChange (AddNode p1) ∅ = {p1}`, which is false for two or more
peers.

kvreconf observes this:
- `Replica.applyConf` stores the returned `cs` (`kv.go:582-585`), so a founder's `r.cs` after entry 1 is all
  the peers.
- `maybeSnapshot` may then snapshot at index 1 with that `cs` (`kv.go:460-461, 478-497`).
- `snapshotCert_make` would need `cs = fold(l[:1]) = {p1}`, so kvreconf cannot certify the snapshot.

**It is unprovable from the machinery.**
- `DynCfg.ofFold dec c0 h0` needs `h0 : CfgOk c0` (`Protocol/RefinementDyn.lean:49`), and `CfgOk` requires
  `s.cfg.incoming ≠ ∅` (`Protocol/CfgOverlap.lean:97-98`).
- Independently, `DynCfg.adj` (`Protocol/Ghost.lean:173-176`) fails for `P1 = []`, `P2 = [e1]`:
  - `MajQ ∅ q` holds for every `q` (`Protocol/StepC.lean:65`);
  - so the empty set is a joint quorum of the empty configuration;
  - so `QOverlap ∅ {p1}` is false.

  This is not a technicality: raft counts every vote as won in an empty configuration.
- Today's dynamic mode starts the fold at the peers' configuration, not at `∅`:
  - `bootInit`/`rnInit` take `c0 = cfgState V ∅` (`ApiVocab.lean:532,585`);
  - `dynamicCluster_alloc` takes `c0 := Membership.simple (listToSet ps)` (`InvApiDyn.lean:300-305`);
  - its `StartNode.dynamicSpec` posts `nodeConfig {applied := 0, membership := Membership.simple ps}`
    (`interface/Spec/.../StartNode.txt:84-88`).

**Newcomers in a `StartNode` cluster are not covered under either choice of `c0`.** kvreconf's `startNew`
(`cluster.go:166-178`) and etcd's joiners use `RestartNode` on a fresh `MemoryStorage`, whose `ConfState` is
empty.
- If such a newcomer catches up from the log, its tracker goes `∅ → {p1} → {p1,p2} → … → ps` while it applies
  the bootstrap entries. These are not the founders' configurations at those indices.
- So the "configuration at prefix k" is not a function of the log for `k < bootLen`.
- With `c0 = ∅` the founders break the specs. With `c0 = simple ps` the newcomers do:
  - their `ApplyConfChange` answers are partial, not the fold;
  - `rnInit` needs the persisted voters to be `c0`'s;
  - `RInv` ties a node's configuration to the fold of its first `cidx` entries
    (`Protocol/RefinementDyn.lean:9-13`).

**Restatement (one of the following).**
- **(i) Recommended.**
  - Keep `c0 = simple ps` for `StartNode` clusters, as today.
  - The fold over the bootstrap entries follows the rule. A `simple ps` founder's tracker matches whatever the
    rule decides, so `cluster_alloc` needs no extra premise.
  - Require a newcomer's initial `ConfState` to be `γ.c0`'s lists, as the candidate already says for
    `c0`-clusters.
  - kvreconf then changes in Go: a `Storage` whose `InitialState` returns the bootstrap voters, as kv's does
    (`examples/kv/kv.go:54-75`), and `r.cs` initialised to that `ConfState`.
  - etcd's joiners stay out of scope; the server proof has no `RestartNode`.
- **(ii)** A newcomer's `nodeConfig` gets a "pre-bootstrap" phase:
  - `nodeConfig_fold` only for `v.applied ≥ γ.bootLen`;
  - `ApplyConfChange` there posts `confStateIs cs (applyChange o v.membership)`, which is true;
  - `snapshotCert_make` only for `l.length ≥ bootLen`. kvreconf then changes in Go so that a newcomer does not
    snapshot below `bootLen`.

  This needs a new `RInv` case for a node that is not in its own configuration. Such a node is not
  promotable (`raft.go:1947-1949`), so it is plausible, but it is new protocol work.

### A2. A persistent `Propose` update weakens etcd's server spec (Tier 1: sufficient for the server; Tier 2: weakest precondition)

**The candidate.** F6 makes `node.Propose.spec` (and `ProposeConfChange.spec`) take
`□ AU <{∃∃ ops, ownCommittedOps γ ops}> … <{∀∀ t, ownCommittedOps γ (ops ++ […]), COMM True}>`, "fired once per
committed copy". It adds `msgCredits_prop : MsgProp → sentMsg ⊢ |==> msgCredits`.

**What the server relies on.** The server proves a one-shot contract:
- `srvPropAu1`: "The proposer's update for `d`, fired at most once" (`SrvRaftLog.lean:528-536`). Its header
  (`SrvRaftLog.lean:16-21`) says a proposal "fires once (its token `γt`)".
- `kvOpAu1`: the clients' updates for put, delete-range and txn, which are not persistent and whose `Q` is
  not persistent (`InvRequest.lean:259-270, 383-423`).

The server never duplicates a proposal, and its transport is not modelled as duplicating. With a persistent
raft-level update:
- the server must give raft a persistent update;
- a second commit of the same `Put` must then change the KV state with no client linearization point;
- so either the exported `EtcdServer.Put/DeleteRange/Txn` specs fall back to the persistent `kvAu`, with a
  persistent `Q` and possible double effects, or the server becomes unprovable.

That is a change to trusted statements, which needs the user's approval.

**The candidate's own inconsistency.** F6 already makes the client pay for each duplicated read
(`msgCredits_readIndex : readCredit ⊢ |==> msgCredits`), but takes proposals' duplicates for free from the
persistent `sentMsg`.

**Restatement.**
- Keep `Propose`'s update one-shot.
- Put duplication on the client's side, as for reads: a duplicated `MsgProp` needs a fresh update for each
  of its entries, `msgCredits_prop : MsgProp → sentMsg γ N src st ∗ ([∗list] e ∈ props st, AU(e.data)) ⊢ |==>
  msgCredits γ N st`.
- Add a persistent witness that a sent `MsgProp`'s entries are proposals (`sentMsg ⊢ ∀ e ∈ props st, proposed γ
  e.data`), so that kvreconf's network can find the update in its invariant. kvreconf's invariant keeps
  `□ AU(d)` for every operation encoding `d` it ever proposed; its operations are idempotent (`applyOp`).
- One spec then covers both clients; the persistent variant is a layer on top (LESSONS 2026-10-27: keep the
  stronger spec).

### A3. Making an empty `EntryConfChangeV2` a filler loses a fact etcd needs (Tier 1: sufficient for the server; caller unfolds)

**The candidate.** F5 makes `LogEntry.isFiller e := e.data = [] ∧ (type 0 ∨ type 2)`, so raft may commit an
empty v2 entry without any client update.

**Why etcd cannot accept this.** etcd's apply loop panics on any entry that is neither `EntryNormal` nor
`EntryConfChange` (`server.go:1933-1955`, `"unknown entry type; must be either EntryNormal or
EntryConfChange"`). Today the server proves no-panic because:
- every committed entry is either a filler, which is normal, or one of the server's own operations;
- `LogEntry.isFiller_normal` holds.

Under F5 nothing would exclude a type-2 entry, although raft only appends its leave when the leader's
configuration is joint with `AutoLeave` (`raft.go:742-763`), which etcd's v1 simple changes never enter.

The server's proofs also unfold `isFiller` positionally (each would need rework):
- `KVAuthModel.lean:529-532` (`obtain ⟨hd, ht⟩ := hf`);
- `SrvRaftLog.lean:279-280` (`toLE_isFiller … ↔ (m.data = [] ∧ m.typ = W32 0) := Iff.rfl`);
- `KVLemmas.lean:110`, `NewServerAlloc.lean:200`.

**Restatement.**
- Keep `isFiller` as type 0.
- Let `ownCommittedOps`' meaning drop raft's own leave entries by context: an empty v2 entry whose prefix
  folds to a joint `AutoLeave` membership. It is true that the leader appends the leave only after applying
  every conf entry before it, so the prefix's fold is the leader's joint configuration.
- Export the law `committed_v2 : isCommittedLogLb γ l ∗ ownCommittedOps γ ops ⊢ ⌜∀ k e, l[k]? = some e → e.type =
  2 → e ∈ opsOf … ∨ (fold (l.take k)).autoLeave ∧ joint⌝`. With it, the server shows there are no v2 entries,
  and kvreconf gets its decode facts.
- A client's explicit `ConfChangeV2{}` keeps its update. When it is indistinguishable from raft's (proposed
  while the membership is joint with auto-leave), the update simply never fires, which is harmless with
  `COMM True`.

### A4. `node.Advance.spec` cannot be called on a snapshot `Ready` (Tier 1: sufficient)

**The premise.** "`nodeDriver st` with `st.handling = some (es, L)` … `NoConfChangeIn st.delivered v.applied
st.delivered.length` and `v.applied ≤ st.delivered.length`."

**Why it fails.** After a snapshot `Ready`, the driver's state has `delivered := strip l.dlv`, the snapshot's
whole prefix (`node.wp_readyRecv`, `interface/Proof/.../InvNode.txt:103-112`). The client applied none of that
prefix. A snapshot of a reconfigured cluster has conf entries in it beyond `v.applied`, so the premise is false
exactly when the snapshot matters.

kvreconf hits this:
- every newcomer's first snapshot;
- every install after a compaction (`kv.go:443-451, 465`).

**Restatement.** Split on `L`:
- `L = none`: today's premise;
- `L = some l`: no premise on `v`. Every earlier conf change was applied before the previous `Advance`, which
  that `Advance`'s premise required, and a snapshot `Ready` carries no committed entries (`log.go:225-228,
  253-258`).

The post is as in the candidate (`{applied := snap index, membership := the snapshot's}`).

### A5. The appliedSnap semantics is in neither the translation nor the protocol model (Tier 1: provable; understated)

**What the candidate assumes.** It "assumes raft's configuration switches at `appliedSnap` (fork
`raft37-goose-lean-a2`)".

**What exists.**
- **The translation.** The translated raft is a1 (`c8217eb9`, CLAUDE.md). The fork's `565c2bd` moves
  `confchange.Restore` from `restore` to `appliedSnap` (`raft.go:766-788`).
- **The protocol model.** It is a1's:
  - `StepR.snapRestore` sets `cfg := cs'` and `cidx := m.index` at restore (`Protocol/StepR.lean:287-306`);
  - `StepR.applyConf` requires `r.snap = false` (`StepR.lean:403-413`);
  - `StepR.applySnap` only moves `applied` (`StepR.lean:398-400`).

**Why it matters for the candidate.**
- The candidate's `Advance` clause ("raft switches to its configuration now") needs `applySnap` to set `cfg`.
- kvreconf needs `ApplyConfChange` of an entry from an earlier `Ready` while a restored snapshot is pending.
  The network goroutine's `Step(MsgSnap)` interleaves with the run loop's applies; this is the scenario of
  `issues/raft-snapshot-during-apply-stale-confchange`. Today's `applyConf` forbids it.

**What I checked of a2's safety.** In the window between restore and `appliedSnap`, the node campaigns with a
stale configuration but a newer log. It cannot:
- `promotable()` is false while `unstable.snapshot` is set (`raft.go:1947-1949`);
- so `hup` returns before `hasUnappliedConfChanges`, which would otherwise scan a compacted range and panic
  (`raft.go:991-1004, 1013-1037`).

So a2 looks safe there. But the model has to say so.

**Restatement.**
1. List, as a prerequisite of the candidate:
   - retranslate to a2 (`etc/goose.py --src raft=.lake/raft-fork`);
   - `snapRestore` keeps `cfg`/`cidx`;
   - `applySnap` sets them from the snapshot;
   - `applyConf` is allowed with `snap = true`, on the pre-snapshot full log.
2. Re-check the RInv cases.

### A6. `Stop`: the candidate's premise about kvreconf is false, and the stopped answers must be tied to a witness (Tier 1: sufficient; failure pattern "vacuous disjunct")

**The candidate's claim.** F8 says "kvreconf's `Main` does not stop the cluster (it returns once porcupine
answers)". This is false:
- `Main` calls `c.Stop()` after porcupine's `Ok` (`check.go:172-178`).
- `Replica.stop` closes `stopc` and then calls `node.Stop()` (`kv.go:416-419`). Meanwhile:
  - the run loop may be in the middle of a `Ready`: `ApplyConfChange` returns `nil` after `Stop`
    (`node.go:562-572`), `Advance`, `CreateSnapshot`;
  - delayed deliveries keep calling `Step`, `ReportSnapshot` and `ReportUnreachable` on stopped nodes
    (`cluster.go:254-258, 268-292`).
- kvreconf survives a `nil` `cs`: `validConf` treats `nil` as empty, and `maybeSnapshot` skips (`kv.go:331-334,
  483`).

**Restatement.**
- `node.Stop.spec` gives `nodeStopped n`, persistent.
- Each method's stopped answer is the disjunct `nodeStopped n ∗ ⌜stopped answer⌝`, never an unguarded
  disjunct.
- `ApplyConfChange`'s stopped branch is `csp = null` and gives `nodeConfig v` back unchanged.
- The same for `Advance`, `Step` (`ErrStopped`), `Tick`, `Report*`, `Status` (`Status{}`) and `ReadIndex`
  (`ErrStopped`).
- Fix the sentence in F8.

### A7. The snapshot certificate must not fix the lists' order: `cl := m.lists` (Tier 1: sufficient for kvreconf and the server)

**The candidate.** `snapshotCert_make` certifies `cl := m.lists`, and `snapshotCert_made` gives `k.cl = m.lists`.

**Why exact lists are a problem.**
- The storage records the `ConfState` exactly:
  - `sv.Metadata'.ConfState'.lists = σ.scs` (`interface/Proof/.../InvMemstorage.txt:199,257,347`);
  - `sentMsg_snapshot` certifies `snapTrip sv sv.Metadata'.ConfState'.lists`.
- But the `ConfState` a client passes to `CreateSnapshot` is raft's answer, or a received snapshot's clone:
  - kvreconf: `kv.go:490, 522`;
  - etcd: `ep.confState`, `server.go:2046, 2125`.
- Its order is raft's (sorted), and nothing makes it equal a canonical `m.lists`. Today's
  `ApplyConfChange.dynamicSpec` already only gives `confStateIs cs m'`, a `Perm`.

**Restatement.**
- `snapshotCert_make … : … ⊢ □ ∀ t cs, ⌜confStateIs cs m ∧ last term = t⌝ → snapshotCert γ N {sid := ⟨t, i⟩, cl
  := cs.lists, al := cs.AutoLeave', dat := d}`.
- `snapshotCert_made` gives `confStateIs k.cs m` (or `Perm`).
- (`MemoryStorage.CreateSnapshot` with `cs = nil` keeps the previous `ConfState` (`storage.go:258-260`); its spec
  must state that case. etcd could pass `nil` only before applying any conf entry.)

### A8. The rule (question a): right abstraction, overstated reason, and etcd's description incomplete (Tier 2: abstraction and documentation; one scope citation)

**The abstraction is right for these clients.**
- kvreconf's rule is `ConfRule.validated` on the membership in force.
  - `validConf` restores `cs` and runs the same `Changer` step as raft (`kv.go:331-351`; `raft.go:1952ff`).
  - The errors depend only on the configuration, not on the progress.
  - With F9's laws it equals `(applyChange o m).isSome`.
- etcd's rule is a function of the prefix (its membership store). A refusal is "apply with `NodeID` 0", which
  `confchange` skips (`server.go:2027-2030`; `applyChange_nodeZero`).
- Passing `m` beside `pre` is redundant (`m` is the fold of `pre`) but avoids a circular definition, so keep it.
- `ConfRule.Ok` over every valid `m` is not restrictive: any rule can be made `Ok` by filtering out the
  decisions `applyChange` refuses. The client then proves that its Go decision equals the filtered rule on
  reachable states. For etcd that needs a workload premise, because etcd's own rule can remove the last voter
  (`issues/raft-remove-last-voter-panic.md`). Say so in the docstring.

**The stated reason is overstated.** The candidate says the fold covers "every log prefix, uncommitted ones
included", so that "the cluster needs the interpretation of every possible entry before anyone applies it".
What the machinery uses:
- the configurations it uses are of committed prefixes:
  - `CfgAt`: "the configuration `c` is the one of the committed prefix `P`" (`Ghost.lean:499-505`);
  - `RInv`: the fold of the first `cidx ≤ applied` entries (`RefinementDyn.lean:9-13`);
  - `raftSnapCert`'s recorded full prefixes (`Ghost.lean:1552-1557`);
- a node only uses a decision its own application made.

What forces a fixed rule is the machinery's design:
- `DynCfg` is a total pure function, in the ghost names `RaftNames.reDyn`, fixed at allocation (`Ghost.lean:285,
  482`);
- `adj` is stated for arbitrary prefixes.

A ghost-state rule, decided at first application and agreed afterwards, is conceivable, but it would be a
redesign of `CfgAt`/`DynCfg` across the protocol proof.

Restate the reason as: "the protocol proof's configuration function is fixed at allocation (`RaftNames.reDyn`);
deciding it as entries are applied would mean replacing `DynCfg`/`CfgAt` throughout; no client here needs a
rule that is not a function of the committed prefix."

**etcd's rule is not only "`NodeID` 0".** With `shouldApplyV3 = false`, i.e. a replay of entries at or below the
backend's consistent index, etcd does not call `ApplyConfChange` at all (`server.go:2041-2047`). That decision
depends on node-local state, not on the log. It is out of scope only because the server proof has no restart.
State it as a scope restriction with a citation (F14).

### A9. `leaderTransferOn`/`Off` is a mode family, and kvreconf needs no campaign bound (Q-B) (Tier 2: special-case family; Tier 1 for the candidate's claim about kvreconf)

**Q-B is moot.** F7 and Q-B say kvreconf "must bound its campaigns (as kv bounds transfers)". It need not:
- `tickCredit_intro : ⧗n ⊢ tickCredit γ n`, and a time receipt `⧗ 1` is taken from any function or method
  resolution step (`Proof/ReceiptTactics.lean:1-10`). kv's `tick` pays each `Tick` this way
  (`Proof/.../kv/tick.lean:46-48`).
- So `Disrupt`'s `Campaign` call pays for itself from its own resolution, and `deliver`'s `Step` of each
  duplicated `MsgTimeoutNow` from its own `Step` call. No Go change is needed.

**The mode family has nothing left to buy.** With F7's message-shape law holding in every cluster, a
transfer-off cluster no longer saves its clients anything: no message filter, no budget. By LESSONS
2026-10-27 ("no special-case predicate or spec family"), drop `leaderTransferOff` and the `transfer` parameter
of `cluster_alloc`.

**Uncertain:** whether the protocol's `reNoXfer` mode is needed for something else; `RaftNames.noXfer_boot`
(`Ghost.lean:474-479`) ties it to a bootstrap log.

### A10. Smaller points

- **`snapshotCert_make` has no `SnapListsOk` premise.** `raftSnapCert` requires `index < 2^61`, `Nodup` lists
  and the size bound (`Ghost.lean:605-611`). Today's `snapshotCert_static` took them as a premise. Provable if
  `isCommittedLogLb` bounds the length (`receiptBound + bootLen ≤ 2^61`) and `m.Valid` gives the rest.
  **Uncertain.**
- **Duplicated reads.** `msgCredits_readIndex` spends a `readCredit` per copy, from a finite supply
  (`2^64 - 2`). kvreconf would have to tie its supply to its receipts. Simpler: `⧗1 ⊢ readCredit γ`, as for
  ticks. **Uncertain:** whether the read-context registry admits two `ReadState`s for one context. raft ignores a
  duplicate while it is pending (`read_only.go`, `addRequest`), but one arriving after the first completed opens
  a second read.
- **The join token** (`joinAuth γ U`, `joinAuth_join`) is needed: two nodes with one id would vote twice. It fits
  kvreconf's `nextID` under `Cluster.mu`. **Uncertain:** whether a newcomer's `PreVote` still needs
  `bootedCluster` (review 1, table row 16).
- **`snapshotCert_make` is a ghost law, not part of `CreateSnapshot`'s spec.** This is fine and arguably better
  (etcd's and kvreconf's snapshots go through the storage). A client may mint certificates it never uses, which
  is harmless.
- **`committed_fold` is pure** given `rule.Ok` and `c0.Valid`. It may stay stated over `isCluster`, since
  `γ.rule` is sealed.
- **Open question Q-A** (one `nodeBoot` or two): with A1(i), `StartNode` founders and `RestartNode`-from-`c0`
  founders are different allocations (`boot ≠ []` versus `boot = []`), so two tokens are natural.
- **MemoryStorage cannot provide the `c0` path.** `RestartNode` "from `c0`" on an empty log needs a storage whose
  `InitialState` is `c0`. `MemoryStorage` cannot provide one: `ApplySnapshot` at index 0 is `ErrSnapOutOfDate`.
  kv uses a wrapper (`examples/kv/kv.go:54-75`). Under A1(i), kvreconf needs the same wrapper; the candidate's
  F11 storage-wrapper law should cover an overridden `InitialState` too.

---

## Per question

**(a) The rule.**
- Right abstraction (A8).
- Reason overstated: the machinery, not the logic, forces it.
- etcd's description incomplete (`shouldApplyV3`).
- `Ok` is not a burden but needs the workload note for etcd.

**(b) Snapshots.**
- TaDa: yes. `ownSnapsMade` is exclusive and client-owned; making a snapshot extends it; receiving one gives
  `snapMade` plus a committed prefix and the configuration there.
- Sufficient for kvreconf's data: its invariant over `S` is "`data = encodeState(state of the committed prefix of
  length index)`", read back with `isCommittedLogLb_agree`. The decode panic is excluded.
- Sufficient for etcd's empty data: the invariant "every `s ∈ S` has `data = []`".
- But:
  - A7 (lists);
  - A1 (bootstrap-region snapshots);
  - A4 (the installing `Advance`);
  - A10 (`SnapListsOk`).
- etcd installing a snapshot and then validating conf changes needs its membership store to equal the prefix's.
  That comes from the backend snapshot, which travels outside raft. It is the server's to tie to `isCommittedLogLb
  l`, not raft's.

**(c) Join.**
- Sound for `c0` clusters (kv).
- For `StartNode` clusters (kvreconf, etcd), broken under either choice of `c0` (A1).

**(d) Proposals and fillers.**
- The persistent update weakens etcd (A2); the fix is to make the client pay per copy.
- The filler extension removes etcd's no-v2 fact and breaks its unfolds (A3); the fix is to tell raft's leave
  apart by its context.

**(e) kvreconf's Go still excluded.**

| kvreconf behaviour | excluded by | finding |
|---|---|---|
| bootstrap entries applied at founders (returned `cs` = all peers); snapshots at index `< bootLen` | `γ.c0 = ∅`, `confStateIs cs m'` | A1 |
| newcomer `RestartNode` on a fresh `MemoryStorage`, catching up from the log | no fold-consistent configuration during bootstrap; `RInv` | A1 |
| `Advance` of a snapshot `Ready` | `NoConfChangeIn` over `strip l.dlv` | A4 |
| `ApplyConfChange` while a restored snapshot is pending (a2 window) | model is a1 (`applyConf` needs `snap = false`) | A5 |
| `Main`'s `c.Stop()` during applies and deliveries | F8 premise false; stopped answers unspecified | A6 |
| `CreateSnapshot(index, r.cs, …)` with raft-ordered lists | `cl := m.lists` | A7 |
| duplicated `MsgReadIndex` | finite `readCredit` supply; second `ReadState` per context (uncertain) | A10 |

No Go change is needed for:
- campaigns and duplicated `MsgTimeoutNow`, paid from receipts (A9);
- transfers asked of followers (F7);
- the storage wrapper's `ErrSnapshotTemporarilyUnavailable` (F11);
- unserialized conf changes and rejection (F4, `nodeConfig_reject`).

## Ranking (most in need of revision first)

1. **The cluster's initial configuration and the join**: `cluster_alloc` with `γ.c0 = ∅`, `StartNode.spec`'s
   post, `RestartNode` and `nodeJoin` for `StartNode` clusters (A1).
2. **`Propose`/`ProposeConfChange` and `msgCredits_prop`** (A2), and **`isFiller`/`opsOf`** (A3): both break
   the verified server.
3. **`node.Advance.spec`** (A4), and the a2 prerequisite of the protocol model (A5).
4. **`node.Stop.spec` and the stopped answers** (A6).
5. **`snapshotCert_make`/`snapshotCert_made`** (A7, A10): small restatements.
6. **The rule's documentation** (A8), and **`leaderTransferOn/Off`** with Q-B (A9).
7. **Sound as stated:**
   - `ConfRule`'s shape and `Membership.fold`;
   - `nodeConfig_fold`/`_skip`/`_reject`;
   - `ApplyConfChange.spec`, apart from A1 and A6;
   - `joinAuth`;
   - `ownSnapsMade`/`snapMade`/`snapMade_elem`;
   - F7, F9, F10, F11, F13, F14;
   - `Campaign`, `ForgetLeader`, `Status`.

## Go defects

No new bug in the Go code.
- **Two views of the bootstrap prefix.** Founders and log-catching newcomers hold different `ConfState`s at
  the bootstrap indices. This is a documented quirk of `Bootstrap` (`bootstrap.go:62-71`) and harmless: a
  newcomer is not in those configurations, so it is not promotable, and a founder never restores a snapshot
  below its commit index `bootLen`. It is not an issue.
- **a2's window** (restore → `appliedSnap`) does not reach `hasUnappliedConfChanges`' panic, because the node is
  not promotable then (`raft.go:997-1001, 1947-1949`).
- **Review 1's doc defect** (`doc.go` versus `node.go:179-183`) now has a file, untracked in this worktree:
  `issues/raft-applyconfchange-reject-doc-contradiction.md`.

## Uncertain points

1. **A1(ii)**: whether a newcomer's pre-bootstrap configuration can be admitted in `RInv`. To settle: try the
   `StepR` invariant with a "not a member of its own configuration" case.
2. **A5**: the extent of the `StepR` and RInv rework for a2. To settle: restate `snapRestore`/`applySnap`/`applyConf`
   and rerun `Protocol/StepRInv.lean`.
3. **A9**: whether `reNoXfer` protects anything beyond the message-shape law.
4. **A10**:
   - whether `SnapListsOk`'s `index < 2^61` follows from `isCommittedLogLb`;
   - whether the read-context registry admits a second `ReadState` for one context.
5. **A2**: I did not trace how many server proofs would change if `Propose` took a persistent update. To settle:
   follow `srvPropAu_api` (`SrvRaftLog.lean`) through `KVLemmas.kv_prop_au`.
6. **A10, `bootedCluster`**: whether `PreVote` at a joined node needs `bootedCluster` (`nodeBoot_booted`).
7. **Not run**: no build, `lean-check` or `tcb-report`. Every Lean citation is from source and `interface/` at
   `08b9b323b0`.
