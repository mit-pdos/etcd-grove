# Review of the unified node-API candidate (candidates 1 + 2 + 3 + 4), round 4

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed. I ran one
`go test -race` of kvreconf's `TestMain_`, which builds outside the repository.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate.md`: candidate 1 as amended by
  candidates 2, 3 and 4. It is a design, not yet implemented, so no finding can be stale against `HEAD`. I looked
  hardest at candidate 4 (B1-B14) and at whether it fixes each finding of review 3.
- **Compared with**:
  - the node API at `eb59bb8d1b`, read with `git show`: `interface/Proof/go_etcd_io/raft/v3/InvNode.txt` and
    `interface/Spec/go_etcd_io/raft/v3/*.txt`;
  - the protocol model at `HEAD` `53a6e0085e` (U0 part 1): `Protocol/StepR.lean`, `Protocol/Ghost.lean`,
    `Protocol/GhostState.lean`, `InvApi.lean`.
- **Go**:
  - raft a2: `.lake/raft-fork`, `565c2bd`;
  - kvreconf: `examples/kvreconf/*.go`, read in full;
  - kv: `examples/kv/kv.go`, and kv's proof `StartCluster.lean`;
  - etcd's server: `server.go` at `a20f6760ff43`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md` (this worktree has no copy).
- **Not run**: lake build, `lean-check`, `tcb-report`.

## Summary

Candidate 4 settles most of review 3:
- one kind of start token per cluster (B1);
- a TaDa registry of proposals (B2);
- specs for stopped nodes (B3);
- read credits paid with receipts (B4);
- the server's frozen "no snapshots" fact (B7), `opsOf_noType2` (B8), `Advance`'s snapshot membership (B9);
- kvreconf's listed Go changes (B11).

Four of these fixes are wrong as written, and one fact about kvreconf's Go is new. **Five Tier-1 findings**:

1. **C1 (new; a Go bug in kvreconf, reproduced).** kvreconf reads and clones a message after giving it to
   `Node.Step`. raft keeps that message and writes to it: `m.From` in `node.run`, `m.To` when it forwards.
   - `go test -race -run TestMain_ ./kvreconf/` reports 3 data races: `proto.Clone` at `cluster.go:263` against
     the write at `node.go:388`.
   - `Step`'s spec takes the whole message (`stepIn`'s `msgPtsC ml 1 1`). The spec is right; the Go has to
     change.
   - raft's documentation of `Step` does not say it keeps the message. That is an undocumented contract, and
     it belongs in `issues/`.
2. **C2 (B1 broken).** The single `cluster_alloc` keeps the premise `BootLog ps ctxs boot`, which forces
   `boot.length = ps.length`. In the `boot = []` branch, `ps = elements c0.voters` is non-empty, so that branch
   can never be used. kv's `StartCluster` (today `cluster_alloc_static`, then `RestartNode`) has no allocation.
3. **C3 (B2 half fixed).** The registry is keyed by the entry's bytes. Two problems:
   - `ProposeConfChange`'s bytes are chosen inside raft: its update binds them, `∀∀ t bs, ⌜MarshalsConfChange
     (some o) bs⌝`, and `MarshalsConfChange` is a decoding relation (`CCModel.lean:240-243`). The client cannot
     register them before the call.
   - `sentMsg_prop` gives no entry type. kvreconf panics on a conf entry that does not decode (`kv.go:438-447`),
     so it cannot build the update for a copy without knowing the type.
4. **C4 (B3 false of Go).** The stopped specs promise `ErrStopped`. Go's `select` may also return `ctx.Err()`
   when the context is done (`node.go:515-541`), and `Step` of a local message type returns `nil`
   (`node.go:480-483`).
5. **C5 (review 3's B5 still open).** At `HEAD` the model still forbids an `ApplyConfChange` after a concurrent
   restore. `StepR.applyConf` needs `r.snap = false`, and `snapRestore` sets `cidx := m.index`
   (`53a6e0085e:Protocol/StepR.lean:309, 410`). `ApplyConfChange.spec` is unprovable until U0 changes them.
   "Told to U0" is a plan, not a fix. The candidate should list it as a prerequisite.

**Tier 2**:
- B4's receipts beside the allocation's `2^64 - 2` credits break the bound (C6);
- B6's `noTransfer` is unspecified, and the shape obligation includes a `Panicf` (C7);
- the joiner's admission is not settled (C8);
- the burden B2 puts on clients that never duplicate (C9).

**Tier 3**: text and small gaps (C10-C14).

**Go defects**: C1's race in kvreconf (this repository's example code), with a raft documentation gap behind it.
Neither is filed; this review is read-only.

---

## Review 3's findings: fixed?

| review 3 | candidate 4 | status at this round |
|---|---|---|
| B1 two start tokens; `c0` not tied to the peers | B1 | **Half fixed.** One kind per cluster, and `boot ≠ [] → c0 = simple ps` is stated. But the `boot = []` branch contradicts `BootLog` (C2). Learners of `c0` get no token (C12) |
| B2 no witness of a duplicated `MsgProp`'s entries | B2 | **Half fixed.** Normal entries are covered once the type is given. Conf entries cannot be registered by their bytes (C3). `ownProposals γ ∅` is not in the allocation, and the elem law is not stated (C12) |
| B3 post-`Stop` preconditions | B3 | **Fixed in substance.** Sound: `nil` from `ApplyConfChange` means "not applied" (`node.go:400-433`, `449-450`, `562-573`). The stopped answers are misstated (C4). The `ApplyConfChange` stopped spec needs the change's ownership (C13) |
| B4 finite read credits | B4 | **Plausible, not finished.** `⧗1 ⊢ readCredit` looks provable (C6). The allocation's `readCredits γ (2^64-2)` must then shrink or go. The fallback's arithmetic is wrong |
| B5 a2 window outside the model | B5 "told to U0" | **Open** at `HEAD` (C5) |
| B6 shape law obligation; the server pays | B6 | **Acknowledged.** The `noTransfer` alternative is unspecified (C7) |
| B7 server's no-snapshot facts | B7 | **Fixed.** `snapsNone_freeze` is sound: a snapshot of index 0 needs no certificate (`MemoryStorage__Snapshot.txt`: `Index' = 0 ∨ memStorCert`) |
| B8 `opsOf`'s signature | B8 | **Fixed** (`opsOf_noType2`). `committed_type2` still names no predicate (C14) |
| B9 `Advance` snapshot membership | B9 | **Fixed** |
| B10 joiner provability | "U4 proves or refutes it first" | **Open, deferred** (C8) |
| B11 kvreconf Go: `r.cs`, one `Storage` | B11 | **Fixed.** Both changes are listed. C1 adds one |
| B12 stale text | B12-B13 | **Partly fixed.** Q-A and Q-B are still under "Open questions"; candidate 1's `transfer` flag is still in `cluster_alloc` (C14). `SnapListsOk` does include "ids nonzero": `CSWf` (`Protocol/Model.lean:187`). Review 3's B12 was wrong on that point |
| B13 workload note; `bootedCluster` | B13 | **Fixed** (text) |
| B14 `γ.rule` departure recorded | B14 | **Fixed** (promised in `notes/decisions.md`) |

---

## Findings, ranked

### Tier 1

#### C1. kvreconf touches a message after `Step` takes it: a data race, reproduced (Go bug; kvreconf excluded)

**Principle**: *Sound* and *Complete*. The spec of `Step` is right; kvreconf's Go breaks it.

**Evidence**
- `Cluster.deliver` steps `m`, then clones it for the duplicate: `c.step(src, dst, m)`, then
  `c.step(src, dst, proto.Clone(m))` (`cluster.go:260-264`).
- `Cluster.step` reads `m.GetType()` after `Step` returns (`cluster.go:270-276`). On `DeadlineExceeded`,
  `dropped` reads `m.GetTo()` and `m.GetType()` (`cluster.go:272-273, 287-292`).
- raft keeps the pointer and writes to it:
  - `node.run` writes `m.From = new(r.id)` for every proposal taken from `propc` (`node.go:386-388`), including
    one stepped in from the network;
  - `stepFollower` writes `m.To = new(r.lead)` and sends the same pointer when it forwards a `MsgProp`,
    `MsgTransferLeader` or `MsgReadIndex` (`raft.go:1743, 1762, 1784`);
  - `send` writes `m.From`/`m.Term` (`raft.go:515-544`);
  - `stepLeader` replaces a refused conf entry in `m.Entries` (`raft.go:1359`).
- `Step` returns as soon as `run` has received the message (`node.go:514-541`). Nothing orders kvreconf's later
  reads before `run`'s writes.
- **Reproduced**: from `examples/`, `go test -race -count=1 -run TestMain_ ./kvreconf/` reports `race detected
  during execution of test`, with 3 data races. The first is a write at `node.go:388` (`node.run`) against an
  earlier read in `proto.Clone`, called from `kvreconf.(*Cluster).deliver` at `cluster.go:263`, on `Main`'s path.
- Today's `node.Step.spec` takes `stepIn γ N id ml`, which holds `msgPtsC ml (DFrac.own 1) (DFrac.own 1)`
  (`InvNode.txt`, `stepIn_intro`), and gives nothing back. So even the race-free reads of `m.Type` after
  `Step`, and the `DeadlineExceeded` path where raft never took `m`, are outside the spec.

**Caller**: kvreconf: one duplicate in 32 delivered messages, and every snapshot's `ReportSnapshot`.

**Restatement.** This is a kvreconf Go change, to add to the candidate's list (B11):

```go
func (c *Cluster) deliver(src *Replica, m *pb.Message) {
	...
	var dup *pb.Message
	if oneIn(32) { dup = proto.Clone(m).(*pb.Message) }   // before m is given away
	c.step(src, dst, m)
	if dup != nil { c.Stats.add(&c.Stats.Duplicated); c.step(src, dst, dup) }
}
func (c *Cluster) step(src, dst *Replica, m *pb.Message) {
	typ, to := m.GetType(), m.GetTo()                     // read before Step
	... err := dst.node.Step(ctx, m) ...
	if err == context.DeadlineExceeded { c.droppedTo(src, to, typ); return }
	if typ == pb.MsgSnap { ... src.node.ReportSnapshot(to, ...) }
}
```

Keep `Step`'s spec as it is: it takes the message for good.

Also record raft's documentation gap: `Node.Step` (`node.go:155`: "Step advances the state machine using the
given message") does not say that raft keeps `*pb.Message` and mutates it after `Step` returns. Messages became
pointers with protobuf-go v2. This is a precondition the code needs and the API does not state, so per CLAUDE.md
it is an `issues/` entry (`upstream: unchecked`). The reproduction is the `-race` run above.

#### C2. The `boot = []` branch of `cluster_alloc` cannot be used: `BootLog` forces `boot.length = ps.length` (B1 broken; kv has no allocation)

**Principle**: *Complete*: every caller can establish the precondition.

**Evidence**
- B1 keeps candidate 1's premises, `BootLog ps ctxs boot` among them, and adds `boot = [] → ps = elements
  c0.voters`.
- `BootLog ps ctxs boot := boot.length = ps.length ∧ …` (`NodeApiVocab.lean:65-70`).
- `c0.voters ≠ ∅` (candidate 1, and `CSWf`'s `v ≠ []`), so `ps ≠ []`.
- With `boot = []` the premises are therefore contradictory, and no `nodeRestartBoot` is ever handed out.

**Caller**: kv. `StartCluster.lean:231` allocates with `cluster_alloc_static` and starts every voter with
`RestartNode` from `{1,2,3}` (`examples/kv/kv.go:57-72`). Under candidate 4, kv has no allocation law. A
reconfiguring client that starts from an `InitialState` (etcd's restart path) is in the same position.

**Restatement.** Either make `BootLog` conditional, or keep two allocation laws over the one `isCluster`.
Both are instances of the same predicate, not two families.

```lean
theorem cluster_alloc … :
    c0.Valid → rule.Ok →
    (boot ≠ [] → BootLog ps ctxs boot ∧ c0 = Membership.simple (listToSet ps)) →
    (boot = [] → listToSet ps = c0.ids ∧ ps.Nodup) → …
    ={E}=∗ ∃ γ, … ∗ joinAuth γ c0.ids ∗
      (if boot = [] then [∗list] id ∈ ps, nodeRestartBoot γ N id
       else [∗list] id ∈ ps, nodeBoot γ N ps ctxs id)
```

Here `ps` lists `c0.ids`, learners included (C12).

#### C3. The proposal registry is keyed by bytes the client does not know for a conf change, and loses the entry type (B2 half fixed)

**Principle**: *Complete* for kvreconf; *Every premise has a source the client sees*.

**Evidence**
- B2: `ownProposals γ P` with `P : GSet (List w8)`. `Propose` and `ProposeConfChange` take `proposalReg γ data`,
  and `sentMsg_prop : MsgProp → sentMsg ⊢ [∗list] e ∈ st.ents, proposalReg γ e.data`.
- **Conf changes.** The client never sees the bytes of its own conf change:
  - `ProposeConfChange.spec`'s update is `<{ ∀∀ t bs, ⌜MarshalsConfChange (some o) bs⌝ ∗ ownCommittedOps γ (ops
    ++ [⟨t, confChangeEntryType (some o), bs⟩]) … }>` (`node__ProposeConfChange.txt`);
  - `MarshalsConfChange (some (.v1 m)) bs := ccDecodeV1 bs = some m` (`CCModel.lean:240-243`) is a relation, and
    infinitely many `bs` decode to one change;
  - `ProposeConfChange` marshals inside raft (`node.go:487-501`).

  So the client cannot register "`data`" before the call: it does not know it, and a finite `GSet` cannot hold
  every encoding.
- **The type.** kvreconf's invariant must exclude a committed `EntryConfChange`/`EntryConfChangeV2` whose data
  does not unmarshal, because `applyEntry` panics on one (`kv.go:437-447`). A registered byte string that comes
  back under another type is outside what the client can account for. Op encodings and protobuf encodings can
  also coincide, since the client chooses op ids freely (`kv.go:69-76`). `proposalReg γ e.data` alone does not
  let the client build the update `ops ++ [⟨t, e.type, e.data⟩]`.

**Caller**: kvreconf:
- a duplicated forwarded `MsgProp` of an operation (`cluster.go:261`, `kv.go:546`): fixable with the type;
- of a conf change (`reconf.go:90`): not coverable as stated.

**Restatement.** Split by type. Only normal entries need the client's registry; raft proves the conf-entry fact
itself, because it only sends what `ProposeConfChange` built.

```lean
theorem sentMsg_prop γ N src st : st.msg.Type' = MsgProp → sentMsg γ N src st ⊢
    [∗list] e ∈ st.ents,
      (⌜e.type = W32 0⌝ ∗ proposalReg γ e.data) ∨
      ⌜∃ o, MarshalsConfChange (some o) e.data ∧ e.type = confChangeEntryType (some o)⌝
-- Propose takes proposalReg γ data; ProposeConfChange takes no registration.
```

`ProposeConfChange` then needs no `proposalReg` premise. Also correct the B2 parenthetical: every copy's update,
including the original's, is the same generic one ("linearize if not yet applied, else nothing"). The client
cannot reserve "the update of its first commit" in advance.

#### C4. The stopped specs' answers are false of Go (B3)

**Principle**: *Sound*; *the postcondition says what the caller inspects*.

**Evidence**
- `stepWithWaitOption`'s `select` has a `<-ctx.Done()` arm beside `<-n.done` (`node.go:515-541`). After `Stop`,
  a context already done can return `ctx.Err()`; Go picks among ready arms at random.
- This applies to `Propose`, `ProposeConfChange`, `Step`, `ReadIndex`, `Campaign` and `ForgetLeader`.
- `Step` of a local message type (`IsLocalMsg ∧ ¬IsLocalMsgTarget`) returns `nil` before any `select`
  (`node.go:480-483`).

**Callers**:
- kvreconf's `step` tests `err == context.DeadlineExceeded` (`cluster.go:272`);
- `propose` loops on `Propose(...) != nil && ctx.Err() == nil` (`kv.go:546`).

**Restatement.** The stopped post is today's error disjunction with the success disjunct removed:
- `Propose`/`ReadIndex`/`Campaign`/`ForgetLeader`: `errStopped err ∨ ctxErr cd err`;
- `Step`: that disjunction, or `err = nil` when the message is of a local type;
- `ProposeConfChange`: `nodeErr cd err` with the change's ownership returned;
- `Advance`/`Tick`/`Report*`/`TransferLeadership`: unit;
- `ApplyConfChange`: `null`;
- `Status`: `Status{}`.

#### C5. The a2 window is still outside the model at `HEAD` (review 3's B5; `ApplyConfChange.spec` unprovable until U0 finishes)

**Principle**: *Sound/provable*.

**Evidence** (`53a6e0085e:Proof/go_etcd_io/raft/v3/Protocol/StepR.lean`):
- `snapRestore` keeps `cfg` but sets `cidx := uint.nat m.index` (`:309`);
- `applyConf` requires `r.snap = false` and `r.cidx ≤ k` (`:410-411`);
- U0 part 1 moved only the switch of the configuration to `applySnap` (`:403-407`).
- So an `ApplyConfChange` of an earlier `Ready`'s entry after a concurrent `Step(MsgSnap)` (kvreconf:
  `kv.go:470` against `cluster.go:270`) is not a model step.
- Go a2 applies such a change to the old configuration, and the candidate's spec promises exactly that.

**What a2 makes easy, checked**: in the window the node cannot campaign. `promotable` checks
`hasNextOrInProgressSnapshot` (the docstring of `Spec/.../raft__hasUnappliedConfChanges.lean`, `raft.go:997`).
Without that check, `hasUnappliedConfChanges` would `scan` below the restored first index and `Panicf`
(`raft.go:1027-1036`, `log.go:551-558`). So the window node is a follower whose stale configuration only weighs
its own votes in other nodes' tallies, and the model change is the one review 3 stated:
- `snapRestore` leaves `cidx`;
- `applyConf` is allowed with `snap` set, on the pre-restore full log;
- `applySnap` sets `cidx`.

**Restatement**: list it as `ApplyConfChange.spec`'s prerequisite, not as "told to U0".

### Tier 2

#### C6. Read credits from receipts beside the allocation's `2^64 - 2` (B4)

**Principle**: *Sound/provable*; *no constant whose reason you do not know*.

**Evidence**
- The protocol's read credits are an `Auth Nat` with `B < 2^64 - 1` (`GhostState.lean:1380-1388`), used as
  `rdCred_bound` at `Refinement.lean:3220`.
- Tick credits are receipts (`InvApi.lean:2789-2792`), and `⧗ n ⊢ ⌜n < receiptBound⌝`
  (`Perennial/GooseLang/Receipts.lean:262`).
- So `readCredit := ⧗ 1` is provable, with `receiptBound ≤ 2^64 - 2`, which `cluster_alloc` already assumes.
  Every receipt is a distinct step, so ticks and reads can share the bound.
- But B1's `cluster_alloc` still hands out `readCredits γ (2^64 - 2)`. Credits from both sources sum past
  `2^64 - 1`, so `readCredit_receipt` and the allocation cannot both hold with one bound.

**Callers**: kvreconf (receipts); kv and the server (they split `2^48` from the allocation today:
`examples/common/Defs.lean:187`, `SrvRaftLog.lean:1572`).

**Restatement**:
- define `readCredit γ := ⧗ 1` (sealed), with `readCredit_receipt : ⧗ 1 ⊢ readCredit γ`;
- drop `readCredits` from `cluster_alloc` and migrate kv's and the server's reads to receipts, one per
  `ReadIndex` call;
- or keep both, and allocate `readCredits γ (2^64 - 2 - receiptBound GF)`.

The fallback ("at most `2^62` tries per call") does not bound the total: `Main` makes up to 400 reads
(`check.go:116-127`). If the fallback is kept, state a total bound.

#### C7. B6: `noTransfer` is unspecified, and the shape obligation includes a reachable-looking `Panicf`

**Principle**: *Faithful to concurrency* (a once-only use needs a token); *every premise has a source*.

**Evidence**
- `noTransfer γ` is "given at allocation to a client that never calls `TransferLeadership`". A persistent fact
  is only sound if `TransferLeadership.spec` then takes something `noTransfer` refutes. That is the mode token
  A9 removed (`leaderTransferOn`), back without a statement.
- The server uses `leaderTransferOff` at `InvBuild.lean:164`, `NewServer.lean:1134` and `SrvRaftLog.lean:648`.
  Its Go does call `TransferLeadership` (`server.go:1284`, `1305`), on paths outside the proof's scope.
- The obligation "`SentMsgShape` in every cluster" also covers forwarded `MsgTransferLeader`:
  - a follower forwards one with `m.To = r.lead; r.send(m)`, and `send` stamps `m.Term` (`raft.go:1784`,
    `541-544`);
  - if a node at that term were a follower with a leader and forwarded it again, `send` would `Panicf`, because
    "term should not be set" (`raft.go:534-536`).
  - I argue it is unreachable: the only leader of a term is the node the forwarder knew, and a leader that steps
    down at its term has `lead = None`. But it is a protocol invariant to prove in U7, not a shape check.
- `SentMsgShape` is not defined anywhere; today's predicate is `SentMsgOk`.

**Restatement**:
- either keep one exclusive `transferToken γ` from the allocation, which `TransferLeadership` takes and
  `noTransfer` refutes;
- or drop `noTransfer` and have the server pay a receipt per `Step`.

List "a stamped `MsgTransferLeader` at term `T` is addressed to `T`'s leader" among U7's obligations.

#### C8. The joiner's admission is deferred, not settled (review 3's B10)

**Principle**: *Sound/provable*.

**Uncertain.** In Go the joiner is sound: it is not promotable (`id ∉ c0.ids`, `raft.go:997-1000`); its votes
count only for candidates whose configuration already contains it, so their logs hold the bootstrap entries; and
an empty log at configuration `c0` is the fold of `[]`. The model does not yet show that `RInv` admits a node with
an empty log and term 0 beside founders whose ghost log starts with the bootstrap entries. Keep `nodeJoin` marked
"pending U4".

#### C9. B2 makes every proposer thread `ownProposals` (caller burden for the server and kv)

**Principle**: *Do not make callers thread a resource only the proof's bookkeeping needs*; caller burden.

**Evidence**
- `Propose` now needs `proposalReg γ data`, so the server and kv, which never duplicate, must keep
  `ownProposals` in an invariant and register before each `Propose`.
- raft's proof only passes `proposalReg` through `sentMsg`.

**Restatement**: a persistent "register everything" law for a client that does not care, for example
`proposals_all : ownProposals γ ∅ ==∗ □ ∀ d, proposalReg γ d`. It is sound because `proposalReg` asserts
nothing raft relies on. A client that never duplicates then never mentions the registry again.

### Tier 3

- **C10. `joinAuth γ (listToSet ps ∪ c0.ids)` with `ps = elements c0.voters`.** Learners of `c0` get neither a
  `nodeRestartBoot` nor a `nodeJoin`, since `c0.ids` is already in `U`. Hand out `nodeRestartBoot` for
  `c0.ids` (C2's restatement).
- **C11. F9's law "`Restore` of `confStateOf m` is `m`".**
  - It must hold for every `cs` with `confStateIs cs m`. kvreconf's `r.cs` comes from `ApplyConfChange` (lists in
    raft's order), from the snapshot's `ConfState` (`kv.go:410`), or from Go-built `c0` lists.
  - `validConf` restores whatever it is given (`kv.go:219-239`).
- **C12. The allocation omits `ownProposals γ ∅`, and the law `proposals_elem : ownProposals γ P ∗ proposalReg γ
  d ⊢ ⌜d ∈ P⌝` is not stated.** B2 says only "(persistent, `d ∈ P`)".
- **C13. The stopped spec of `ApplyConfChange`** must take and return `ownConfChangeI c dq (some o)`, because
  `cc.AsV2()` reads it before the `select` (`node.go:562-565`).
- **C14. Stale text.**
  - "Open questions" still lists Q-A and Q-B, both answered.
  - Candidate 1's `cluster_alloc` still has `(transfer : Bool)`, `leaderTransferOn/Off` and the `[∗set] id ∈
    c0.ids, nodeRestartBoot` conjunct. Rewrite the statement once with B1 and A9 folded in, rather than leaving
    it to supersession.
  - `committed_type2`'s "(∃ o, `e.data` marshals a client `ConfChangeV2` o proposed)" still names no predicate
    (review 3's B8). With C3 it can be "the entry is in `opsOf` at its position, or `RaftLeave`".

---

## What is good

- **B1's shape.** One kind of start per cluster, and `boot ≠ [] → c0 = simple ps` stated. This closes review 3's
  divergence: a `StartNode` founder's committed-by-fiat bootstrap entries (`bootstrap.go:59-77`) never meet a
  `RestartNode` founder at term 1.
- **B2's direction.** A client-owned registry registered before `Propose` is the right TaDa shape. A witness in
  `Propose`'s post would come too late: the forwarded copy can reach the client's transport before `Propose`
  returns (`node.go:514-541`, then `run`'s `Ready`).
- **B3 is sound.**
  - `ApplyConfChange` returns `nil` only when `done` was closed before `run` took the change. `run` blocks on
    `confstatec` once it has taken it, and only `run` closes `done` (`node.go:400-433`, `449-450`, `562-573`).
  - "Not applied" with `nodeConfig` unchanged is therefore right.
  - The second spec is a case split on the node's state, not a disjunction of alternative specs.
- **B4's direction.** Receipts remove the finite pool. The pieces exist (`receipt_lt`, `tickCredit` is `⧗`).
- **B7.** `snapsNone_freeze` is a TaDa instance and keeps the server's facts pure. Index-0 snapshots carry no
  certificate, so `noSnapsEver ∗ snapshotCert ⊢ False` does not contradict the storage contract.
- **B8, B9** are as review 3 asked. B9's `confStateIs` matches kvreconf's `install` (`kv.go:410-415`).
- **B11** lists kvreconf's Go changes for `r.cs` and the founder/newcomer `Storage`.
- **B13** is right that `SnapListsOk` includes nonzero ids, through `CSWf` (`Model.lean:185-190`).

## kvreconf's Go still excluded under the amended candidate

| behaviour | where | excluded by | finding |
|---|---|---|---|
| `proto.Clone(m)` of a stepped message for the duplicate (a data race); reading `m`'s type/to after `Step` | `cluster.go:260-264, 270-292` | `Step` takes the message (correct); **Go change needed** | C1 |
| a duplicated forwarded `MsgProp` of a conf change | `reconf.go:90`, `cluster.go:261` | registry by bytes (C3) | C3 |
| a duplicated forwarded `MsgProp` of an operation | `kv.go:546`, `cluster.go:261` | covered once `sentMsg_prop` gives the type | C3 |
| `ApplyConfChange` of an earlier `Ready`'s entry after a concurrent restore | `kv.go:470` vs `cluster.go:270` | the model at `HEAD` | C5 |
| a joiner (`startNew`) | `cluster.go:166-178` | U4 (uncertain); Go changes listed (B11) | C8 |
| unbounded `Read` retries; duplicated `MsgReadIndex` | `cluster.go:325-333, 261` | covered if `readCredit := ⧗1` (C6) | C6 |
| forwarded `MsgTransferLeader`; duplicated `MsgTimeoutNow` | `reconf.go:104`, `cluster.go:261` | covered once U7's shape obligation is proved | C7 |
| calls after `Stop` (`r.cs = nil`, then `Advance`, delayed `Step`s) | `kv.go:304-307, 461-473, 353` | covered by B3, with C4's answers | C4 |

**Not excluded**:
- snapshots between applied entries, and compaction (`kv.go:348-358, 389-404`);
- rejected and unserialized conf changes;
- joint configurations and automatic leaves;
- `Campaign`, `ForgetLeader` and `Status().Lead`;
- `Storage.Snapshot`'s `ErrSnapshotTemporarilyUnavailable` (F11).

## Per target

- **Allocation** (`cluster_alloc`, the start tokens, `joinAuth`): C2, C10, C12; C6 (its `readCredits`); C14.
- **Proposals** (`Propose`/`ProposeConfChange`/`sentMsg_prop`/`msgCredits_prop`): C3, C9, C12.
- **Stopped nodes** (`Stop`, the second specs): C4, C13.
- **`ApplyConfChange.spec`**: C5 (the model). The statement itself is right.
- **Reads** (`readCredit_receipt`): C6.
- **The shape law and `noTransfer`**: C7.
- **The joiner**: C8.
- **Snapshots, `Advance`, `nodeConfig_*`, `ConfRule`, `opsOf`**: C11 and C14 only.
- **`Step.spec`**: no change; kvreconf's Go must change (C1).

## Ranking (most in need of revision first)

1. `cluster_alloc` (C2, then C10, C12, C14).
2. The proposal registry and `sentMsg_prop` (C3, then C9).
3. kvreconf's Go: the race (C1). Not a spec change, but the candidate's list of Go changes must include it.
4. The stopped specs' answers (C4, C13).
5. The model prerequisite of `ApplyConfChange` (C5).
6. Read credits (C6).
7. `noTransfer` and the shape obligation (C7); the joiner (C8).
8. Text (C11, C14).

## Go defects

- **kvreconf (this repository's example code): a data race**, reproduced with `go test -race -count=1 -run
  TestMain_ ./kvreconf/` from `examples/` (3 races; `cluster.go:263` against `node.go:388`). The fix is in C1.
  Not recorded anywhere yet (`grep` of `issues/` and `notes/`). As a bug in this repository's own code it
  belongs in `notes/`, or as a fix with the kvreconf changes.
- **raft (documentation)**: `Node.Step` keeps and mutates the `*pb.Message` it is given (`node.go:388`;
  `raft.go:516, 543, 1359, 1743, 1762, 1784`), and its documentation (`node.go:155`) does not say so. This is a
  precondition the API does not state, so it belongs in `issues/` (`upstream: unchecked`), with the `-race` run
  as its reproduction. **Not filed**: this review is read-only.
- No new raft code defect.
  - The `hasUnappliedConfChanges` scan below a restored snapshot would panic, but `promotable` guards it.
  - The forwarded stamped `MsgTransferLeader` `Panicf` (C7) looks unreachable.

## Uncertain

1. **C6**: that `rdCred_bound`'s use at `Refinement.lean:3220` can take a receipt bound instead. I checked the
   bound's shape, not the proof.
2. **C7**: that the re-forward `Panicf` is unreachable. I argued it from Go; it is not proved.
3. **C8**: the joiner beside bootstrap founders in `RInv`.
4. **C5**: U0's next part may already be in progress. The working tree's uncommitted changes touch
   `stepFollower`, `stepCandidate` and `handleSnapshot`, not `StepR.lean`.
5. **Not checked**: F9-F11, F13 and F14, which are still promises rather than statements.
