# Review 1 of candidate 15 (S1): proposals over duplicating networks (`propCredit`, `msgCredits_copy`)

Reviewed at `421683aded` (worktree `raft-spec-review`), read-only. Target:
`/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-propose-dup-spec.md`. I judged it within the user's
decision: a cluster-wide `dup` flag, one spec per function, no registry.

Note: `.claude/skills/spec/PRINCIPLES.md` and `examples/README.md` do not exist in this worktree
(`.claude/skills/` holds `spec-repair`, `proof-cleanup`, ... only). So I judged by CLAUDE.md, the
user's recorded spec principles (memory: observable state only, locality first) and the user's
conditions as the brief states them.

## Verdict

The design is sound, and it is about as local as the user's condition allows. The API has two
dup-conditional statements (`propCredit`, `msgCredits_copy`) and one pure allocation fact. Each
client can use it. Nothing in it needs a new axiom. Four things need fixing before it freezes:

- **Medium.** The `msgCredits_intro` it states is false at HEAD for `MsgReadIndex`, and kvreconf
  duplicates those too.
- **Medium.** It shows only one of the allocation laws that exist at HEAD.
- **Medium.** Its internal plan understates what bifurcates: firing and the index binding change,
  not only the ticket's representation.
- **Low.** kvreconf's persistent update must test the committed ops, not "applied". Plus some small
  cleanups: `propCredit_true` should become an unconditional `□ P ⊢ propCredit γ P`, and the
  automatic-leave paragraph is moot.

## What is good

- **Minimal API surface.** The only dup-conditional definition is `propCredit` (candidate l.45-49).
  The only dup-conditional law is `msgCredits_copy`. The flag is fixed at allocation (`⌜γ.dup =
  dup⌝`). One spec each for `Propose` and `ProposeConfChange`, no second family. `dup = false` gives
  back today's `node.Propose.spec` exactly (interface/Spec/go_etcd_io/raft/v3/node__Propose.txt:8-17).
- **Sound.** The analysis is below; in short, persistent tickets are harmless once the update they
  pay for is persistent:
  - Internally `msgCredits = rdCred (if ReadIndex then 1 else 0) ∗ stTks`
    (Proof/go_etcd_io/raft/v3/InvApi.lean:2086-2087).
  - `stTks` of a `MsgProp` is `[∗list] entTk` (ApiVocab.lean:441-442).
  - `entTk` is `emp` for a filler and `propTk` otherwise (Protocol/Ghost.lean:1315-1317).
  - `rdCred γ 0 = own (◯ 0)` is the unit, so it is persistent (Protocol/GhostState.lean:1405-1406,
    1421-1424).
  - So with persistent tickets, `msgCredits_copy` holds. A ticket is no longer needed to prevent
    double firing once the deposited update is `□`.
- **Matches the Go.** The cases that matter:
  - `stepFollower` forwards the stepped message itself (`m.To = new(r.lead); r.send(m)`,
    `.lake/go-src/raft/raft.go:1712-1721`). The candidate drops it, raft.go:1676.
  - `stepLeader` appends every entry of every copy (raft.go:1294-1352). It may replace a conf change
    with an empty normal entry in place (raft.go:1340). That entry is a filler: its ticket is dropped
    and the client's update never fires for that copy, which the spec allows.
  - kvreconf's `deliver` clones before stepping a duplicate (`examples/kvreconf/cluster.go:263-271`),
    so each copy has its own message ownership, as `stepIn_intro` needs. Its `msgPtsC` comes from
    `proto.Clone`'s spec (`Spec/google_golang_org/protobuf/proto/Clone.lean`).
- **Each client can use it:**
  - **The server.** Its network payload already separates one-shot from duplicable messages:
    `srvNet.once st := MsgReadIndex ∨ MsgProp`, with `dup` from `msgCredits_none`
    (Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBuild.lean:136-141). rafthttp delivers a POST at
    most once (notes/rafthttp-plan.md:53, 248-258), so `dup = false` is right for it.
  - **kv.** Steps each message once (examples/kv/cluster.go:123).
  - **kvreconf.** Retries a proposal with the same bytes (`kv.go:554-567`). It dedups on
    `applied[string(data)]`, where the data carries a fresh id (`kv.go:69-76`, `kv.go:503-526`,
    `cluster.go:314-325`). Its `applied` table is in its snapshots (`kv.go:196-200`). So the
    persistent "fire the client's update at the first committed occurrence" update is buildable
    from its invariant.
  - The building block exists: `□ AU` is already a client obligation for reads
    (`readCtx_commit_after`, interface/.../InvNode.txt:284-287).
- **Converting the update.** `api_propAu1` turns the API update into raft's `propAu1` using only the
  persistent `apiInv` (InvApi.lean:2551-2556). So `□ AU ⊢ □ propAu1` follows by `□`-introduction,
  with no new lemma.

## Findings

### F1 (medium): the stated `msgCredits_intro` is false at HEAD for `MsgReadIndex`, and kvreconf needs it

- **Principle.** A law is stated for the state it will be proved in, and an ordering dependency is
  explicit.
- **Evidence.**
  - Candidate l.28-30 and l.60-61: `msgCredits_intro : st.msg.Type' ≠ MsgProp → ⊢ |==> msgCredits γ N st`.
  - At HEAD a `MsgReadIndex`'s credit is `rdCred γ.raft 1` (InvApi.lean:2087). It cannot be minted:
    the authority `● B` sits in `rdCredInv` (GhostState.lean:1409-1410).
  - Today's laws exclude it (`msgCredits_none`, interface/.../InvNode.txt:367-368).
  - The removal is U7's planned, not-yet-done read-credit exchange (notes/decisions.md:25574-25581:
    "Read credits, not done").
- **Caller affected.** kvreconf: `deliver` duplicates every message type (cluster.go:263), and it
  uses `ReadIndex` (kv.go:597). So a forwarded `MsgReadIndex` copy needs this law. The server is
  unaffected (`once` covers `MsgReadIndex`).
- **Restatement.**
  - Until the exchange lands, keep today's two laws: `msgCredits_none` (≠ ReadIndex, ≠ Prop) and
    `msgCredits_snapshot`.
  - Write the candidate's `msgCredits_intro` as the form after the read-credit exchange, and say it
    depends on it.
  - Afterwards the server's `once` shrinks to `MsgProp` (InvBuild.lean:139).
- **Optional simplification.** Once `rdCred` leaves `msgCredits`, `msgCredits_copy` could drop its
  `MsgProp` premise: `γ.dup = true → msgCredits γ N st ⊢ □ msgCredits γ N st`. Every other type's
  credit is then `emp`. That gives one rule for a dup network's copies instead of a case on the
  type. It is still the only dup-conditional law.

### F2 (medium): every allocation law at HEAD must fix `γ.dup`, not only `cluster_alloc_dec`

- **Principle.** Clients must be able to use the spec: `propCredit_false` needs
  `⌜γ.dup = false⌝`, and only an allocation can give it.
- **Evidence.**
  - The candidate states one allocation law (l.38-42).
  - HEAD has three: `cluster_alloc` (InvNode.lean:292; interface InvNode.txt:117-123),
    `dynamicCluster_alloc` (InvNode.lean:671; InvNode.txt:289-296) and `cluster_alloc_dec`
    (InvNodeRule.txt:40-44).
  - The server allocates with `cluster_alloc` (NewServerAlloc.lean:216, NewServerAllocOn.lean:101).
  - kv's `StartCluster.lean:237` names `cluster_alloc_rule`, which no longer exists (kv awaits U10).
- **Callers affected.**
  - The server's `raftPropose_of_isNode` (NodeBridge.lean:300-318) calls `node.Propose.spec` and
    would need `⌜γ.dup = false⌝`. It holds only `rnEnvOk`, `rnIsNode` and `srvRaftLogInv`, so the
    fact must be added to a pure record such as `srvClusterOk`/`rnEnvOk`.
  - kv's `KV__do` and `KV__RemoveMember` likewise.
- **Restatement.**
  - `cluster_alloc` and `dynamicCluster_alloc` (until U9 deletes them) each add `⌜γ.dup = false⌝` to
    their post, with no new argument. Their clients stay as they are, apart from the rewrite at the
    call site.
  - `cluster_alloc_dec` (later the unified `cluster_alloc`) takes `(dup : Bool)` and gives
    `⌜γ.dup = dup⌝`.
  - Internally the flag must live in `RaftNames`, because `propTk`/`entTk` take `γ.raft`. It would
    sit beside `reNoSnap`/`reNoXfer`, with `γ.dup = γ.raft.reDup` in `NodeOk`/`clusterInv`, like the
    other mode flags.

### F3 (medium, provability / internal locality): firing and the index binding bifurcate, not only the ticket

- **Principle.** A feasibility claim should match the proof it commits to. The user's condition
  covers the internals too ("one proof").
- **Evidence.** The candidate (l.111-117) says only `ticket`'s representation depends on `dup`, plus
  `propCredit_elim` and `ticket ⊢ □ ticket`. At HEAD, three more things depend on the ticket being
  exclusive and consumed:
  - **The append.** It spends the ticket into a one-shot index record: `propTk` holds
    `dghostVar γt 1 none`, and `propTk_set` turns it into `propIdx γ d i` (Ghost.lean:1188-1213,
    used at Ghost.lean:1497 in `propData_stampTk`).
  - **The entry's data.** A committed entry's data includes `propIdx γ d e.Index'` (`entDataIs`,
    Ghost.lean:1232-1234).
  - **Firing.** `fire_one` finds *the* deposit whose ticket was spent at this index. It refutes
    "already fired" by comparing indices, then moves the slot from its update to `fired`
    (Protocol/LeaderCompleteness.lean:936-959; `depSlot`, GhostState.lean:1073-1075).

  With a persistent ticket none of this holds: one deposit is appended at several indices, so there
  is no one-shot `propIdx`, and `depSlot` must keep its `□ propAu1` after firing.
- **Caller affected.** Track A's estimate and the user's "one proof" condition. The API is
  unaffected.
- **Restatement of the internal plan.** It stays local, about six definitions and lemmas, all in
  `Protocol/Ghost.lean`, `Protocol/GhostState.lean` and `LeaderCompleteness.lean`:
  - `propTk γ d := if γ.reDup then depWit γ d else today's`, where
    `depWit γ d := ∃ p k γt, d ↪[reProps]□ p ∗ k ↪[p.2]□ γt`.
  - `entDataIs γ e (some d) := propDataIs ∗ (if γ.reDup then depWit γ d else propIdx γ d e.Index')`.
  - `propTk_set`'s dup case is the identity.
  - `depSlot`'s left disjunct is `propCredit (savedPred ∗ propAu1)`. In the dup case `fire_one`
    fires from `□` and keeps the slot, skipping the not-fired-before check.
  - `prop_deposit`/`node_propose_ghost` store `□ propAu1` when dup.
  - The 12 files that only carry `entTk` along (`grep -rl entTk`: node__run, InvNodeRun,
    Refinement, RawNode__Propose, ...) are unchanged, provided `entTk` stays a definition they do
    not unfold.

### F4 (low, client usability): kvreconf's update must test the committed ops, not "applied"

- **Evidence.** Candidate l.100: "if `op` is not applied, fire the client's update, else nothing".
  The update fires at commit, in `⊤ \ ↑N`, before any replica applies the entry.
- **Restatement.** "If `op` does not occur in `ops` (the committed ops the update opens), fire the
  client's update stored under `op`; else nothing."
  - `applyOp`'s `applied[o]` then agrees: it is a function of the applied prefix of the same log, and
    snapshots carry it (kv.go:196-200, 503-526). So the first committed occurrence is the
    linearization point and the first application.
  - The client's update lives in kvreconf's invariant, whose namespace must be disjoint from `N`.

### F5 (low): replace `propCredit_true` by an unconditional introduction law

- **Evidence.** `□ P ⊢ propCredit γ P` holds whatever `γ.dup` is. kvreconf gives `□ AU` at every
  `Propose`/`ProposeConfChange` (candidate l.97-104), so it does not need `γ.dup = true` there; it
  needs it only for `msgCredits_copy`.
- **Restatement.**
  - Add `propCredit_persistent : □ P ⊢ propCredit γ P` (no premise).
  - Keep `propCredit_false : γ.dup = false → propCredit γ P ⊣⊢ P`.
  - Drop `propCredit_true`, or keep it as derived.
  - The dup flag then appears in a client's proof only where its network copies a message.

### F6 (low, accuracy): the automatic-leave paragraph is moot

- **Evidence.** Candidate l.118-121 says raft gives `propCredit γ (AU id)` for its automatic leave.
  But the leave is an empty `ConfChangeV2`, i.e. a `Filler`, which "carries no ticket" and fires the
  standing `noopAu` (Ghost.lean:1143-1155 `Filler`; `entTk` is `emp`, Ghost.lean:1315-1317).
- **Restatement.** "The automatic leave is a filler: no ticket, no update; unchanged by `dup`."

### F7 (low, polish)

- **Empty data.** `Propose`'s update "never fires for `data = []`" (l.73). The wrapper drops it
  (node__Propose.lean:194-199). In a dup cluster, a client proposing empty data must still give
  `□ AU`. No client does this (kvreconf's ops are non-empty), so no change is needed; perhaps a doc
  line.
- **Decisions spec.** The candidate says it supersedes the decisions spec's proposal parts
  (l.3-7), but `notes/spec-first-study/raft-decisions-spec.md` mentions no proposals or credits
  (grep finds none). Name only candidate 12 §2/§3 (`raft-node-unified-candidate.md:187-192,
  232-236, 280-281`) and the parked plan entries (notes/raft-unified-plan.md:96-99, 217-224).
- **RaftWitness.** `RaftWitness/` has its own `node.Propose`/`ProposeConfChange` specs. The
  candidate should say they are left unchanged, which is fine: the part never imports the main
  raft.

## Answers to the open points

1. **Is wrapping the update in `propCredit` the most local form? Yes.**
   - Two specs (`AU`, `□ AU`) break "one spec per function".
   - A client-chosen modality buys a generality no client uses, and needs its own laws
     (elimination; persistence of the credit it pays for), which is more API.
   - A per-call choice (`AU ∨ □ AU`) fails: the network cannot tell from a sealed `msgCredits`
     which choice a message carries.
   - So a cluster-wide Bool is the least that works. Make `propCredit_persistent` (F5) its
     introduction law.
2. **`msgCredits_copy` sealed, or expose the per-entry `propCredit` in `readyRest`? Sealed.**
   Exposing it would put the internal update shape (`propAu1`'s `rLog`, its key) or the API update
   into `readyRest`, and a client's network would gain nothing from seeing it. After the read-credit
   exchange, consider the premise-free form (F1).
3. **Does any client need `sentMsg_prop`? No.**
   - It is not in HEAD's API at all (no match under `interface/`); it lives only in candidate 12 and
     the parked WIP ref.
   - kvreconf's conf-entry facts come from its own invariant and from `committed_confDecodes`.
   - Raft's own `stepLeader` needs the decoding of a stepped `MsgProp`'s conf entries (raft.go:1313,
     1318 panic on `Unmarshal` failure). It gets that from the internal `isRaftMsg`/`propDataIs`
     (`CCDecodes`, Ghost.lean:1232ff), which `sentMsg` already seals. Dropping it is right.

## Go code

No bug found. Behaviour the spec relies on:

- **Writes into the stepped message.** `stepLeader` writes into the stepped message's entries
  (raft.go:1340) and `stepFollower` writes its `To` (raft.go:1720). kvreconf clones per copy
  (cluster.go:229-231, 263-265). This is already recorded as a non-issue
  (`issues/nonissues/raft-step-writes-caller-message.md`, cited at cluster.go:275-276).
- **Empty `MsgProp` panic** (raft.go:1295-1297). Unreachable for a copy: every sent `MsgProp` has
  the entries of the `Propose` that made it.

## Ranking (one target)

1. **Candidate 15: revise before freezing.**
   - F1 and F2 change statements: the law as stated, and which allocations carry `dup`.
   - F3 changes the internal plan and its estimate.
   - F4-F7 are wording and a small law swap.
   - The design itself (cluster flag, `propCredit`, sealed `msgCredits_copy`, no registry) needs no
     change.

## Uncertain (not verified)

- That `□ AU` with kvreconf's invariant can be introduced (`iauintro` under `□` with only
  persistent hypotheses). The `readCtx_commit_after` precedent suggests it can, but I did not build
  it.
- The decision cluster's `opsOf` of a duplicated conf entry: whether a second commit of the same
  change records a second decision that kvreconf's `validConf` must reject. The candidate asserts
  kvreconf's invariant decides it; I did not check the `confDecide` laws against a repeated change.
- The Go source read is `/home/ubuntu/etcd-grove/.lake/go-src/raft` (the shared checkout). I did not
  confirm it is at the pinned `565c2bd`; the line numbers match the cases quoted.
