# Raft's node API for durable clients (2026-10-31)

**Kind:** an API extension one spec must serve two kinds of client with. One client keeps nothing
durable (kvreconf, kv, etcd's server as proved). The other writes raft's state to disk and crashes
and restarts (`examples/kvdurable`; later etcd with its WAL).

**Principles it shows:**
- A commit point the client chooses is an update the library hands out.
- The client-owned state is only the part its choice is about.
- No bookkeeping handles.
- Resolve open questions with few new predicates and local specs.
- Every soundness claim is tested against the code by an independent reviewer.

The full history is in `/home/ubuntu/spec-scratch/raft-durability/` (candidates 1-11 and the
`spec-reviewer` agent's nine reviews; not committed).

## First version (candidate 1, the author's)

The client owns `nodeDisk γ N id ι D`, the durable state of node `id` bound to an incarnation `ι`
of an abstract type `NodeInc`. Each Ready hands out:
- an exclusive write obligation `readyWrite γ N ι b p δ`;
- receipts `batchWritten`/`batchSafe`;
- gated messages `readyMsgs`, released by `readyMsgs_send` given the receipt or role leader.

`Advance` takes `batchSafe`. `RestartNode` starts from a persistent `restartable D` and a rebind of
the incarnation. Per-incarnation keys use `nodeInc n ι`. About ten new predicates.

Reviews 1-3 found real defects: a stale or unbound incarnation could win with delayed vote grants,
`Applied` above the snapshot was unsafe, and the per-node keys were unsound after a restart. They
were repaired into candidate 4, still in this vocabulary.

## Critique 1 (the user, on candidate 4)

> The change should be just that Ready returns an AU that the client can fire when they want to
> enter the new raft state. If they want durability, they fire at the durable state's commit point;
> if not, whenever. The permission to send messages would be part of the AU's postcondition. Things
> like `nodeInc` seem bad, and there should be no `nodeDisk` in the raft library, since the user may
> choose not to have a disk.

**What it changed:**
- The obligation, the receipts, the message gate and the write law became one update in the
  Ready's post, whose post is the permission to send.
- Nothing in raft is named after a disk.
- No incarnation type: the node object is the incarnation.

Principles: "A commit point the client chooses is an atomic update the library hands out"; "No
identification handles for the proof's bookkeeping".

## Critique 2 (the user's answers on candidate 5)

> Q1: The raftState should be just the durable parts, so there's no "restart" step, since the
> volatile parts aren't even there. Q2 (Advance takes the update's post): seems ok. Q3 (a storage
> not attached to a node needs no bounds): good.

**What it changed:** the client-owned `raftState γ id S` holds term, vote and the log from a base.
The volatile half stays inside raft, and a restart builds a fresh volatile half over the client's
state. Principle sharpened: the client-owned state is only the part its choice is about.

## Critique 3 (the user)

> Try to resolve all questions yourself by focusing on specs with as few new predicates introduced
> as possible and as much locality as possible. Once you've stabilized, come back to me.

**What it changed:** five more review rounds.
- Two attempts to drop a predicate were refuted with Go reproductions, and the predicates stayed:
  - two nodes of one id running at once both become leader of a term and report a false committed
    entry, so `nodeVacant` stayed;
  - a stopped node's update fired after a restart makes `Step` panic, so the updates take a
    `nodeRunning` fraction.
- The snapshot and compaction laws were removed altogether: the storage's business, not the
  durable state's.
- Review 8 found a real data race in the example: the client called `InitialState` while a node
  ran.
- The candidate was reported stable (candidate 11), and the user approved it ("prove these specs").

## The approved spec (candidate 11)

- **Predicates against the old API.**
  - New, sealed: `raftState γ id S` (exclusive), `nodeVacant γ id` (exclusive), `storFresh K`
    (exclusive).
  - Gone: `nodeFounder`, `nodeJoin`.
  - Re-keyed from the node id to a storage key `K`: `nodeAppliedLb`, `snapGiven`, `isStorage`,
    `memStorJ`, `storDL` (now sealed).
  - Generalized: `memStorFresh ms γs c sv` (a detached MemoryStorage).
- **The Ready.** The receive gives the physical resources and the committed-log facts as before,
  and two updates, both from the batch's start state `st.durable`:

  ```lean
  (∀ E q, ↑N ⊆ E → raftState γ id st.durable ∗ nodeRunning n γ N q ={E}=∗
     raftState γ id S' ∗ nodeRunning n γ N q ∗ nodeDriver n γ N st' ∗ msgs ∗ reads) ∗      -- enter
  □ (∀ E q, ↑N ⊆ E → raftState γ id st.durable ∗ nodeRunning n γ N q ={E}=∗
       raftState γ id st.durable ∗ nodeRunning n γ N q ∗ reads ∗ (⌜st'.role = StateLeader⌝ -∗ msgs))  -- check
  ```

  `Advance` is unchanged: it takes the driver, which only *enter* gives.
- **`RestartNode`** takes:
  - `nodeVacant`;
  - an AU over the client's `raftState` checking that the storage holds it;
  - a configuration point `a` with `confAt γ a m`;
  - `Applied ∈ {0} ∪ [base, commit]` with `Applied ≤ a ≤ commit`;
  - a `restartStorage` (detached, keyed by `K`, with a client frame).

  It posts the driver from `S`, `nodeConfig ⟨a, m⟩` and `nodeRunning n 1`. `Stop` gives
  `nodeVacant` back.
- **Scope restrictions:** `a ≤ commit`; a bootstrapped node restarts only once it holds the
  bootstrap entries; a MemoryStorage is attached once.

**The lesson for the author:** the author's first vocabulary followed its own proof's bookkeeping
(obligations, receipts, incarnations). The user's shape followed the client's view: one update to
fire when it enters a state, and nothing about how it stores it. It needed fewer predicates and
fewer laws, and every remaining predicate earned its place by a concrete counterexample.
