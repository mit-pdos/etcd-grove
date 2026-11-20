# backend-snapshot: proving `backend.backend.Snapshot` (retiring its axiom)

Branch `worktree-backend-snapshot-proof`, worktree `.claude/worktrees/backend-snapshot-proof`, off `lean`
`57d66952d9` (2026-11-20). The user's request: "get rid of the backend.Snapshot axiom; use the ideas from
SpecPlan to the degree they're helpful; if existing proofs must be redone, consider improving them".

## Where it starts

`backend.backend.Snapshot.wp_proof` is an axiom (`Proof/go_etcd_io/etcd/server/v3/storage/backend/
backend__Snapshot.lean`); the body is translated (S4b, `notes/bbolt-integration-plan.md`), and its three
companions (`snapshot.WriteTo/Size/Close`) are proved. S4b left two blockers:

1. `b.mu.RLock()` outside the batch lock needs a reader slot of `b.mu`; the constructor keeps only the
   batch lock's (`batchPhys`) and drops the others.
2. `DB.Begin(false)` outside the batch lock: bbolt's `Begin` takes an atomic update over `boltState γ q D`,
   but `ownDB` puts the whole `boltState γ 1 D` in the batch lock; and the spec's observation `Q` needs the
   caller's `R` with the batch lock's `W ∗ Pk` and ghost halves, which no thread holds at the `Begin`.

## What the callers need (why there is a `Q`)

The one proved caller is the leader's merged snapshot (`createMergedSnapshotMessage`, through mvcc's
`mvccImage_snapshot.law` and the server's `senderImage.law`): after `KV().Commit()`, the snapshot must be
the state at the applied index `ai` (`imageRestAt … i … D`, `dbImageA`). The apply thread knows it from
`R` (its state at `ai`) against the batch lock's `Pk` (the pre-commit hook's stored-index mirror) and the
lock's halves of the writer's contents (`hkOwn`, `rbOwn`, `fkdOwn`, `dlsOwn`, the view quarter): a pure
fact true of the writer's contents at every moment `R` is held. The writer's contents are the committed
data exactly at a commit; so `Q` holds of every image committed while `R` is held, which is what the
spec's `Q D` claims of the image `Begin` reads. A commit can land between `Snapshot`'s own `Commit()` and
its `Begin` (the `run` goroutine's periodic commit, a compaction batch), so the image need not be the one
the snapshot's own commit made.

## Decision: registered observations (commits help), SpecPlan's history not adopted for the client side

SpecPlan (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`) drops `Q`: the
snapshot is an image of a client-owned history no older than a prefix `L0` the caller names
(`beHistLb`), with a counted reader slot (`beRdToks γ 1`). It moves the observation into the client's
invariant over the history, so every commit must run a client update recording what its image means to
the client (`commitOk`). For etcd that is the same commit-time reasoning (the stored index, the tracked
buckets, the compaction's deleted entries), but owned by mvcc and the server: their invariants would
have to be rebuilt around a history (`KVStoreApi`, `KVStoreLaws`, `SnapSendBranch`, mvcc's API).

Registered observations keep the callers' contract (`backend.backend.Snapshot.spec`'s pre and post, but
for the reader slot below) and confine the change to the backend:
- the snapshotter registers its `R` and its observation wand (saved propositions,
  `Perennial/Ghost/SavedProp.lean`) in a backend invariant that also holds half of bbolt's
  `boltState`;
- every commit, at `Tx.Commit`'s linearization point (where it fires bbolt's atomic update, now by
  opening that invariant), holds `W ∗ Pk` and the lock's halves at the committed contents `S`, and
  applies each registered wand: the registration is armed with `Q S`;
- `Snapshot`'s own `Commit()` arms its registration even when nothing is pending (then the writer's
  contents are the committed data);
- at `Begin(false)`'s linearization point the snapshotter reads the invariant's committed `D` and its
  armed `Q D`, and takes its `R` back.

Taken from SpecPlan: the counted reader slot (below), and the backend's record of commits (the
invariant's committed image), which a later move to SpecPlan's history statement would reuse. Recorded
in the ledger (`notes/specs-only/ledger.md`).

## The reader slot of `b.mu`

`Snapshot` read-locks `b.mu` before bbolt's `Begin(false)` lends its `threadTok` to `mmaplock`, and
holds it past the `go` statement: one thread token cannot pay for both (Perennial's `ThreadPool`: two
copies at once need two tokens). Lock levels (`levelTok`) would need bbolt's pool at a fixed level (a
generic library tied to the server's level numbering, 0-4 taken). Per `notes/bounds-plan.md`, D2 (a)
(nested read locks across owners on one long-lived goroutine keep a counted slot), the backend's
constructor keeps `b.mu`'s other slots as a counted stock (`bmTok`), and `Snapshot` takes one and gives it
back; the server's apply thread holds one, delivered as the constructor's counted open shares are.

## Stages

- **B1** the commit point: `ownDB` at half of `boltState`, the backend's commit invariant (`cmtInv`,
  persistent in `isBackend`) with the other half; the commit glue (`batchTx__commit.lean`) and the
  begin glue (`backend__unsafeBegin.lean`) fire bbolt's updates through it; `Close` and `New`.
- **B2** the registry: registrations, arming at commits and at a no-op `Commit`; the lock's halves at
  the linearization point (`unsafeCommit`, the `Unlock` window).
- **B3** the `b.mu` stock (`bmTok`), its delivery to the apply thread.
- **B4** `Snapshot` proved; `Link.lean` regenerated; the axiom gone; trust base, collections,
  interfaces, STATUS.

## Log

- 2026-11-20: scope and decision (this note).
- 2026-11-20, **B1 done** (`4d67548d5b`): `ownDB` holds half of `boltState`, `cmtInv` (in `isBackend`
  and `isBackendNH`) the other half (`dbHalf`) or, once stopped, `bStopped`. The commit glue
  (`batchTx__commit.lean`) fires bbolt's update by opening `cmtInv` (the lock's quarter of the open
  flag refutes the stopped case); a stop's commit (paid with `stopPay`, `payIn`'s stop case) stops the
  backend at its commit point and takes the half out (`bDBOutG`'s `dbHalf`, for `Close`).
  `batchTx.commit.spec` changed (the quarter, the stop's payment); `unsafeCommit`, `Close`,
  `backend_init`, `newBackend` adjusted. The backend's `Link` builds.
- 2026-11-20, B2 start: `sessWf` gains `st.pend = W64 0 → st.S = st.C` (every write counts in `pending`;
  `pend_add_one_ne`): what lets `Snapshot`'s own `Commit` arm its registration when nothing is
  pending. Positional uses fixed (`BatchLemmas`, `WritebackLemmas`, `CommitLemmas`, `Unlock`,
  `st0_freeOk`).

## Open: arming at an `Unlock` window's commit (B2)

A registration must be armed for the image `S` *before* the commit point (a snapshotter's `Begin` may
come right after it), from the lock's inputs at `S` (`bStopView γ P W Pk S`'s: `W`, `Pk`, the view
quarter with the deleted entries, `hkOwn`, `rbOwn`, `fkdOwn`). For an ordinary commit they are all in
`unsafeCommit`'s context before `batchTx.commit` (`thinV_trans`, `dlVd_of_dlsOk`). In an `Unlock`'s
commit window (`win = true`) the lock's view quarter is at the physical view (`batchViewQ0`, only
`dlsS`), and only the commit's close (`rtRes_cm_close`, after `tx.Commit`) moves `γ.view` to the
session's logical view `L'`: before the commit point the inputs at `S` do not exist (the S4b note's
"`dlsW` exemption"). Options:
1. Move the window's view update (`γ.view` to `L'`) to the commit point: its fractions are reachable
   there (the lock's quarter, `rtRes`'s quarter, held whole by the committer, the clients' half
   deposited in `cacheInv`), but `cacheInv`'s use of the deposited half and `rtRes_cm_close` change.
2. Arm after the commit, and make a snapshotter that `Begin`s inside an unarmed window wait or retry:
   not Go's behavior (`Snapshot` does not retry), so no.
3. SpecPlan's history statement for the snapshot (the client reasons about images): moves the same
   question to mvcc's invariant, where the window's logical view is mvcc's own.
