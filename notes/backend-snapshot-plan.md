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

**Refined (2026-11-20, B3): the slot rides in `rdTok`.** A new token delivered to the apply thread would
run through `newPostKP`, mvcc's open laws, `NewStore`'s post, the server's boot and its restore path. But
the apply thread already holds a backend reader token at the call (`apply.bkRT`'s `rdTok`, which
`SnapSendBranch` takes out and gives back around the snapshot), and SpecPlan's `Snapshot` takes a counted
reader slot too (`beRdToks γ 1`). So every `rdTok` also carries a `b.mu` read slot (`bmSlot`, tied to
the backend's database by `bDB`), and `Snapshot` borrows the caller's `rdTok`. `b.mu` has
`actualMaxReaders` slots and the batch transaction keeps one, so the constructor makes one `rdTok` fewer
(`rdStockN` one smaller; its last `readTx.mu` slot unused). The spec chain: `backend.Snapshot.spec`, mvcc's
`mvccImage_snapshot.law`, the server's `senderImage.law`/`snapImageG`, and `SnapSendBranch`'s call.

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

- 2026-11-21, **B2 done** (`5b38d08e58`, step (c) without a restructure); **B3 done**: `rdTok` carries `bmSlot`
  (`BmStock.lean`, `rdSlotsN`, both irreducible: a reducible count let `newBackend`'s framing unfold a
  `2 ^ 30`-element `List.replicate`, 61 GB); the spec chain lends the caller's `rdTok`. Merged with `lean`
  (Perennial pin `c8e356cb1`, built against a private copy, `.lake/perennial-pin`, since the shared checkout
  was at another pin). B4's registry lemmas (`RegSnap.lean`: `reg_register`, `reg_take`) checked.

- 2026-11-21, **B1-B3 landed** through the land queue (claim #16; `lean` `abd7c00ed5`).
- 2026-11-21, **B4 done**: `backend.Snapshot` proved (`backend__Snapshot.lean`, written by a subagent over
  `RegSnap`'s `reg_register`/`reg_take`); the commit invariant keeps `fkRd` at the committed data (the post's), the
  commit glue takes it at the writer's contents (`unsafeCommit` derives it from `fkHalf`, `fkOkRvG_empty`);
  `backendInit` gains `minSnapshotWarningTimeout` (the ticker's interval floor: `time.NewTicker` needs `0 < d`, and
  the float conversion of the size-based interval can be any value). The backend `Link` links it
  (`batchTxBuffered__Commit+Cnt`).

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

**Decided (2026-11-20; the user: "make your own choice ... the top-level robustness theorems should
have fewer axioms"): option 1.** Why:
- Option 3 (SpecPlan) does not avoid the question: mvcc's snapshot law observes the frozen writer's
  state through `W` (`lateW`) and the view quarter (`SnapLaws.lean`, `snapObs`), and compaction's
  sessions commit in `Unlock` windows while mvcc snapshots, so mvcc's history update would need the
  same commit-time `W` in a window; and it changes `backend.Snapshot.spec`, mvcc's
  `mvccImage_snapshot.law`, `KVStoreLaws`/`SnapSendBranch`/`applyAll` on top.
- A cheaper exclusion (the snapshotter holds a share of the clients' view, `bView`, so no window,
  which needs the clients' whole half, can be open while it is registered) fails for mvcc: mvcc's
  clients' half is in the writer's resources inside the batch lock's `W` (`bkView` = `bView`), not
  with the snapshotter (`mvccReaders` are pool tokens).
- Option 1 keeps every client-facing spec (mvcc's API, the server's) and the same axiom reduction (all
  26 collections reaching `backend.Snapshot`); it matches Go (snapshots concurrent with window commits).

**Option 1's restructure.** In a window, `W` exists only as the `Unlock` caller's wand
`bView γ 1 (relog P vd st) -∗ W ∗ Q` (`batchTxBuffered.Unlock.spec`'s second case), and the clients'
half is deposited in `cacheInv` while `γ.cur` says `win`. So, in `unsafeCommit`, before
`batchTx.commit`, a ghost-only step advances what the close advances that does not depend on the new
read transaction: the history entry `(ver, idx + 1) ↦ (S, R.reset)`, `γ.cur` to it out of the window
(fresh, so `cacheInv`'s poison condition holds), the view's three fractions to `L'` (`view_upd3`); the
clients' half then leaves `cacheInv` and the caller's wand gives `W ∗ Q`. The registrations are armed
with `W`, `Pk` and the lock's halves at `S` (as at an ordinary commit). After the commit a variant of
`rtRes_cm_close` (from an intermediate `rtCmMid`) does the physical part (the new interval, `γ.rd`,
`γ.rvs`). `unsafeCommit.spec`'s window case takes the caller's wand and returns `W ∗ Q` in place of
`bView γ 1 L'`; `Unlock` passes it. Readers cannot see the intermediate state (`readTx.mu` is held
from `rtRes_cm_open` to the close).

**Arming, refined (2026-11-20).** Arming happens *at* the commit point (in the commit glue, inside bbolt's
update), from the lock's inputs at `S` passed to `batchTx.commit` (`obsIn γ P W Pk S`, `bStopView`'s
shape, given back), so that no snapshot can `Begin` between an arming and the data changing. Every call
of `batchTx.commit` (a commit, or a no-op when nothing is pending: then `S = C`, `sessWf`) arms every
registration and increments a counter `c` in `cmtInv` at once. The invariant: every registration made at
a count below `c` has `Q` of the committed data. A registration records the count `n`; `Snapshot`'s own
`Commit()` gives `cntLb (n + 1)` (a second spec of `batchTxBuffered.Commit`, pre `cntLb n`, post
`cntLb (n + 1)`, through `commit`/`unsafeCommit`'s same parameter); at `Begin` the registration is armed.
A registration: the map `γ.txb` (fixed value `(γR, γΨ, n)`, the registrant's element whole), the
entry in the invariant `∃ R Q, savedProp γR ½ R ∗ savedPred γΨ ½ (λ D, ⌜obsAt P Q D⌝) ∗ R ∗ obsWand … R Q ∗
⌜n < c → obsAt P Q Dc⌝`. At the commit point each wand is applied to `▷ R` and the inputs, kept by
`P ⊢ P ∧ P` (the conclusion is pure: `◇`).

**Done so far (B2):** the registry and its arming (`RegLemmas.lean`: `entry_arm`, `entries_arm`,
`regs_arm`, `obsIn_of_lock`); `batchTx.commit` arms at its commit point or a no-op (`cmt_arm_noop`), over a
frame `F` with `F ⊢ obsIn` (kept whole); `unsafeCommit`/`batchTxBuffered.commit` take `cntLb n` and `W`
(out of a stop and a window) and give `cntLb (n + 1)`; `Commit.specCnt` (and `Commit.spec` from it);
`CommitAndStop`, `run`, `Unlock` pass `cntLb 0`.

**Step (c), as done (2026-11-20, `5b38d08e58`): no restructure.** The commit glue takes an arming step
(`armStep`: from a frame `F`, at the commit point's mask, arm every registration at `S` and bump the
counter, `F` back) instead of `F ⊢ obsIn`; `regs_arm`'s inputs may come by a ghost update (`|==> obsIn`),
which is *hypothetical*: the conclusion is pure, so the and-trick keeps the original resources and drops
the update's effects. In a window (`RegWindow.lean`, `armStep_win`) the step borrows the clients'
deposit from `cacheInv` (the open window, `rtCm`'s half of `γ.cur`, says it is there), moves the view's
three fractions to `L'` and applies the `Unlock` caller's wand for `W` inside the hypothetical update
(`obsIn_win`), and puts the deposit back unchanged. `unsafeCommit`/`commit` lend the caller's wand
through a window (`Qw`); `Unlock` passes it. `cacheInv`, `rtRes_cm_close` and the window protocol are
unchanged.

**Step (c), concretely (2026-11-20).** The window opens in `Unlock` with `rtRes_wb_close … true`, which
deposits the clients' half `bView γ 1 vd` in `cacheInv` (`(win = false) ∨ ∃ vd, bView γ 1 vd`); the commit
runs with `readTx.mu` held whole (`rtRes_cm_open` … `rtRes_cm_close`); `unsafeCommit`'s post gives
`bView γ 1 L'` (`L' = relog P vd st`) and `Unlock` applies the caller's `bView γ 1 L' -∗ W ∗ Q` after it.
Plan: (1) `cacheInv`'s window case gains a third alternative, `bvTaken γ` (the deposit taken, while
`readTx.mu` is held: no reader is in); (2) in `unsafeCommit`, before `batchTx.commit`, take the deposit,
move the view's three fractions to `L'` (`view_upd3`: the lock's quarter, the readers' in `rtCm`, the
clients' half), apply the caller's wand (now in `unsafeCommit.spec`'s window pre; its post gives `W ∗ Q`
in place of `bView γ 1 L'`) for `W`, arm from `obsIn` at `S` (the quarter at `L'`: `thinV (sData S) L'`
is `Hpre`, `dlsOk P st' L'` is `Hdlc.2`); (3) `rtRes_cm_close`'s window branch takes the view already at
`L'` and `bvTaken` instead of the deposit. Risks: `rtCm`'s readers' quarter is `viewQ … (vData (C, R)) L`
with `cacheValid (C, R) idx L`: at `L'` these need `thinV (vData (C, R)) L'` (to check) and `cacheValid`
(vacuous under `poisonAt`, as the close's own argument).

**Superseded (2026-11-21):** `lean` had already translated and proved `snapshotTransferSec`'s initializer (2026-11-19); B4 only adds its histogram fact to `backendInit` (`etc/gen-init.py`), no axiom.

**Found for B4 (2026-11-20, superseded above):** `Snapshot`'s goroutine calls `snapshotTransferSec.Observe` (`metrics.go`),
a package variable today under `opaqueInitsOk` only: proving `Snapshot` would need a new
`snapshotTransferSec_init` axiom, a net zero. Instead translate the backend's `metrics.go` histograms
over a constructor spec (`prometheus.NewHistogram`, the options literal, `ExponentialBuckets`): the four
`commitSec`/`rebalanceSec`/`spillSec`/`writeSec` `_init` axioms go too (floats are stepped now), for a net
reduction.

**Next steps, in order:** (a) B2 registry defs (`ObsQ`, `obsAt`, `obsWand`, entries with saved
`R`/saved predicate, `γ.txb` as the map's authority; `viewAt`/`viewAtD` moved to `InvBackend`); (b) arming
at an ordinary commit (unsafeCommit, before `batchTx.commit`, from `thinV_trans`, `dlVd_of_dlsOk`,
`bStopG`-like extraction); (c) the window restructure above; (d) arming at `Snapshot`'s own no-op
commit (`sessWf`'s new fact); (e) B3; (f) B4.
