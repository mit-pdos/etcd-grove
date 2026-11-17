# A1: the backend's read model over the tracked hook buckets (Scope, 2026-11-17)

Stage A1 of `auth-schema-srv` (`notes/auth-schema-srv-scope.md` §3, gap G1; Q2: proved). Branch
`auth-schema-srv`, worktree `/shared/etcd-grove-authschema`. This run: the Scope, a Go test of the
modeling decisions and a throwaway Lean probe of the shape; no Lean in the tree.

**Goal.** A reader holding `ReadTx().RLock()` learns, from the backend's proved specs, what it sees of
a tracked bucket (`P.RB`: on the server the rest buckets, auth's three among them), per bucket, in
terms a client can tie to its own history, including inside an `Unlock`'s window: a bucket the
session only put into is seen after the session from the write-back on, one it only deleted from is
seen before it until the commit, one it did both in is unconstrained until the commit. This is what
A0's per-bucket read contract (`auth.authReadTxOk` over `auth.BkView`, `auth.authViewSnapFrom`)
needs of the backend, and the law `rtHeldF_rbOwnIn` that `notes/backend-auth-split-plan.md` ("Later
stage: option (a)") left unproved, for the buckets a client claims.

## 1. What the backend has today, and the gap

- Readers: `readTx.RLock` gives `rtHeld γ P b rtx rv` (`InvBackend.lean`), `rv = (C, R)` the
  interval's committed data and the read buffer; `readTx.UnsafeRange` returns `rtRange rv bi ...`,
  exact for every bucket (a point read on a non-safe-range bucket: `vOf P rv n k`). So a reader's
  results are a function of `rv`; what is missing is any link from `rv`'s tracked buckets to client
  ghost state.
- The only reader-side ghost is `γ.view` (`bView`/`viewQ`/`thinV`, the logical view), over `vData`,
  which drops the hook buckets (`P.HB`); on the server `HB n = (n ≠ key)` (`mvcc.KBReal.P`,
  `mvcc.bridgeParams`), so every tracked bucket is outside it. `sessWf`'s write-side agreement
  (`ndel = 0 → agreeOff P.HB ...`), `viewSame`, `freeOk`'s empty write buffer and `hookStep` are all
  off the hook buckets too.
- The writer side tracks each tracked bucket's contents in `γ.rbk` (`rbPart`/`rbOwnIn`/`rbOwn`, the
  pending flag `F`; `rbSide` the lock's half, sealed). `rbOwnIn` is "no write pending" only (decision
  3, option (b)): its readers' meaning is argued from Go in the trusted readers' docstrings.
- The window machinery (`RdSt.win`, `γ.rvs`, `poisonAt`, `BSess.win`, `dlsW`/`dlsS`, `dls`) marks
  the readers' states between an `Unlock`'s write-back (`wb_core`) and its commit
  (`rtRes_cm_close`) and keeps the safe-range bucket's deleted entries; A1 sets its new ghost at
  exactly these two points and reuses the window flag to know which state is a window's.

## 2. The model (decisions in §6)

**D1. Per-session kind of each tracked bucket** (pure, `Model2.lean`): `RbK := idle | put | del |
mix`, a ghost field `BSess.tk : GoString → RbK`. `BSess.put`/`create` on a tracked bucket join `put`,
`del`/`delBucket` join `del` (put ⊔ del = mix); `Unlock` resets every bucket to `idle` (its
write-back and, when a delete is pending, its commit leave every tracked bucket's readers' contents
at the writer's, below); a commit leaves `tk`. A0's `AuthSess` (`BkW` per bucket, the `Sw` token) is
the auth-side image of `tk` on `authUsers`/`authRoles`; `auth` is always `put`.

Not `dlc` (the entries deleted since the last commit, the window's readers' view being the writer's
contents plus them): considered first, as the Q9 audit's "puts over the old snapshot" and the `dls`
precedent suggest; the kind gives the same answer for every non-mixed bucket with no new map and no
values, and the client already tracks kinds (`Sw`). `dlc` stays the fallback if a client ever needs
a mixed bucket's window state (A0's known limit O2).

**D2. The readers' contents of a bucket**: `rvBkt P rv n : BktData := k ↦ vOf P rv n k` (absent =
empty; probed, §5). New internal invariant clauses (in `sessWf`, `freeOk`):
- `trkOk`: for a tracked `n` of kind `idle`/`put`, the write buffer over the readers' view is the
  writer's contents (`ovB P.BT st.W.bks (viewOf P st) n = dget st.S n`); of kind `del`, the write
  buffer has nothing for `n` and the readers' view is the session's start contents;
- `freeOk`: every tracked bucket `idle`, its write buffer empty (as off the hook buckets today);
- `hookStep` strengthened: the hook leaves the tracked buckets' write buffer and kinds (today it
  leaves `rbData` but may buffer a put there; the server's hook writes `meta` only).

The window per bucket then follows: at the write-back (`vOf_writeback`: buffer over the old view) a
`put` bucket's readers' contents become `bktOf st.S n`, `idle`/`del` stay (`rvBkt_writeback_nop`,
probed), `mix` become `rvBkt P (st.C, writebackR st.W st.R) n`; at the commit every bucket becomes
`bktOf st.S n` (the commit's `C' = S` on tracked buckets: `hookStep` leaves `rbData`); a commit with
the lock free (`run`, `ForceCommit`, schema's `Unlock`'s second `Commit`) changes no tracked
readers' contents (`freeOk` + `trkOk`).

**D3. The readers' ghost, claimed per bucket.** A ghost map `γ.rbr` over the tracked names `γ.rbD`,
element `n ↦ rvBkt P rv n`: half in `readTx.mu`'s resource (`rtCore`, split by `rfrac` among the
readers, so it changes only under `readTx`'s write lock: `wb_core`, `rtRes_cm_close`, the
constructor), the other half **the lock side's** (inside `rbSide`, sealed) for an unclaimed bucket,
**the client's** (`rbRd γ n q v`, fractional) for a claimed one. A bucket is claimed once, for good
(a discarded per-bucket marker, as `dlNoDel`/`dlReg`), by the **claim law**

`batchLocked γ P b st ∗ rbOwnIn γ S r ⊢ |==> batchLocked γ P b st ∗ rbOwnInR γ S r ∗ rbRd γ S ½ r`

(the idle part agrees with the readers: an internal invariant, "flag `false` ⇒ kind `idle` and
readers' contents = the part's", which is option (a)'s `rtHeldF_rbOwnIn` inside the backend).
`rbOwnInR`/`rbPartR` (sealed, `@[no_expose]`) are the claimed buckets' writer parts: they hold the
`γ.rbk` halves that `rbOwnIn`/`rbPart` hold, and there is **no** law back to `rbPart`, so no trusted
writer (they all take `rbPart`/`rbOwn`) can ever write a claimed bucket. That is the soundness
argument for keeping every trusted text unchanged: a trusted writer of a claimed bucket would move
the readers without the client's half.

**D4. The readers' law**: `rtHeldF γ P b rtx rv p ∗ rbRd γ n q v ⊢ ⌜rvBkt P rv n = v⌝` (the two
fractions of one element agree). No law for `ConcurrentReadTx` (its cached copy can be stale after a
commit, `nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`; auth's `ReadTx()` is
`be.ReadTx()`, `schema/auth.go:63`).

**D5. Writers.** `UnsafePut`/`UnsafeSeqPut`/`UnsafeDelete`/`UnsafeCreateBucket`/`UnsafeDeleteBucket`
take the bucket's part of either kind (`rbPut` or its claimed twin `rbPutR`) and update `st.tk`.
`batchTxBuffered.Unlock.spec` gains, for the claimed buckets `Sc` of its part, an **accessor** of the
client's halves, run by the proof at the write-back and again at the commit, under `readTx`'s write
lock (no backend invariant open, mask `⊤`):

`Rr ={⊤}=∗ ∃ old, ([∗list] n ∈ Sc, rbRd γ n ½ (old n)) ∗ (∀ v, ⌜∀ n ∈ Sc, v n = new n⌝ -∗ ([∗list] n ∈ Sc, rbRd γ n ½ (v n)) ={⊤}=∗ Rr')`

with `new` by kind (D2; for the commit, `bktOf st.S n`). The client keeps its halves where it likes
(auth: in its invariant, which its readers open while the session runs); the post gives the
accessor's final resource and `rbOwnInR γ Sc r` (the claimed part idle). Today's statement is the corollary with `Sc = ∅` (`Unlock.spec_old`); a caller holding
its halves itself passes the trivial accessor. Shape probed (§5).

What A6 then does with it (not A1's): the auth realization claims `authBkts` at the first auth
`Lock` (C9), keeps `rbRd γ n ½ v` of the three buckets in its invariant with "each `v` the encoding
of a recorded state at index ≥ the published one, `ju ≤ ja`" (A0's `authViewSnapFrom`); a reader
opens the invariant after `RLock` and D4 gives its `BkView`; the writer's `Unlock` accessor moves the
halves to the session's state for `put` buckets (`auth`, and `authUsers`/`authRoles` per `Sw`) and,
at the commit, for `del` buckets. `mix` never occurs (`Sw`).

## 3. Proved vs trusted; the trusted texts it touches

**Proved, no axiom or `sorry` added**: everything above. **Trusted texts restated: none in text.**

| trusted text | effect |
|---|---|
| `storage.OpenBackend.wp_proof` (post `newPostK`), and through it the opened backend's `isBackend` | text unchanged; its meaning includes `isBackend`'s new internals (`γ.rbr`, `trkOk`), which `backend.New.spec`'s proof establishes: the axiom's standing argument ("claims what `New` gives") carries over, as at every backend stage (`dls`, `fk`, the window). To re-read at the stop, not to re-approve, unless the coordinator says otherwise. |
| the axioms taking `isBackend` as a premise (`backend.backend.Snapshot`, `snapshot.Size`, `NewBackendQuota`, `MustUnsafeGetAllLeases`, membership's `MustRead/Save/DeleteMember…`, `RaftCluster.Recover/SetBackend`, v3alarm's `NewAlarmStore`/`AlarmStore.restore`, `lease.NewLessor`, `auth.NewAuthStore`) | a premise only grows; their buckets stay unclaimed (no claim is ever made outside A6's auth buckets), so their writes keep the lock-side halves consistent. `backend.Snapshot`'s observation hands `rbOwn` (unchanged; the lock side's readers' halves are not in it). |
| `auth.authSchemaSrv` (`hD22`), `authSchemaSnap`, `authBkLend` | unchanged by A1; A6 proves them (C1's per-bucket read clause from D3/D4). |
| the trusted readers' Go arguments for `rbOwnIn` (`MustReadMembersFromBackend`, `RaftCluster.Recover`, `NewAuthStore`'s `authRecoverOk`) | unchanged (their buckets unclaimed). A later stage could claim `members`/`members_removed` and prove `MustReadMembersFromBackend` over `readTx`; not here. |
| exported `Results.lean:1081` (the server's pre-commit hook result, post `⌜backend.hookStep P st st'⌝`) | **statement changes** (stronger post: D2's `hookStep`); proof `BackendHooks.OnPreCommitUnsafe` writes `meta` only. A stop item (exported statement), though only strengthened. |

## 4. Go evidence for each modeling decision

New test (A1.0, done): `notes/auth-schema-srv-a1/zz_a1_trackedwindow_test.go`, copied into
`server/storage/backend` of the fork pin 6e8f0c004 (clone `/shared/tmp/auth-schema-srv/etcd`),
go1.27.3, real `NewTmpBackend` with a 1 ms batch interval (periodic commits racing), four readers,
three tracked (non-safe-range) buckets: three runs, 2761-5296 sessions and 0.8-1.5 M reads each.

| decision | test | result |
|---|---|---|
| D2 `put` bucket seen whole from the write-back (M1) | `TestA1TrackedBucketWindow`, bucket `a1put` | 0 split reads in 3 runs |
| D2 `del` bucket seen whole, before until the commit (M2) | same, `a1del` | 0 in 3 runs |
| D1 `mix` unconstrained in the window (M3, control) | same, `a1mix` | 14-24 k unrecorded reads a run |
| D2 commits with the lock free change no tracked view (M4) | same (completed session always seen) | 0 in 3 runs |
| D2 absent bucket reads as empty; a put into a bucket created and not committed is seen after `Unlock` (M5) | `TestA1CreatedBucketUncommitted` | pass |
| D1 the write-back/commit order | `batch_tx.go:328-357`; `nonissues/etcd-auth-readtx-delete-window-mixed-state/` (window, per-bucket and mixed-session tests, A0) | as modeled |
| D5 `Unlock` resets kinds (after it every tracked bucket's readers' contents are the writer's) | M1/M2/M4 together; split-plan's `TestUnlockIdlePut`/`TestUnlockIdleDelete` (2026-11-01) | as modeled |
| D3 one claim, auth's buckets, written only by schema's auth code in mode on | `server/storage/schema/auth*.go` (the only writers of `auth*` buckets besides `NewAuthStore`'s boot, which mode on reaches through `authSchemaSrv`) | code reading |

## 5. Lean probe (throwaway, `Scratch/A1Probe.lean`, untracked)

Checked against the tree (`etc/lean-check.py`): `rvBkt` as a finite map from `vOf`/`vKeys`;
`rvBkt_writeback_nop` (a write-back leaves a bucket the buffer has nothing for: the `del` and `idle`
cases) proved from `vOf_writeback`; `RbK`; the accessor `rdAcc` as an `IProp` (the `={⊤}=∗` shape
with a big-sep over the claimed buckets). Whole file 0 errors (`lean-check -a`); copy at
`/shared/tmp/auth-schema-srv/A1Probe.lean`. Not probed: the `Unlock` proof itself (A1.5's risk).

## 6. Decisions needed (each with a recommendation)

1. **Claim per bucket (D3) vs all tracked buckets.** (a) Readers' tracking only for buckets a client
   claims, sealed claimed parts: no trusted text restated, lease/membership/alarm untouched.
   (b) Every tracked bucket's readers' half inside `rbPart`/`rbOwnIn`/`rbOwn`: proves
   `rtHeldF_rbOwnIn` for all, but changes the meaning of the ten trusted texts over them (and
   `Snapshot`'s observation), and every `Unlock.bare` writer of a tracked bucket (mvcc's bridge, the
   lessor's `Revoke`) must pass its part. **Recommend (a).**
2. **Kinds (D1) vs deleted-since-commit entries (`dlc`).** **Recommend kinds**; `dlc` only if a mixed
   bucket is ever needed.
3. **The `Unlock` accessor (D5), a `={⊤}=∗` callback run twice**, vs a logically atomic `Unlock`, vs
   the client handing its halves in as a resource (bView's precedent: then readers learn nothing
   during the session, which auth's concurrent `CheckPassword` needs). **Recommend the accessor.**
4. **`hookStep` strengthened** (the exported `Results.lean:1081` post grows). **Recommend yes**
   (the alternative, an invariant that tolerates a hook's equal-value buffered put, is longer and
   still needs the hook not to put-then-delete).
5. **`OpenBackend`'s meaning through `isBackend`** treated as routine (follows `New`'s proof).
   **Recommend yes**, recorded in the stage notes, no axiom review.

## 7. Steps and estimates (Lean lines)

| step | content | est. |
|---|---|---|
| A1.0 | Go test of the model (done, §4) | - |
| A1.1 | pure model: `RbK`, `BSess.tk`, `rvBkt`, the ops' `tk`, `trkOk`, `freeOk`/`hookStep` clauses; preservation by put/del/create/delBucket/write-back/commit/hook | 500-800 |
| A1.2 | ghost: `γ.rbr` and the claim marker in `BNames`; `rtCore` and `rbSide` halves; `New`/`NewAlloc` | 300-500 |
| A1.3 | the readers' law (D4), `rbRd` laws (split, timeless) | 100-200 |
| A1.4 | the five write ops over either part, `tk` | 300-500 |
| A1.5 | `Unlock` with the accessor: `wb_core`, the commit's `rtRes_cm_close`, `Unlock.spec_old`/`bare` corollaries | 800-1500 |
| A1.6 | lock-free commits (`Commit`, `ForceCommit`, `run`, `CommitAndStop`, the hook window) keep `γ.rbr` | 300-600 |
| A1.7 | the claim law, `rbOwnInR`/`rbPartR` (sealed), their split laws | 300-500 |
| A1.8 | callers: `Unlock`'s 8 users, `BackendBridge`, `CindexBackend`/`OnPreCommitUnsafe`, `Results.lean:1081` | 200-400 |
| A1.9 | interfaces (`etc/api/backend.txt`), tcb/axiom-tok/bounds gates, notes | 50-100 |

Total about 2900-5100 lines. Checkpoints: after A1.1 (the model, pure, cheap to change), after A1.5
(the `Unlock` statement as proved: internal, but the accessor's final form is what A5/A6 consume),
before landing (the exported `Results.lean:1081` change).

## 8. Risks

1. **`Unlock`/commit proofs** (A1.5-A1.6): the largest edits are to `batchTxBuffered__Unlock.lean`
   (349 lines), `CommitLemmas`/`rtRes_cm_close`, `WritebackLemmas`; the window's `poisonAt`/cache
   marks must not interact (the cache copies only non-window states; `rvBkt` is a function of `rv`,
   so cached copies need nothing new). Mitigation: A1.1's pure lemmas first; `lean-check --split`.
2. **Running a client update inside the critical section**: legal (no backend invariant open at the
   write-back's and commit's ghost updates if the accessor runs outside `cacheInv`'s opening), but it
   fixes an order: the accessor must not need `readTx` (auth's invariant does not).
3. **Sealing is by convention** (`import all` is unrestricted; `etc/api-check.py`'s backend list is
   the gate): a proof outside the backend that unfolds `rbOwnInR` could reach `rbPart` and a trusted
   writer. The `import all` gate on the backend's modules must cover the new modules.
4. **Memory/time**: backend modules are mid-sized; the server's chains rebuild on `isBackend`'s change
   (`etc/importers.py --count` on `InvBackend.lean`: ~2250 importers). Full builds through the slot
   wrapper; expect several hours per full rebuild.
5. **Not modeled**: `backend.Defrag` (not translated/linked; swaps bbolt's file under both locks,
   contents unchanged); a future link must keep `γ.rbr`.
6. **lean moves** (the origin/lean merge, Perennial pin c6b39d4f8) before A1's Lean starts: merge first.

## 9. How A2-A7 depend on A1

- **A2** (`UnsafeForEach`): the read-side `baseReadTx.UnsafeForEach` result is stated over `rvBkt`
  (`bktEnts (rvBkt P rv n)`); can be drafted over A1.1's `rvBkt` before A1.5. The batch-side
  `batchTx.UnsafeForEach` is over `st.S`, independent.
- **A3** (Marshal, `sizeCache`) and **A4** (put budget): independent of A1; can run in parallel.
- **A5** (schema's write side): the `authBatchTx` ops over `rbPutR` (claimed auth buckets) and the
  kinds (`Sw`'s `BkW` ↔ `tk`); `authBatchTx.Unlock` over A1.5's accessor. Needs A1.4-A1.5's statements
  (not proofs).
- **A6** (the realization): the claim (A1.7), the readers' law (A1.3), the accessor (A1.5); proves
  C1 (per-bucket `RLock`), C5 (`authBkLend`, over `rbOwnInR`'s agreement), C11 on every snapshot
  backend (claim at its first `Lock`).
- **A7**: after A6; A1 adds nothing to the closed statements.
