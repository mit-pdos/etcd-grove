# S8 of the receiver epochs: `applySnapshot` past the empty case (plan, 2026-10-24)

Stage S8 of `notes/snapshot-receiver-epochs.md` §4 (track T-S, D22). Go: `server/etcdserver/server.go`
`applySnapshot` (lines 1014-1172 at the etcd pin `bc9c3868c`). What it builds on: S7 and S7f
(`notes/decisions.md`, "D22 receiver epochs, S7 carried out" and "S7f carried out", their "What S8
uses" lists). Each sub-stage is one commit with a full `lake build` and `etc/tcb-report.py --check`.

## The open issue, resolved: no hook runs on the new backend before `SetBackend`

S7f left it open. `OpenSnapshotBackend`'s `openPre` asks for the new backend's batch-lock resource
`Pk γB = batchLockInv (γA.withPh π') (metaTM γB P)` at the open (inside `backend.New`'s ghost
step), but the apply protocol registers the new names `π'` only at `ci.SetBackend`'s store of 0
(`ci_swap_au`, atomic with `ci := 0`). A hook running in between would store the old `ci` (below
the snapshot's index) into the new backend: `UnsafeUpdateConsistentIndex`'s verification fails (a
panic under `ETCD_VERIFY`), and without it the new backend's stored index goes back, so a reload
re-applies entries. Go relies on no commit of the new backend before `SetBackend`: `newBackend`
sets `b.hooks` after `newBatchTxBuffered`'s empty commit (`backend.go:273-275`), `run` commits only
with `pending ≠ 0`, and nothing but `applySnapshot` holds the new backend until then.

The two options S7f named:
- (a) the backend's contract guarantees no hook runs before the first write or forced commit, with
  the write right held by `applySnapshot` until `SetBackend`;
- (b) a "future" status in the apply protocol's registry whose hook triple is refuted.

They are not alternatives: a future status can be refuted inside the hook only with something the
hook sees, and today the hook sees only the batch lock's state and `Pk`, which say nothing about
who could commit (a `ForceCommit` with nothing written finds the same state as no commit at all).
So the refutation needs (a)'s fact, in the smallest form the backend's proof already has:

**S8 takes both, minimally.** The backend proof already makes every commit *paid* (`payIn`, in
`unsafeCommit`'s precondition): a write-back token (`Commit`, `ForceCommit`, `Snapshot`), the `run`
goroutine's write-back witness (`m = 1`, after an `Unlock`'s write-back, which spent a token),
`Unlock`'s own write-back (`m ≥ 2`), or the clients' half of the open token at a stop (`Close`).
`newPost` gives the creator *all* of these (`ownToks γ.wb wbInit`, `bOpen γ 1`). So:
1. the hooks' triples see the commit's payment (`payIn`, framed: given and returned), and
2. a lemma refutes a payment beside the creator's fresh rights (`hook_fresh_false`: `bFresh γ :=
   ownToks γ.wb wbInit ∗ bOpen γ 1`; needs `bgOk`'s new `w ≤ ver`: a write-back raises the read
   buffer's version, which the token budget bounds),
3. the creator's batch-lock step (the `openPre` fupd) receives `bFresh γ` and gives `K γ` back
   (`newPostK`), so a creator can deposit the rights where the hook finds them, in the same ghost
   step that makes `Pk γ` (a deposit after `Open` returns would leave a window in which the hook
   cannot refute: it never sees the creator's local resources);
4. the apply protocol has a future status: the new names `π'` (with the new backend's `wb`/`opn`
   ghost names, so the hook of backend `γB` finds *its* rights) announced at the open with the
   rights deposited; the hook of a future backend refutes (2.); `ci_swap_au` takes the rights back
   when it registers `π'` (current) and retires the old names.

Why this is the smallest true choice: no trusted statement becomes false or stronger in substance
(`OpenBackend`'s axiom is generalized exactly as `backend.New`'s proved spec, which it wraps; the
hooks' triples get more in their precondition, which every existing hook frames); no backend client
spec changes (`Lock`, `Commit`, `ForceCommit`, `Snapshot`, `Close`, `Unlock` keep their statements);
`bootOk` keeps its text (`newPost` unchanged, `newPost_of_K`). Rejected: an axiom that the new
backend commits nothing (provable, so not a trust-boundary fact); threading a "backend used" flag
through every client operation (every client's spec would change); a deposit after `Open`
(the window above).

## Sub-stages

- **S8a. The backend: commits pay the hooks.** `payIn` moved to `InvBackend` and framed into
  `hooksSpec`, `hookFnSpec`, `hooksReq` and the storage layer's `saveSpec`/`saveReq`/
  `BackendHooks.OnPreCommitUnsafe`; `payIn`'s `m ≥ 2` case with the write-back's lower bound;
  `bgOk` with `w ≤ ver`; `bFresh`, `hook_fresh_false`; `openPre`, `backend.New`, `newBackend`,
  `OpenBackend` (axiom, generalized), `OpenSnapshotBackend` with the creator's `K` (`newPostK`;
  `newPost_of_K`, `openPre_keep`).
- **S8b. The apply protocol's future status.** `ApplyPhys` gains the backend's `bwb`/`bopn` names;
  `ApplyNames.fut` (a monotone list of announced futures, each with a claim token); `consRest` holds
  the futures (registered, or their deposited `bFresh`); `batchLockInv`'s registration is
  `applyRegd ∨ applyFut`; `ci_announce` (in the open's ghost step: deposit, mark, the lock's
  resource), `ci_swap_au` restated from the future (registers `π'`, gives the rights back),
  `fut_resolve` (in a hook: a future refuted, or registered since), the hooks' contracts for the
  new backend's `Pk` family (`hooksOk` of the server's hooks).
- **S8c. The callees' trust boundary.** Axioms, each in `Proof/<pkg>/<fn>.lean` with a docstring
  arguing it against the Go lines, for what is not translated and not cheap to translate:
  `lessor.Recover`, `authStore.Recover`, `RaftCluster.SetBackend`, `RaftCluster.Recover`,
  `Transport.RemoveAllPeers`, `storage.Release` (as needed; the others, e.g. `Members`, `AddPeer`,
  may already have specs).
- **S8d. `applySnapshot` for a non-empty snapshot.** The spec (the apply thread's resources before;
  `applyAll`'s post shape at the new backend after: `beSucc`, `isServer` at the new names, the
  snapshot's metadata in `ep`) and its proof; the empty case kept as a corollary so `applyAll`'s
  proof is unchanged; the wiring into `applyAll`/`run` is S-j1's (raft's contract must first hand
  over a non-empty snapshot).

If S8d does not fit, it stops at a committed, building point with what is left listed here.

## S8c/S8d, callee by callee (2026-10-24, after S8a and S8b)

What `applySnapshot`'s body needs, in its order (`server.go:1014-1172`), and where each stands. ✓: a
spec or lemma exists; **W1-W4**: a design question that crosses another track's trusted statements,
to settle before the axiom can be written true.

1. `applySnapshotInProgress.Inc()`/`Dec()`: the gauge's initializer is opaque today; it needs the
   gauge fact (`etc/gen-init.py`'s `_srv_custom`, as `proposalsApplied`): +1 init axiom.
2. `raft.IsEmptySnap` ✓ (a non-empty snapshot: index `i > ep.appliedi ≥ 0`).
3. `<-toApply.notifyc`: a unit bag; its payload is S-j1's (`snapSaved γd i` and the content
   certificate). S8d's spec takes the snapshot file and its image directly (below).
4. `OpenSnapshotBackend` ✓ (S8a's `K` form): `hooksOk` from `hooksOk_server_fut` ✓; the open's
   batch-lock step from `ci_announce` ✓ and a fresh `lateW` slot; `pathOwn` of the backend path
   (`bootOk`'s `Hpath`, to thread through `NewServer` → `run`); `dbOpensOk` (`NewServer`'s
   premise); the file `fileHolds (snapDBPath ss i) D` with `□ srvImage γ i D`. **W1**: the file is
   in the snapshot directory (`snapDirInv ss γd img Rm`), whose removal fact `Rm` is still
   undecided (`notes/decisions.md`, "D22 S-j2 carried out": with the fork fix of
   `issues/etcd-release-snapdb-before-open.md` the removers of `i` are `applySnapshot(i)` itself
   and `Release(i')` after `applySnapshot(i')`; a workable `Rm j := snapTaken j ∨
   appliedAtLeast γr (j + 1)`, with `snapTaken` minted from an exclusive claim raft's hand-off
   gives `applySnapshot(i)`); S8d takes the file in its precondition, S-j1 takes it out of the
   directory.
5. `ci.SetBackend` ✓ with `ci_swap_au` ✓ (S8b): its premise `ciEff ≤ i` a premise of S8d's spec;
   S-j1 from raft (a restored snapshot's index is above the committed index, at least the stored
   consistent index; `ciJ` allows `ciEff = c₀ > ai₀` at boot, which this bound covers).
6. `lessor.Recover(newbe, rd)`: an axiom (`lessor.go:600-609`, `initAndRecover` `:808-835`: under
   `le.mu`, `le.b`, `le.rd`, fresh maps, the lease bucket created and read under the new
   backend's batch lock (`LockOutsideApply`, `Unlock`: a write-back token), `ForceCommit` (a
   token; its hook runs at `ci = 0`, the new names registered)). Pre: `lessorInv`, `lessorBeOn lp
   oldbe`, the new backend's contract, two tokens, an open share, its `rbOwn` with the lease
   bucket empty, the lessor's lease set empty (the workload grants none); post: `lessorBeOn lp
   newbe`, the rest back. Straightforward; not written yet (no caller until S8d).
7. `kv.Restore` ✓ (`watchableStore.Restore`, S6) with `restorePre_of_apply` ✓; still to supply:
   `certOk E.γ ([[], []] ++ R)` for the image's log (a certificate minted in the server's `cok`
   map: whose authority holds it after `NewServer` is to be found), the new backend's
   `storeBackendT` (`storeBackendT_of_backend` ✓ at `lateW gx'`), `kbView` of the image's key
   bucket (`imageAt_keyView` ✓), `kbNoCmp` (`OpenSnapshotBackend`'s post with `keyImage_noCmp`
   ✓), `kbRegRight` (the other half of `gx'`), the reader tokens (`newPostK`'s).
8. `SetTxPostLockInsideApplyHook` ✓, `getTxPostLockInsideApplyHook` ✓ (at the new names),
   `ConsistentIndex()` ✓ (`ci_get_au`).
9. `s.be = newbe` under `bemu`'s write side: a ghost lemma to write (S7's "What S8 uses", 1):
   `bemuP 1`, `srvBeOwn`, `srvWTPool`'s quarter of `γbe`, moved to the new `d'` with the new
   backend's write-back tokens (`n' ≥ receiptBound`), the old tokens to `oldbe.Close`.
10. `storage.Release(snap)`: an axiom (`storage.go:75-82`: the WAL's `ReleaseLockTo`, the snapshot
    directory's `ReleaseSnapDBs`, which removes the `.snap.db` files below the snapshot's index):
    its removals need `Rm j` (**W1**).
11. `alarmStore.Recover(NewAlarmBackend(lg, newbe))` ✓ (S7c; the image's alarm bucket empty,
    `bkRestAt_boot` ✓).
12. `authStore.Recover(NewAuthBackend(lg, newbe))`: an axiom (`auth/store.go:399-418`). **W2**:
    `NewAuthStore`'s axiom gives the request path a persistent `isReqAuth st RD` over an
    existential reader resource `RD`; after `Recover` the permission checks read the new backend
    (`lockedReadTx` under `beMu`), so a true `Recover` needs `RD` to be a reader resource of
    whichever backend is current (it cannot be re-made: `isReqAuth` is persistent and shared).
    Whether `NewAuthStore`'s `RD` is so is the auth track's statement (`notes/auth-plan.md`);
    settle with them before writing `Recover`.
13. `cluster.SetBackend(NewMembershipBackend(lg, newbe))`: an axiom (`cluster.go:247-250`: the
    field, then `MustCreateBackendBuckets` under the new backend's batch lock: the membership
    buckets exist in the image, `rbOwn` unchanged, a write-back token): `clusterBeOn c oldbe` →
    `clusterBeOn c newbe`; `NewMembershipBackend` needs a spec (as `NewAlarmBackend`'s).
14. `go oldbe.Close()` ✓ (`backend.Close.spec`): `isStopChans` and all of the old backend's open
    token, gathered from the store's tokens `Restore` returns, the write budget's and the
    monitor's (item 9) and the objects' (their `Recover`s return their shares).
15. `cluster.Recover(api.UpdateCapability)`: an axiom (`cluster.go:262-300`: under the cluster's
    lock, `UnsafeLoad` of the new backend's members, removed members and version,
    `MustDetectDowngrade`, `onSet`): `rcLockInv` re-established with the image's members (the
    static members: `restModel`'s at the image's log, the local one among them, none removed),
    `clusterMem c` at them, each member's peer URLs the network directory's (`memberDirIs`, for
    `AddPeer`), under the workload's premises (no downgrade, the cluster version not above the
    server's).
16. `transport.RemoveAllPeers()` and the `AddPeer` loop. **W3**: `AddPeer` panics on a stopped
    transport (`transport.go:300-302`); the started transport's contract (`transportStarted`,
    persistent) lets `raftNode.onStop`'s `Stop` (`isRNTransport`'s triple, no token) race with it
    in the model, while Go orders it (`run`'s deferred `sched.Stop()` before `s.r.stop()`,
    `server.go:818-825`: "must stop raft after scheduler"). A true `AddPeer` after `Start` needs
    an exclusive right that `Stop` consumes: `Transport.Start`'s axiom and the raft node's
    transport contract restated, the right passed from the apply thread to the raft node's stop
    when `run` returns. `RemoveAllPeers` alone (no panic) is true over `transportStarted`.
17. `cluster.Members()` ✓, `MemberID()` ✓, the `ep` stores, `NewUberApplier` ✓ (at `E'`).
18. The post: `isServer` at the new names and `E' = E.onBe …` (`beSucc`), `applyBackend`
    (`ciOwner` from `SetBackend`, `isMetaBackend newbe (readView …)` from the open's backend),
    `srvApplyKV` at `E'`, `srvRest E' γr A'`, and the KV model at the image's prefix: **W4**
    (S-j2's item 6): `kvApplied γr.raft γr.kv A' x'` with `x'.log = kvModel γk A'` needs the KV
    ghost moved to the image's log through `kvInv` and a certificate of the committed prefix minted
    there (`dbImage`'s `A`, `srvRLogLb`); not designed in Lean yet.

**Where S8 stops (2026-10-24).** S8a and S8b are done (the open issue resolved, the protocol's swap
ready); S8c/S8d not started: four questions (W1-W4) need settling first, two of them (W2, W3) in
trusted statements other tracks own (the auth store's constructor, the transport's start and stop).
Next step: settle W1 (with S-j1) and W3 (a restatement of `Transport.Start`/`isRNTransport`'s
`Stop` with a peers right), ask the auth track about W2, then write items 1, 6, 10, 12, 13, 15, 16's
axioms and S8d.
