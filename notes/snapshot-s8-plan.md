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
    when `run` returns. `RemoveAllPeers` alone (no panic) is true over `transportStarted`. *Settled 2026-10-25 (the user for the D22
    owner; `notes/decisions.md`, D43, "W3 settled"): the right is the transport's `trLive` (D41),
    not frozen by `NewServer`, held by the apply thread, consumed by `Stop`; carried out in T-M's M5
    (`notes/membership-plan.md`).*
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

## Where S8 stops, second pass (2026-10-24)

Done since the first pass: W3 (the transport's peers right, `RemoveAllPeers`), the callees' axioms
(`lessor.Recover`, `authStore.Recover` with W2 in mode `.off`, `RaftCluster.SetBackend`), the
gauge's initializer, `NewMembershipBackend` proved, and two of S8d's lemmas (`kv_cert_jump`, W4's
KV jump; `srv_be_swap`, item 9). Not done: `RaftCluster.Recover`, `storage.Release`, and
`applySnapshot`'s spec and proof, which need:

- **W5, an environment premise for the snapshot file.** `OpenSnapshotBackend` returns an error when
  `DBFilePath`'s directory read or `os.Rename` fails (their axioms allow any I/O error), and
  `applySnapshot` then panics (`lg.Panic`, `server.go:1059`): a goroutine's panic, which `run`'s
  proof cannot take. A no-panic spec needs a premise of the kind of `storage.dbOpensOk` ("the file
  system cooperates for the server's database files"), with `DBFilePath`'s and `os.Rename`'s axioms
  (or `OpenSnapshotBackend`'s spec) saying no error happens under it. An environment assumption:
  the user's to approve, as D22's two were.
- **W1, `Rm`'s variant to confirm**: `Rm j := snapTakenLb γt j` (a monotone counter of the highest
  snapshot index opened, the apply thread's authority at most its applied index), since the decided
  `snapTaken j ∨ appliedAtLeast γr (j + 1)` cannot be shown at `Release`'s removals
  (`notes/decisions.md`, "D22 receiver epochs, S8c carried out", W1).
- **W6, `RaftCluster.Recover`'s members.** After `UnsafeLoad` the cluster's members are decoded
  from the image's membership bucket; the `AddPeer` loop needs each member's peer URLs to be the
  network directory's (`γn.dir id = urls`, `memberDirIs`, which only `bootstrap`'s contract gives
  today), and `srvRest` at the image needs `clusterMem c` at the rest model's members
  (`restModel … .mem`): a relation between the model's bucket and in-memory members (static
  membership: the boot members) for the axiom to give, or `rcLockInv` carrying the directory fact.
- **W7, the old backend's `Close`.** `backend.Close.spec` takes the backend's stop channels
  (`isStopChans`) and all of its open token (`bOpen 1`); `NewServer` drops the boot backend's
  `isStopChans` (`bootBackend_of_newPost`'s `-`) and splits `bOpen` among the store's reader tokens,
  the monitor's and the constructors' (given back); S8d needs all of them back at the swap (the
  store's from `Restore`, the monitor's from `srv_be_swap`, the remainder `qo` and `isStopChans` kept
  by `NewServer` and threaded to `run`).

- **W8, `RemoveAllPeers` and D35's peer coverage** (open, 2026-10-25; the rafthttp track's note,
  `notes/decisions.md`, D40, "Note for D22 S-j"). The proved transport's `AddRemote` after the
  freeze returns at once for a recorded peer (`AddRemote_frozen`), and the handlers' premises are
  discharged from the frozen state and the caller's coverage, "every other member among the recorded
  peers" (`trAddRemote_of_frozen`, `trRemotesFrozen`). `applySnapshot`'s `RemoveAllPeers`, then the
  `AddPeer` loop, runs while the transport serves: in the window a handler's `AddRemote` adds a
  remote (Go's behavior), and the coverage does not hold through it. Their suggestion: state
  `RemoveAllPeers` keeping the recorded ids, with the window's remotes stopped by the re-add, or a
  premise; rejected by them: a premise that the handlers' `AddRemote` returns, and letting the
  handlers add remotes. To settle when `RemoveAllPeers`/`AddPeer` are stated over the proved
  transport (W3 redone).

Then S8d: the spec (S-j2's item 6 adjusted: the snapshot file and image in the precondition, the
apply thread's resources before, `applyAll`'s post shape at the new backend after) and the proof in
`applySnapshot`'s order, with `restorePre_of_apply`, `kv_cert_jump`, `srv_be_swap`,
`ci_announce`/`ci_swap_au`, `hooksOk_server_fut` and the axioms above.

## For S-j1 (2026-10-25)

- **The old backend's close resources (W7's second part, the user's (c)).** `applySnapshot.spec`
  takes the current backend's stop channels and the constructors' half of its open token as a
  named premise. S-j1 threads them: the reverted patch of 2026-10-25 put them in `srvBeOwn`
  (`backend.isStopChans d.γB d.be ∗ backend.bOpen d.γB ½`, `srvBeOwn_frag` keeping them), framed
  them at `NewServer`'s `srvBeOwn` (`HSC` from `bootBackend_of_newPost`, `Hopen` after the last
  constructor: it must be carried to that split, the one missing step), and had `srv_be_swap`
  return the old ones; `applySnapshot` then puts the new backend's (from `OpenSnapshotBackend`'s
  `newPostK`) in. It changes `srvBeOwn`, which `Results.lean:431` reaches through `srvApplyKV`.
- **W8** (the user's): a named premise of `applySnapshot.spec`, discharged with the rafthttp track.
