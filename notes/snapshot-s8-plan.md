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
