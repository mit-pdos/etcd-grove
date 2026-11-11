# mvccfull F1, Prove: B3 (`mvcc.New`/`NewStore` over a backend holding a history), 2026-11-10

All five "B3 Prove" `sorry`s are proved; no axiom, no new `sorry`, no spec statement changed. Checked by
`lake build` of mvcc `Link`, `ApiResults`, `Results` (`#print axioms` of `mvcc.wp_NewStore`,
`mvcc.wp_New`, `mvccApi_New_wp_proof`, `mvccApi_NewStore_wp_proof`: no `sorryAx`).

| target | file | how |
|---|---|---|
| `mvcc.NewStore.wp_proof` | `NewStore.lean` → `NewStoreR.lean` (`wp_proofR`) | below |
| `mvcc.newWatchableStore.wp_proof` | `newWatchableStore.lean` | the fresh proof, the lock at `L'` (`NewWatchableAt.lean`: `wsInitAt`, `wsFrozenM_of_new`) |
| `mvcc.New.wp_proof` | `New.lean` | the fresh proof, `wsCloserM_of` (`NewWatchableAt.lean`) |
| `mvcc.api.NewStore.wp_proof` | `Api/NewStoreApi.lean` | over `Api/ImageBridge.lean`'s `newStore_of_storage` (S3/S4: `restore_of_storage`'s body generalized to `∀ γ`, a new module; the private original unchanged) and `resumeCtx_of_api` |
| `mvcc.api.New.wp_proof` | `Api/NewApi.lean` | the docstring's outline, the same bridge |

## `NewStore` over an image (`NewStoreR.lean`)

The fresh proof (`ae30739dde`) with: the image normalized across modes (`NewStoreImage.lean`:
`restoreImageM_norm`, off = the whole bucket at no record as a cut image); the caller's fresh index
names grown to `L'` (`idxFresh_image`: the authorities whole, so no `idx_renew`; R3 settled); the
session over `storeSessT`, its `Unlock` given the unregistered `Wi` (`sess_W_of_Wi`); `restore()` at
`ns = false` over the clean read, its `s.revMu` rounds on private memory (`nsRevP0/P/K/Q`); in its
`restoreDone` (the resume continuation `resumeK`) the store is made (`nsReady`): the registration
fixed (`storeSess_fix`), the writer at `L'` with the registration pending (`writerReg_allocP`), the
pool, `s.revMu`'s lock with the lag (`revMuBodyL`), `physOk`, the right by the mode; then, if the
records resume a compaction, `compactLockfree` (so `NewStore.wp_proof` now takes
`store.compactLockfree.spec`, as `store.Restore`'s does; link list and `Link.lean` regenerated,
interface regenerated).

**Findings.**
- **`s.mu` must be a lock during `restore()`'s resumed compaction** (`compactLockfree` takes
  `isStore`, whose `s.mu` guard). Perennial can make a lock only of unlocked memory with its
  resource, which `NewStore` has only after `restore()`. Workaround: `RWMutexWLocked.lean`'s
  `init_RWMutex_wlocked` (a lock made from the write-locked memory `plain.wp_Lock` leaves; P given at
  the unlock), proved over Perennial's sealed RWMutex internals (`*_unseal`): the only unfold of
  another package's definitions. Recorded in `notes/perennial-changes.md`.
- **R4 (the reader count with a resumed job)**: `compactLockfree` takes a reader token, and the
  post's `nReaders - nJobRd` readers leave none spare. The pool is made with `restore()`'s token
  counted retired (`retiredAt` at `nJobRd + 1`) and given back after `restore()` returns
  (`NewStorePool.lean`'s `readerPool_unretire`).
- R5 (`compactRightR` before `restore`): made inside the continuation, at `r.crev`.
- `etc/lean-check.py` reported "0 errors" on files `lake build` then rejected (errors inside terms and
  some tactic errors); `lake build` of the module (~30 s) was the loop instead.

**Bounds.** mvcc stock 44 (was 49): the deleted fresh helpers of `NewStore.lean` (-5); `NewStoreR`
and `RWMutexWLocked` listed as owners in `etc/bounds-allow.txt` (the store's constructor builds the
pool and the locks' slots; the lock's construction). `etc/api/mvcc-layout.txt`: the deleted helpers
dropped. Not run: `etc/tcb-report.py --check` (needs a full build; the five `sorry`s are gone, so the
baseline needs `--check --update`).
