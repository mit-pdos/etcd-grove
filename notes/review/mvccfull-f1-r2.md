# Review: mvccfull F1, round 2 (2026-11-10)

Under review: `836dc79be2..d595560967` (branch `worktree-mvcc-full-tester`), limited to `Spec/`, the
`Spec*` proof files and the tester's `Writer`/`Members`/`Readers`/`Streams`. Round 1's reports are
`notes/review/mvccfull-f1-{api,newlessor,tester}-r1.md`.

**Checks run.**
- `etc/lean-check.py -a` on `NewStoreR`, `newWatchableStoreR`, `NewR`, `NewStoreLineup` and
  `NewStoreSessReal`: 0 errors. The only `sorry`s are the three `spec_of_specR` and the glue
  `api.New.specR_of_internal`.
- `runner__restore.olean` was built at 23:54, after its last edit (`087571a6e3`). A later
  `Writer.lean` commit (`78d5d6a5c4`, which adds `wbStock`) makes it out of date, so
  `lake build --no-build` now reports it stale. I did not rebuild it. The change is additive, so the
  risk is low.
- Go: `server/storage/mvcc/kvstore.go` under `.lake/go-src/etcd` (`ce3dbc0`) and
  `examples/mvccfull/mvccfull.go`.
- I found **no bug in the Go code**, so nothing goes to `issues/`.

**Round 1 findings at `HEAD`.** All are addressed (stale):
- API: F1.1 to F1.4 and F2.1 to F2.3. F2.1 is now settled by restating R1.
- Tester: F1 to F5 (`nrev`, the `1 ≤ revLo` / `revHi < 2^62` bounds, `MainConfig`, `hashing.lean`,
  `1 ≤ nw` in `writerOwn`).

## Ranking (need of revision)

1. **`runner.open` / `runner.newMember`, and `runner.restart` with them.** T1: the post's
   `Ops ≤ k` cannot be proved without a bound on `Ops`.
2. **The internal chain's `spec_of_specR` corollaries** (`NewStoreR`, `newWatchableStoreR`, `NewR`).
   T2: in compaction mode, no caller can meet their pre.
3. **`runner.restore.spec`, `runner.write.spec`.** Second tier: a redundant premise, and the loop
   invariant is missing from the write outline.
4. **`lessorW` / `writerOwn`.** Second tier only.
5. **The internal `specR`s themselves, and the glue outline.** Sound, and they need only what the
   body uses. Second tier: `restore_of_storage` is private, and the API `NewStore.specR` has no
   glue.

---

## First tier

### T1. `open.spec` and `newMember.spec` promise `Ops ≤ k` write-back tokens but take no bound on `Ops`

- **Principle.** The spec must be provable: the post asks for more than any proof can produce.
- **The post.**
  - `runner__open.lean:62`: `(sint.Z cfg.Ops').toNat ≤ k`, where `k` is the count of tokens in
    `bkKeep` (`ownToks bk.γB.wb k`, `Writer.lean:448-453`).
  - `runner__newMember.lean:45`: the same.
- **The only source of those tokens.** `inc_open_backend` (`Writer.lean:816-823`) splits them out of
  the fresh backend's `ownToks γB.wb wbInit`, with `wbInit = 2^40 - 1` (`InvNew.lean:36`). Its
  premise is `receiptBound GF + k + 4 ≤ backend.wbInit`.
- **What restore does.** `runner__restore.lean:314-317` meets that premise at `k = Ops + 1` only
  because of the new premise `sint.Z cfg.Ops' < 2^38`. That premise is change 3 of
  `notes/mvccfull-probe-writer.md`.
- **The gap.**
  - `open` has `ops.length < 2^38` but nothing on `cfg.Ops`.
  - Neither has `newMember`.
  - `writerCtx` (`Writer.lean:542-556`) holds none either.
  - So for `Ops ≥ 2^40 - 4 - receiptBound`, the post asks for more tokens than exist.
- **Effect of the Probe change.** Change 4 (`ReceiptBoundLe 2^38`) fixed half of this premise for
  `open` and left the `Ops` half open. The notes say "open and restore were unprovable", but only
  `restore` got the bound.
- **Who is affected.**
  - `open.wp_proof` (`sorry`) and `newMember.wp_proof` will stall here.
  - `restart` calls `open`. It is proved, but it has no bound on `Ops` (`runner__restart.lean:35-38`)
    and would have to supply one.
- **Restatement**, one of:
  - (a) Add `0 ≤ sint.Z cfg.Ops' ∧ sint.Z cfg.Ops' < 2^38` to `writerCtx`, as a pure conjunct.
    - `Run` builds `writerCtx` and has the bound from `runCfgOk` (`Run.lean:57`).
    - `open`, `newMember`, `restart`, `restore` and `write` then all have it for free.
    - Drop the explicit `sint.Z cfg.Ops' < 2^38` from `write` (`runner__write.lean:38`) and
      `restore` (`runner__restore.lean:49`).
    - This is the recommended option: one statement instead of five premises.
  - (b) Add `sint.Z cfg.Ops' < 2^38` as a premise to `open`, `newMember` and `restart`.
- **The callers can meet either:**
  - `Run` (`runCfgOk`);
  - `write` (its own premise);
  - `restore` (its new premise).
- **Obligations that get harder:**
  - `restart`'s proof needs one more argument for `wp_open` under (b), none under (a).
  - `Run` must put the bound into `writerCtx` under (a).

### T2. In compaction mode, the corollaries ask for the fixed contract and the unfixed registration together

- **Principle.** Every premise needs a source; a corollary meant for callers must be meetable.
- **What the pre takes.**
  - `NewStore.spec_of_specR` (`NewStoreR.lean:164-178`) takes `∀ s γ, storeBackendT b s γ P` and
    `restoreRegM d`.
  - So do `newWatchableStore.spec_of_specR` (`newWatchableStoreR.lean:98-109`) and
    `New.spec_of_specR` (`NewR.lean:97-107`).
- **Why both cannot be held in compaction mode (`d.cm = true`).**
  - `restoreRegM d` is `dlInit d.γB` (`RestoreVocab.lean:139-140`). That is the whole fraction of
    the flag `dghostVar γ.dlb (own 1) false` (`DelKeys.lean:49-51`).
  - The only way to a `storeBackendT` in compaction mode is `storeBackendT_of_backendC`
    (`BackendBridge.lean:3695-3725`). It needs `storeDlReg d.γB γi`, which `storeDlReg_fix`
    (`InstanceLaws.lean:125`) makes by consuming `dlInit`. It persists the flag at `true`
    (`dlReg_fix`, `DelKeys.lean:55-65`).
- **The callers the docstring names.** `NewStoreR.lean:150-163` says the compaction-mode callers
  "migrate to it": `NewStoreApi`, `NewApi`, and `StoreBackend`'s `NewStore_backend`. They fix the
  registration before the call:
  - `NewStoreApi.lean:145`: `storeDlReg_fix … Hdl`;
  - `StoreBackend.lean:139-161`.
  After that, `dlInit` is gone. So in compaction mode the corollary's pre cannot be met.
- **Soundness.** The statement is still true, and provable from `specR` through
  `storeSessT_of_storeBackendT` and a wand that ignores the fix. It is just useless where the
  docstring says it is used.
- **Restatement**, one of:
  - Give the corollary `specR`'s own form of the contract:
    `∀ s γ, storeSessT b s γ P` and `∀ s γ, restoreFixM d γ -∗ storeBackendT b s γ P`.
    - Compaction-mode callers then build it from `storeSessT_of_backendC` and
      `storeBackendT_of_backendC` (behind the wand), keeping `dlInit`.
    - Off-mode callers build it from `storeSessT_of_storeBackendT` and a constant wand.
  - Or restrict the corollary to `d.cm = false`, and say that compaction-mode callers use `specR`.
- Either way, fix the docstring's list of migrating callers.

## Second tier

- **S1. `restore.spec` has a redundant premise.**
  - `ops.length < 2^38` (`runner__restore.lean:48`) follows from the two new premises,
    `ops.length ≤ Ops` and `Ops < 2^38`. Drop it, or drop both new ones under T1(a).
  - Better still: put `ops.length ≤ Ops` in `writerOwn` next to `v0.ops = ops.length`
    (`Writer.lean:596`).
    - It is a state invariant: `write` appends only while `l.ops < Ops` (`mvccfull.go:1503-1507`).
    - `Run` starts at `ops = []`.
    - `write`'s post (`ops'.length = Ops`) is consistent with it.
- **S2. `write`'s outline does not name the invariant that `restore` now needs.**
  - `runner__write.lean`'s proof header gives the loop invariant as "`writerOwn` (with
    `nv ≤ 3·|ops|`)".
  - `restore` now needs `ops.length ≤ Ops` at every iteration. It holds because case 0 appends only
    under the loop guard. Add it to the outline, or take S1's `writerOwn` route.
- **S3. The glue reuses a private lemma.**
  - `api.New.specR_of_internal`'s outline (`NewR.lean:148-182`) reuses the body of
    `restore_of_storage`. That lemma is `private` in `RestoreApi.lean:80`, and it quantifies over
    `γ.withPhys p` for a fixed `γ`.
  - Every lemma it uses already quantifies over all `γ`: `keyCleanRead_of_backendC`,
    `storeBackendTR_of_backendC`, `restoreImageM_of_openOn`.
  - Generalize it to `∀ γ` with `γ.bucket = γb ∧ γ.kb = some d'` and make it public (one bridge for
    `Restore` and `New`).
  - Export `fkV d'.γB true`. `storeSessT_of_backendC` needs it (`NewStoreSessReal.lean:77`), and
    today it can only be read back out of `restoreImageM`.
  - Without this, the glue duplicates about 70 lines.
- **S4. No glue for the API's `NewStore.specR`.**
  - `ApiNewRestoring.lean:97` states the API `NewStore.specR`, but nothing derives it from
    `mvcc.NewStore.specR`. `NewR.lean` has only `New`'s glue.
  - The server's `server_kv_backend` (etcdserver `Results.lean:955`) reaches `NewStore` through the
    API. So Freeze needs this glue too, or the API candidate should be dropped.
- **S5. `lessorW` holds the current contract and a contract that implies it.**
  - `lessorW` (`Writer.lean:457-464`) holds `lessorBackend lp … bk.be …` and now also
    `lessorApplyOk lp` (`SnapRO.lean:138-143`).
  - `lessorApplyOk` gives the former from `isBackend` (in `bkKeep`), `plHookRO γB f` with
    `f ≠ nil` (`hookIs`), and a `rwLens`.
  - This is optional: keeping only `lessorApplyOk` plus a projection law makes `restore` and `open`
    uniform. `restore`'s proof (`runner__restore.lean:582-620`) already derives the new backend's
    contract this way.
  - The change is additive and its source is right: `NewLessorR.lean:143` gives `lessorApplyOk`, so
    `open` has it, and `Recover` keeps it because it is persistent.
- **S6. A fragile instance workaround.**
  - `Writer.lean`'s `attribute [local instance high] mvccfull.mvccState_countable …` works around
    mvccrand's duplicate `Countable` instances.
  - It changes no statement. But any importer that elaborates `memberState` and `incW` under the
    other instance gets ghost names that no longer match.
  - Make the shared instance module the notes propose (`mvccfull-probe-writer.md`, change 1) before
    Freeze.

## 1. B3's internal chain: what is good

- **True of the code.**
  - `NewStore` (`kvstore.go:87-133`) does, in order:
    1. `SetRangeDeleter`;
    2. the batch session (`BatchTx`, `LockOutsideApply`, `UnsafeCreateBucket`,
       `UnsafeCreateMetaBucket`, `Unlock`, `ForceCommit`);
    3. `restore()` under `s.mu`.
  - `restore()` (`kvstore.go:317-426`):
    1. reads the records under a `ReadTx`;
    2. attaches the leases;
    3. calls `RUnlock`;
    4. then, if there is a scheduled compaction, calls `compactLockfree`.
  - The restated pre matches this order:
    - **The session.** It uses only `storeSessT`'s `BatchTx` and `ForceCommit` clauses
      (`NewStoreSess.lean:64-89`). `batchTxInitSpec` (`InvStore.lean:1758-1769`) names neither
      `Del` nor `NC`.
    - **The clean read.** It is lent `storeRT ∗ restoreRegM d` and gives it back at `RUnlock`.
    - **The fix.** It comes before the compaction it resumes: `storeSess_fix`,
      `restoreDone_fix` (`NewStoreLineup.lean:85-104`).
  - So the registration is fixed only once no reader depends on it being unfixed, exactly as in
    `store.Restore`.
- **Says only what the body needs.**
  - `RC` is gone, and the separate bridge lemma with it.
  - The session's `P` comes from `LockOutsideApply`'s post (`InvStore.lean:1761`).
  - Its `storeReq γ True True` comes from `storeReq_true` (`NewStore.lean:486`).
  - R2 (the view stays clean through the session) needs nothing new: the client keeps the whole
    `bViewC` (`notes/mvccfull-probe-r1.md`, "R2").
- **Derivable from the API's callers.** Each piece the glue needs is already a proved lemma:
  - `restore_of_storage`'s body (`RestoreApi.lean:136-195`) produces, from `mvccStorageFor`, the
    image, the receipt, the clean read lent `storeRT ∗ restoreRegM`, the fix wand and `restoreRegM`.
  - `storeSessT_of_backendC` (`NewStoreSessReal.lean:34-108`, proved) adds the session contract,
    with no registration, at the `fkV … true` that `restore_of_storage` derives.
  - So every caller of `api.New.specR` can reach the internal pre:
    - the tester's `open`;
    - `restart` through `open`;
    - mvccrand and the server through the proved `New.spec_of_specR` (`ApiNewRestoring.lean:135-167`).
  - Caveat: only in compaction mode, since `mvccStorageFor` gives `d'.cm = true`. That is all the
    API needs. Only `NewStore_backend` reaches the off branch.
- The three files agree word for word on the changed pre (`NewStoreR.lean:101-108`,
  `newWatchableStoreR.lean:52-58`, `NewR.lean:54-60`), and `RC` has left the posts.

## 2. The tester's changed specs

- **`ReceiptBoundLe GF (2^38)` in `open`, `newMember`, `restart`, `restore`, `write`.**
  - It is right, and it is needed: `receiptBound + (Ops + 1) + 4 ≤ 2^40 - 1` with `Ops < 2^38`.
  - Every caller already holds `2^38`: `Run` (`Run.lean:64`), `Main` (`Main.lean:36`), and the
    runner specs among themselves. No mvccfull spec is left at `2^48`.
  - The mvcc API's `2^48` follows by `ReceiptBoundLe.pow_succ` (Perennial `Bounds.lean:101`).
  - The half that is still missing is T1.
- **`restore.spec`'s new premises are true and needed.**
  - `nb + 1 ≤ Ops`: the builder's file must be among `writerOwn`'s unused ones (`Writer.lean:598-599`).
  - The builder's grants need write-back tokens (`Ops ≤ k + b.ops`).
  - The kept `Ops + 1` tokens of the snapshot backend must fit in `wbInit`.
  - The post's `nb + 1` follows from `v1.ops < v0.ops` and `nb = v0.ops → v1.ops = v0.ops`.
  - The caller `write` holds the premises (but see S1 and S2).
- **`lessorW`:** see S5. **`writerOwn`:** its only change is through `lessorW`. It already had
  round 1's `1 ≤ nw` (`Writer.lean:601-603`).

## 3. Callers whose obligations got harder

| Changed statement | Caller | Still met? |
|---|---|---|
| internal `NewStore`/`newWatchableStore`/`New.specR` (session + fix wand + `restoreRegM`) | `api.New.specR_of_internal` (`sorry`) | yes, by the outline (S3) |
| the same | the `spec_of_specR` corollaries and their compaction-mode users (`NewStoreApi`, `NewApi`, `NewStore_backend`) | **no** (T2) |
| `restore.spec`: `ops.length ≤ Ops`, `Ops < 2^38` | `write` | yes, if it carries `ops.length ≤ Ops` as a loop invariant (S2) |
| `ReceiptBoundLe 2^38` | `Run`, `write`, `restore`, `restart`, `newMember` | yes |
| `lessorW` gains `lessorApplyOk` | `open` (`sorry`; from `NewLessorR.lean:143`), `restore` (proved), `restart` (through `open`) | yes |
| T1's fix (bound on `Ops` for `open`/`newMember`) | `Run`, `restore`, `restart`, `write` | `restart` gains a premise under T1(b), none under T1(a) |

## Uncertain (not verified)

- That `runner__restore.lean` still builds after `78d5d6a5c4` (stale `.olean`, see above).
- That `bkKeep`'s write-back tokens are bounded by an authority in the backend's invariant. T1 does
  not depend on it: `inc_open_backend` is the only source of the tokens, and it needs the bound.
- The glue's steps 5 to 8 (`NewR.lean:168-182`). I read them against the post's definitions but no
  proof exists.
