# `etc/gates.sh` on `mvcc-api` after the R8 merge (2026-11-08)

The full build and the TCB check passed; three gates failed: bounds, mode, api. What was done, and
the baseline increases left for the user's review (one line of justification each).

## Bounds (`etc/bounds-check.py`, `notes/bounds-plan.md`)

Fixed:

- **spec-receipt in `storage/mvcc` (2 → 0).** The API's `New.spec`/`NewStore.spec`
  (`Spec/.../storage/mvcc/Api.lean`) had a premise `receiptBound GF ≤ 2 ^ 48`; they take
  `[ReceiptBoundLe GF (2 ^ 48)]` again, B1's form (`lean`'s internal `mvcc.New`/`NewStore` already
  did). Same strength; proofs adapted (`Api/NewApi`, `Api/NewStoreApi`, the call sites in
  `etcdserver/NewServer` and `examples/mvccrand/runChecks`).
- **stock in `storage/mvcc` (58 → 54) and `storage/mvcc/Api` (12 → 0), owner's matches allowed**
  (`etc/bounds-allow.txt`): the mvcc API owns the store's reader tokens. The storage abstraction's
  sealed definitions (`mvccStorageFor`, `storageRest` in `Api.lean`) and the bridge
  (`EtcdBackend.lean`) hold the backend's slots the pool is built from; `Api/RdSupply` (the pool
  `rdkPool`), `Api/NewStoreApi` (building it), `Api/RestoreApi` and `Api/ClosedLaw` (giving the slots
  back).
- **stock in `examples/mvccrand` (5 → 1), owner's matches allowed**: the test's own history lock
  (`RunChecksWorld` allocates the `RWMutex` and makes the `histRd` handles; `runChecks` hands them
  to its reader goroutines).
- Decreases recorded: `etcdstart` 24 → 20, `cluster3` 1 → 0, `client/v3` 19 → 16, `etcdserver`
  35 → 33 (stock).

Baseline increases (debt, for review):

- **spec-receipt `etcdserver` 9 → 13.** `EtcdServer.Start`/`start` had `acReceiptOk C` (a named
  predicate in a Proof file: `receiptBound GF ≤ 2 ^ 48` with auth on); strict M1 needs the bound in
  both modes, so they and the new `run`/`applyAll` premises state `receiptBound GF ≤ 2 ^ 48`. No new
  bound: the same premise, unconditional and now visible to the check. The fix is B1's instance
  binder down the apply path's specs (`run`, `start`, `Start`, `applyAll`, `apply`, `applyEntries`, …),
  a statement change to every caller up to the examples: not cheap here.
- **spec-thread and spec-readers `api/v3rpc` 1 → 3 each.** `serverWatchStream.sendLoop` and
  `watchServer.Watch` state `⌜threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders⌝` (for
  `GetProgressReportInterval`'s loan from the interval lock's pool). On `lean` the same premise was
  inside `sendRes`/`watchRunSlot` (Proof-file predicates the specs took); the migration spelled the
  resources out. No new bound. The fix is an instance (`[ThreadBoundLe GF (2 ^ 29)]`) on
  `GetProgressReportInterval`, `sendLoop`, `Watch` and their callers (B1).
- **stock `examples/mvccrand` 0 → 1.** `RunChecksBackend.wbToks_list` splits the backend's write-back
  tokens (`ownToks γB.wb k` into `k` `backend.wbTok`) to make the store's storage by hand, as the
  server's boot does through `etcdStorage_open.law`; a client of the backend counting its tokens.

## Mode (`etc/mode-check.py`)

Classified (`etc/mode-allow.txt`):

- `kvNxM` (`AuthCompRows`, the store's witness per mode): a model row, with `kvRunM`'s.
- `ServerOnDefs`' `kvLogsPubM`, `kvLogsPubM_iff`, `srvKVInvsM_uberOn` (4 literal modes): moved from
  `ServerOn.lean`, where they were `unmoved`; `ServerOn`'s count comment 7 → 3.
- `client/v3/WatchFire.srvKVCoreM_someNx` (2): model, the mode-generic lemma's `cases on`.
- `etcdstart/WatchSrv.srvWOk_of_readOn` (1): unmoved, the auth-on twin of `srvWOk_of_read` (as
  `memberUpOn`).

Baseline increases (for review): match-mode `etcdserver` 69 → 70 (`kvNxM`, R6's merge of `srvKVInvs`'
`kvNxOff` and `srvKVInvsOn`'s `kvNxOn`); lit-mode `client/v3` 16 → 17 (`WatchFire`'s two, one gone
elsewhere); lit-mode `etcdstart` 5 → 6 (`WatchSrv`). Decrease recorded: lit-mode `etcdserver`
143 → 142.

## API (`etc/api-check.py`)

- `etc/api/etcdstart.txt`: `WatchSrv` and `OnceUpTo` importable (R9 wrote them for the examples'
  watch clients); interfaces generated.
- `etc/api/backend.txt`: `DlLemmas` importable (theorems only, imported publicly by `InvBackend`, as
  its listed sibling lemma files; making the import private would leave the backend's own proofs
  that use it through `InvBackend` to import it each); `Spec...backend.New` importable (the
  constructor's spec; `examples/mvccrand` calls `backend.New` itself, the server goes through
  `storage.OpenBackend`). Interfaces generated.
