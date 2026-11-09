# Batch 3e (mvcc's core), provability review, round 1

Reviewer: provability (`notes/specs-only/review-brief.md`). Scope: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/{Model,ApiStorage,Api,Internal,InternalIdx,InternalStore,InternalTxn}.lean`
and the store/transaction/compaction/restore/hash specs, snippets `examples/specreq/mvcc/`, the
`from 3e` requests. Go: the pinned fork (`.lake/src/server/storage/{mvcc,backend}`, `pkg/schedule`).
`batch-3e.md` read only after the findings below were written.

## What is good

- **The read path matches the code exactly.** `rangeOut`/`rangeResult` (`Model.lean`) against
  `storeTxnCommon.rangeKeys` (`kvstore_txn.go:73-152`) and `treeIndex.{Revisions,CountRevisions,Range}`
  (`index.go:107-196`): `ErrFutureRev` with `Rev: curRev`, `ErrCompacted` with `Rev: 0`, `Count: -1`;
  `ro.Rev ≤ 0` read at the current revision; count-only counts all; keys-only from the index with
  lease 0; the limit stops the index (count = number returned unless `WithTotalCount`); a `nil` end
  (`decide (endk = slice.nil)`) vs an empty one (no upper bound, `index.go:95`); the context checked
  only on the full path, between keys (`.ctxErr` only when neither count- nor keys-only).
- **The compaction check reads `tr.s.compactMainRev` unlocked** (`kvstore_txn.go:81`); the spec's
  `k.state.crev` is right because every writer of `compactMainRev` (`Compact`, `Restore`,
  `NewStore`'s `restore`) holds `s.mu` for writing and every transaction holds its read side.
- **Writes.** `putRec`/`putEv` are `storeTxnWrite.put` (`:223-291`: the index read at `beginRev+1`,
  so the transaction's own events count; created kept, version + 1); `putLs` is the code's lessor
  steps (`GetLease` only when present, the early return on equal ids, `Detach` errors logged,
  `Attach` errors panic: hence the liveness premise); `deleteRange` at `beginRev(+1)`; `DeleteRange`'s
  returned revision (`:197-202`); `Changes` length; a write transaction's `FirstRev()` is `0`
  (`store.Write`, `:179`) — and the batch report's consequence for `checkRange` (`txn/range.go:180`:
  a negative range revision fails `ErrCompacted` in a write transaction, not in a read-only one at a
  never-compacted store) is true.
- **`End`'s two updates** (notify, bump) both fire inside `revMu`'s critical section of
  `storeTxnWrite.End` (`:209-221`), with the write-back (`Unlock`) in it, so a read that sees the
  new revision sees the new data; the `σ = σ₀` obligation is dischargeable because the transaction
  holds `s.mu`'s read side and the batch lock (only `Compact`/`Restore` change the state otherwise,
  and they need `s.mu` for writing).
- **Compaction.** The fork has etcd-io/etcd#22377 (`key_index.go:276-286`, `isRecreatedAt`), so
  `issues/etcd-compaction-delete-then-put.md` does not block. `KV.Compact`'s three arms are
  `updateCompactRev` (`kvstore.go:197-222`) exactly (hook and commit only on success; `nil` channel
  only on `ErrFutureRev`). `compactBarrier`'s re-schedule branch (`:144-150`) is unreachable as the
  report says (`close(stopc)` precedes `Stop()` in `Close` and `Restore`), so the schedule-after-stop
  panic (`schedule.go`, `Schedule`) is not reachable either. `storeCfgOk` is needed (a negative
  batch limit hangs `scheduleCompaction`, `kvstore_compaction.go:68`).
- **Restore from any image.** `restore` (`kvstore.go:317-426`): `currentRev` raised to the finished
  and scheduled keys is consistent with an image's last revision being `h.rev` (a compaction keeps
  each key's last change at or below it, a tombstone at exactly the compaction revision included,
  `key_index.go:276`); `RestoreLs` (any map order, `Attach` failures logged) is the code; the
  `u`-resumption runs the hook once and one commit (`SetScheduledCompact` + `ForceCommit`).
- **`Unlock`'s row** is true of etcd's backend for deletes too: `batchTxBuffered.Unlock` commits when
  a delete is pending (`batch_tx.go:355`), so the compaction's deletes are visible when it returns.

## First tier

### F1. `KV.Compact`'s premise `1 ≤ rev` is not what its caller can give (a user not served)

`Api.lean`, `KV.Compact.contract`: `⌜1 ≤ sint.Z rev⌝`. The apply passes the client's revision
unchecked (`etcdserver/apply/backend.go:73`); the server's own premise is `rev ≠ 0`
(`Spec/.../etcdserver/EtcdServer__Compact.lean`, "The premise `rev ≠ 0`"), and the applier's spec
admits any compaction op (`apply/applierV3backend__Compaction.lean`: `op.ok`, which says nothing of
the revision, `apply/Api.lean:501-517`). A negative revision is reachable and the code handles it:
`rev ≤ compactMainRev` (`kvstore.go:199`, `compactMainRev ≥ -1`) gives `ErrCompacted`, which the
contract's second disjunct already states (`σ.crev ≥ -1 ≥ rev`). Only `rev = 0` at a never-compacted
store needs excluding (it succeeds where W0's model refuses).
**Fix**: `⌜sint.Z rev ≠ 0⌝`; tell 2d its applier needs `rev ≠ 0` from the op (W0 already answers
`ErrCompacted` for `rev ≤ compacted`).

### F2. `ReqCompactErrors` is unprovable: no spec says the `ErrCompacted` channel is non-`nil`

`compact.go`, `ReqCompactErrors`: `if !errors.Is(err, smvcc.ErrCompacted) || ch == nil { panic }`.
The contract's `ErrCompacted` arm gives only `compactChanOk ch`, which a `nil` channel also meets (a
receive on `nil` blocks; it never panics). The code returns `make(chan struct{})`
(`kvstore.go:200`); so does the success arm (`:235`). **Fix**: `⌜ch ≠ chan.nil⌝` in the success and
`ErrCompacted` disjuncts (the `ErrFutureRev` one already says `ch = chan.nil`).

### F3. No client can take a reader token: `mvccTokN` has no law (snippets unprovable)

`Api.lean:104`: `opaque mvccTokN : Nat`, sealed; `NewStore`/`New` give `mvccReaders γ mvccTokN`;
the only law is `mvccReaders_split`. Every read (`Rev`, `FirstRev`, `Range`, `Read`, `Write`, `Put`,
`DeleteRange`, `HashByRev`, `Hash`) takes `mvccReaders γ 1`, which needs `mvccTokN = 1 + m`: not
derivable (it may be `0`). So `ReqBoot` (`kv.Rev()` after `NewStore`), and every snippet whose
tokens come from a constructor, cannot start. Likewise `mvccReaderN` (`ApiStorage.lean:172`): 4a's
opener must hand over `kbRdToks B mvccReaderN` (`req/..._backend.md`, item 2) without knowing the
number, and nothing bounds it by the storage's real limit (Go's `RWMutex` readers, the
`concurrentReadTx` wait group). **Fix**: a law giving the bound the server needs
(`K ≤ mvccTokN` for the constant the bounds plan fixes at adequacy, or `mvccTokN` a parameter of
`NewStore` with `mvccReaderN = mvccTokN + 2 + 1`, the loops' and the open token's slots stated), and
a law (or a 4a premise) relating `mvccReaderN` to the storage's slot count. The snippets'
`Assumes:` should also say which reader tokens they hold (none does).

### F4. Two `keyBackend` rows are false of etcd's backend (4a cannot prove them)

`ApiStorage.lean:244-255, 285-286` (`rangeOk` on a read transaction, `kbRead B rt D`):

1. **Empty end, non-`nil` slice.** `bkRange` reads `e = []` as "the key alone". The contract's
   `es ↦*{de} e` admits a non-`nil` empty slice. `baseReadTx.UnsafeRange` forces `limit = 1` only
   for `endKey == nil` (`read_tx.go:79-82`); for an empty non-`nil` end with `limit ≤ 0` it sets
   `MaxInt64` and **panics on `Meta`** (`:86-88`, `Meta` is not a safe-range bucket), and on `Key` it
   can return the key twice (from the write buffer and from bolt, `:89, 120`).
2. **The merge is not a sorted, cut range.** A read transaction returns bolt's entries followed by
   the write buffer's (`read_tx.go:120`: `append(k2, keys...)`), with bolt's part cut at
   `limit - len(buffer part)`. With entries of the bucket in the buffer (a write since the last
   commit) the result is not "`[k, e)` in key order, cut at `limit`": committed `1..100`, buffered
   `101..105`, limit 10 gives `1..5, 101..105`. For an arbitrary `D` (the contract's `UnsafePut` row
   admits any key) it is not even sorted.
   mvcc relies on the cut: `restore`'s chunked scan (`kvstore.go:346-362`, `ReadTx`, limit
   `restoreChunkKeys`, the next chunk after the last key returned) would skip committed entries (and
   `restoreIntoIndex`'s `verify` would fire) if `Key`'s buffer held entries. It works in etcd only
   because the buffer is empty there (`NewStore` force-commits just before, `:125`; a `Restore`'s
   new backend has had no `Key` write). 3f's `rangeEvents` (no limit) relies on the order, true for
   `Key` only because its keys are revisions put in increasing order, which the contract does not
   say.

**Fix**: (1) require `es = slice.nil` when `e = []` (all of mvcc's single-key reads pass `nil`:
`kvstore_txn.go:126`, `store.go:23, 31`); (2) either state the read transaction's range as etcd
computes it (`D` split into committed and buffered parts), or give the rows what makes the simple
statement true: `UnsafeSeqPut` of `Key` above every key present (the code's revisions), and a
limited range on a read transaction only of a storage whose `Key` buffer is empty (a `kbClean B`
that `ForceCommit` gives and a `Key` put's `Unlock` takes), carried by `mvccStorageFor` to `restore`.

### F5. `Restore`'s post claims every reader slot of the old storage, which the code does not give

`KV.Restore.contract` gives `storageRest B` = `kbRdToks B mvccReaderN` (all slots). `store.hashByRev`
takes the old storage's shared `ReadTx` read lock, releases `s.mu`, and keeps reading the old storage
(`kvstore.go:188-192`), so `Restore` (`s.mu.Lock`, `:293`) can return while a hash still holds a slot
of `B`. The batch report's open question 3 says "the specs as written assume the latter" (`Restore`
gives back all slots but those of hashes in flight): they do not; the statement gives all of them.
Nothing in Lean refutes it only because `HashByRev` is a trusted contract that does not mention the
storage, so the trust base silently asserts something false of the code (PRINCIPLES, "An
assumption states the physical fact the code relies on"). **Fix**: as the report's chosen option,
make `storageRest` (from `Restore`) the slots but a token-tracked number of in-flight hashes, with
the hashes' slots coming back through a resource the trusted `HashByRev` contract states (4a's close
waits for them: `batchTxBuffered.commit` takes `readTx.Lock`, `batch_tx.go:376`); or put the decision
to the user with the statement matching it.

### F6. The trusted `Hash()` contract asserts no panic of code with a data race on `s.b`

`HashStorage.Hash.contract` ("any hash, revision and error", reader token only); the fork's
`store.hash` reads `s.b` (an interface value) and `s.currentRev` with no lock (`kvstore.go:160-164`),
while `Restore` writes both (`:299, 305`) and nothing in the specs orders them (`Hash` holds a reader
token, `Restore` the open token and the whole share). A torn interface read can call a method on the
wrong receiver; `ForceCommit` on the old storage after the server closed it (`server.go:1140-1144`)
reaches `t.backend.begin` on a closed bolt DB, `lg.Fatal` (`backend.go:1103-1106`) — by reading,
not reproduced. `issues/etcd-mvcc-hash-currentrev-race.md` ("Proof") says exactly that a `Hash` spec
needs #22609 cherry-picked ("a racy read has no proof"); `ReqHash` claims safety "concurrently with
... restores". **Fix**: cherry-pick etcd-io/etcd#22609 into the fork before stating `Hash`, or give
`Hash` a resource excluding `Restore` (a share of the open token, as the frozen API's decision 10
considered), and update the issue file's "Proof" section either way.

## Second tier

- **S1. `mvccImage`'s intended realization is too weak for `restore`** (`ApiStorage.lean:49-58`:
  with `u`, "any subset of those the scheduled one's removes"). `restoreIntoIndex` rebuilds a key's
  generation from its first surviving entry (`ki.restore(created, rev, kv.Version)`) and counts the
  rest (`keyIndex.put`, `ver++`): a hole in the middle (revs `[2, 5, 8]`, `5` deleted but not `2`)
  gives version 2 at `8` where the history says 3: keys-only reads and the next put's version are
  then wrong. The job deletes in revision order (`kvstore_compaction.go:58-66, 92`), and a union of
  two jobs' prefixes (an interrupted job overtaken by a later `Compact`) is still, per key, a prefix
  of its revisions. State that ("per key, a prefix of the revisions the scheduled compaction
  removes").
- **S2. No law about `mvccImage`'s content.** Only `mvccImage_empty`; `store.restore`'s sketch
  (`RestoreEntsOk`, `idxRestore = h`'s index) and 3f's `rangeEvents` (req item 5, "from 3f": "a law
  of `ApiStorage.lean` over `kbRead`/`rangeOk` at an image would serve") have nothing to derive from.
  3f's item 5 is not answered in the batch report.
- **S3. Open question 1 (the compactor's `Rev()` after close), option (a) is not enough.** After the
  storage's close, `Rev` still runs `ReadTx().RLock()` (`kv_view.go:31-35`), whose row needs
  `kbObs B Ψ`, an atomic update over `kbData B`, which `storageRest B` handed to the backend's
  close. Lending the compactor one token also needs a closed-storage `RLock` row (no snapshot) or
  `kbData` kept out of `storageRest`. Say so in the question.
- **S4. Snippets' resources.** `ReqCompact`/`ReqViews`/`ReqReadFloor`/... call reads but their
  `Assumes:` name no reader token (with F3 fixed they are provable). `ReqCompact`'s full read at `rev`
  needs `Context.ctxDone` of `context.TODO()` refuted (a 1c law; cite it).
- **S5. `store__Read.lean`'s Margin is wrong in its reason**: "writers wait for `s.mu`" — writers take
  its read side (`kvstore_txn.go:175`) and commit while a read transaction is open; the statement is
  still right (`mvccTxn` pins the state it read; only `Compact`/`Restore` are excluded).
- **S6.** `mvccState_reachable`'s `σ.rev + 1 < 2^63` has no `ReceiptBoundLe` binder while
  `NewStore` has one: the sketch should say the invariant keeps the bound's persistent consequence
  from `NewStore` for later commits (`End` has no instance either).

## Snippets

Provable as written (with F3's token): `ReqReadFloor` (`Read`'s update at the current state;
`kvsFit` for positivity, `MvccReachable`/`EvsWf` for `ModRevision ≤ Rev`), `ReqSoleWriter`,
`ReqDeleteRange`, `ReqReadOnlyTxn` (`NewReadOnlyTxnWrite`, `mvccTxn_readOnly`), `ReqRangeErrors`,
`ReqViews`, `ReqCommit` (`storageReq_true`), `ReqCompact`, `ReqBoot`, `ReqRestore` (`storageRest`
to 4a's close), `ReqClose` (`mvccClosed_rest`), `ReqPutLease` (`putLs`/`delLs` worked through all
three cases, the lease live by assumption), `ReqRangeDeleter` (`mvccDeleter`, the attachment
invariant), `ReqHash` (modulo F6). Unprovable: `ReqCompactErrors` (F2).

## Go code

No new confirmed bug. By reading (not reproduced): `Hash` racing `applySnapshot` can call
`ForceCommit` on the closed old backend (F6), covered by `issues/etcd-mvcc-hash-currentrev-race.md`'s
race on `s.b` (fixed upstream by #22609, not in the fork).

## Ranking (by need of revision)

1. `Api.lean` (F1, F2, F3, F5, F6, S6) — the contracts `KV.Compact`, `KV.Restore`, `HashStorage.Hash`
   and the token constant.
2. `ApiStorage.lean` (F4, S1, S2, F3's `mvccReaderN`) — two contract rows, the image's realization.
3. `examples/specreq/mvcc/` (F2's snippet stands once the spec gives `ch ≠ nil`; S4).
4. `store__Read.lean`, `store__restore.lean`, `NewStore.lean` (S5, S1's consequence in the sketch).
5. `Model.lean`, `Internal*.lean`: no finding.

## Verdict

Not done: six first-tier findings. F1, F2 and F4(1) are one-line repairs; F3 needs a law; F4(2) needs
a decision on how the storage contract states a read transaction's range (or a "clean" resource);
F5 and F6 are open question 3 restated against the code, and need either the fork's fix (#22609) or
a statement matching the chosen option.
