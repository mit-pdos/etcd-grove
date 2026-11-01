# mvcc's API: candidate specs (2026-11-01, branch `worktree-mvcc-rand-tester`)

The user asked for new candidate specs of etcd's mvcc package, written in the Lean spec files,
designed with the `spec` skill, good enough for etcd's proof and for the randomized tester
(`examples/mvccrand`, `notes/mvccrand.md`). **Status: candidates for review.** They typecheck;
nothing proves them, and no proof uses them; today's specs and proofs are untouched.

- The vocabulary: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean` (new).
- The specs: `<F>.specC`, appended to each function's spec file next to today's `<F>.spec`
  (27 functions: `New`, `store.Read`/`Write`/`Rev`/`Commit`/`Compact`, `watchableStore.Write`/
  `Close`/`NewWatchStream`, `metricsTxnWrite.Range`/`Put`/`DeleteRange`/`Rev`/`FirstRev`/
  `Changes`/`End`, `watchableStoreTxnWrite.End`, `NewReadOnlyTxnWrite`,
  `txnReadWrite.Range`/`Rev`/`End`, `watchStream.Watch`/`Chan`/`RequestProgress`/
  `RequestProgressAll`/`Cancel`/`Close`). Side by side rather than in place so that the build stays
  green while they are reviewed: adopting them replaces each `<F>.spec` (and its proof).
- Out of scope: the store's own `Put`/`DeleteRange`/`Range` (`writeView`, `readView`: no caller in
  etcd's proof or the tester), `Restore`, hashing, `NewStore` (etcd uses `New`), the internal
  functions.

## The design

Today's specs are written in the implementation's terms: reader slots (`storeReaderC`), revision
tokens (`ownToks γ.revs`), the index's certificates (`idxCert`, `crevLb`), the caller's
certificate map (`certOk`, `certOkNext`), the writer's fragments (`writerFrag`, `watchWriter`,
`logQ`), the reader's tag `Z`, the internal ghost names (`StoreNames`, `WsNames`, `WatchParams`).
A client reasons about the log it read through a floor (its certificate), an upper bound (the
tokens) and the pin these give the sole writer (`txn/SoleWriter.lean`).

The candidates follow the reviewed examples (`.claude/skills/spec/examples/put.md`, `range.md`):
the API's abstract state, owned by the client, and linearizability as the caller's atomic update.

- **The state** `mvccState γ σ`, `σ : MvccState = {log, crev}`: mvcc's own history (every
  revision's changes, `stateAt σ.log r` the state at `r`; compacted revisions stay in the model
  and read as `ErrCompacted`) and the compaction revision. The server's `KVState` (base store at
  the compaction revision, later changes) is a function of it.
- **Reads** (`Read`, `Rev`, `Watch`'s registration) fire the caller's update at the state they
  read, unchanged. A reader that knows a revision was written (it is in its invariant's state)
  reads at least it: the floor is the state, not a certificate.
- **A write transaction** (`Write` ... `End`) is pinned to the state `σ` it began at
  (`mvccTxn_write_agree`: it holds the batch lock and `s.mu`, so no write and no compaction can
  change the state before its `End`); its operations extend its pending changes `pend`; `End`
  commits them by the caller's update (`σ' ↦ σ'.commit pend`). The sole writer's exactness is the
  law, not a token budget.
- **Watches**: the watchable store sends a revision's events before it bumps the revision (a read
  that starts after an event was received may still see the revision before it). So reads stay
  exact, linearized at the bump, and watch events may be ahead by the revision being committed:
  they come from a log the client **announced** (`mvccAnn γ r L`, the client's own map from a
  revision to a log; `watchableStoreTxnWrite.End` takes the announcement of the log it commits),
  so the client relates them to its records. Laws: the events received for a watcher are its
  range's events, filtered, of the revisions `[lo, hi)` of an announced log (`wsRecv_events`); a
  progress response (per watcher, or `-1` for the watchers registered before it was sent and not
  cancelled) comes after every event up to its revision (`wsRecv_progress`); each response's
  revision is at or above its events' (`wsRecv_resp`). The registration (`Watch`) fires the
  caller's update, so a watcher from revision `0` knows its first revision (`σ.rev + 1`).
- **The lessor**: any implementation meeting the store's need (`isMvccLessor le γl R`: the four
  triples of today's `isLessor`, over any interface value; `R` the real lessor's reader slot).
- **Resources**: the caller's `threadTok` (lent to a transaction until its `End`) instead of
  reader slots; no write token: `New` takes the receipt-paid write-back supply once.
- **Hook**: the batch lock's invariant `P` and the post-lock hook `f`, frozen on the backend
  (`mvccHook γ P f`; `nil` allowed: `hookRun` is then the caller's update); `Write` runs it from
  the caller's `Pre` to `Q`, `End` takes `P` back.

## Decisions for the user (new client-owned ghost state and premises)

The skill's policy: each new premise or client-owned ghost state on a spec with clients is the
user's decision. Today's statement beside the candidate's:

1. **The client owns the store's abstract state** (`mvccState γ σ`, from `New`). Today: the
   caller's certificates and tokens (`idxCert γ.idx log`, `ownToks γ.revs m`, `certOk γ log`)
   bound the log it reads. Alternative: keep today's, and add the abstract state as a layer above
   (which the certificate style cannot express without the implementation's ghost names).
2. **The client's announcements** (`mvccAnnAuth γ M`, `mvccAnn γ r L`; `watchableStoreTxnWrite.End`
   takes `⌜pend = []⌝ ∨ mvccAnn γ σ.log.length (σ.log ++ [pend])`). Today: the caller's certificate
   map (`ghostMapAuth γ.cok`, `certOkNext γ.st ilog pend`), the same mechanism under internal names.
   Alternative: commit at the notification (the state then runs ahead of the revision reads see,
   and reads must answer from a past state, `range.md`'s form); the candidate keeps reads exact.
3. **`New`'s premise `threadBound GF ≤ 2 ^ 30`** (the store's readers are the threads; Go's
   `RWMutex` allows `2 ^ 30` readers). Today: reader slots, one per reader, handed out by `New`. The
   examples' closed theorems take `n + 2 ≤ 2 ^ 31`: they would need `n + 2 ≤ 2 ^ 30`.
4. **`New`'s premise `□ (⧗ 1 ={⊤}=∗ backend.wbTok d.γB)`** (write-backs paid from time receipts,
   M2's `kbWTSupply`, given by the backend's creator). Today: two write tokens to `NewStore`, then
   one per `Write` (`storeWT`) and `Commit`. Alternative: keep the per-call token.
5. **The lessor generalized** (`isMvccLessor`, with its resource `R`). Today: `isLessor` (the real
   `*lessor` only), which excludes `FakeLessor`. The real lessor meets the general contract with
   `R := lease.lessorRd lp γl` (today's `isLessor` minus `lessorPin`).

Dropped premises (each today's, none needed by the code under the candidate's ownership): the
reader tags `Z` (always `True`), `crevLb` floors, `NoDelPutAt` (already gone in M2 on `lean`),
`L.length + 4 ≤ 2 ^ 63` (a law: every state's changes are fewer than the receipts),
`writerFrag`/`writerOwn` on `Commit`, the compaction right (`Compact` is linearizable under
`s.mu`; concurrent compactions are serialized by it).

## Complete for etcd and for the tester (the argument; not proved)

- **The sole writer** (etcd's apply thread, the tester's writer) holds `mvccState` in its
  invariant; the agreement law gives it the state each write transaction began at, exactly (today:
  `pinned_sole`). Its reads (`Txn`'s compare) see that state.
- **A linearizable read** (etcd's request goroutines, the tester's readers): the client's
  invariant ties `mvccState`'s revision to what it published (etcd: the applied index the read
  index waited for; the tester: the writer's published revision); the read's update fires at the
  current state, whose revision is at least it (today: `store.Read`'s `log₀ <+: log`).
- **The read's revision is in the client's records**: the update fires at the state the client's
  invariant holds, so it is the client's (today: `certOk` and the client's map).
- **Watches** (etcd's `v3rpc` watch server, the tester's watch stream): events from announced logs
  (the client announces its own pending log before `End`: etcd's server already does, with
  `certOkNext`), progress per watcher and for the stream (the tester's checks), the registration's
  first revision (etcd's clients watch from `0`).
- **Leases**: puts with a lease keep the item map (as today); `Revoke` (the lease package's spec,
  not changed here) would take the announcement of its exact deletions (the keys the item map puts
  on the lease, sorted), which its caller can compute, in place of today's `∀ pend,
  certOkNext γ log pend` (unsatisfiable for a caller that uses its map: `notes/mvccrand.md`).

## Open

- **The key's bound on `Put`** (`(k.length : Int) < 2 ^ 63 - 1`): kept from today's spec; its
  reason is to be found (not obvious in `put`'s Go code).
- **The backend boundary is unchanged**: `New` takes what today's `NewStore_backend` takes of the
  real backend (`isBackend` at `lateW`, `keySized`, `bkView`, `bkNoCmp`, `lateReg`, `bkRTx`), which
  names implementation ghost state (`lateW` registers the store's names); a design of its own.
- **Compaction over the real backend**: `Compact.specC` is stated unconditionally (true of the
  Go code); proving it needs M2's backend compaction model (`KBReal.cm`).
- **The watch id `0`** (`AutoWatchID`) on `Watch`: a scope restriction (etcd's client never
  chooses one); a caller's id adds the `ErrWatcherDuplicateID` arm.
- **Compaction responses** (`WResp.compactRev ≠ 0`): only that they carry no events and are at
  most the compaction revision; what follows them for the watcher is not stated.
- **`Changes`' slice read-only** (`chs ↦*□ ps`): the transaction only appends later; to check
  against the proof of `put` (today's spec hands the slice over and seals the transaction).
- **The laws are obligations**: an implementation proves each `<name>.law` over its definitions
  of the opaque predicates; until then nothing rests on them.
