# The server-side clients of mvcc over the API (rounds 15-16): draft of the restated specs and invariant

Scope: the apply chain, the lease package (`Revoke`, `Grant`), the server's construction,
compaction, reads and snapshot path, and the examples' closed theorems that build a server. `txn` and
the watch path are drafted in parallel; their needs of this draft are answered in §(b) and §(c).

**The Lean draft** is `/home/ubuntu/.claude-D/jobs/e4ba2bf8/tmp/clients/server/ServerSpecs.lean`:
- It is a scratch file under namespace `srvApi`; a restated definition carries the suffix `A`.
- **It typechecks with no error or warning** against `mvcc-api` at `6cc29c14f0`, with
  `lake env lean FILE` from the worktree.
- Laws are stated as `abbrev …law : Prop`; two sanity theorems are proved (`logOk_of_receipt`,
  `dbImageA_of_send`).
- G3 is the API's `mvccImage_snapshot.law` (an update at the state, no pin predicate). Since
  `6cc29c14f0` it covers only a store that never compacted, and its pre takes `isMvcc`. The draft's
  §3b builds its update from `kvStoreInv` in a cluster that never compacts, and §3c states the
  sender's image over it. The compacting sender is deferred.
- No repository file was edited.

Paths below are under `Proof/go_etcd_io/etcd/server/v3/etcdserver/` unless they say otherwise.

## Superseded (2026-11-06, decided by the coordinator)

- **`lessor.Revoke.specA`'s update only for a live lease**: the precondition takes
  `if decide (id ∈ L) then auBegin γ σ₀ (auEnd γ σ₀ dels Y) else True`, and the not-live arm does
  not give the update back (it gave it back unused). The server builds the update from its writer's
  half, which no law recovers from an unused update, so after a not-live revocation the apply
  thread had lost its half of the store's state. The code returns `ErrLeaseNotFound` before `rd()`
  (`lessor.go`'s `Revoke`), as txn's `Put` for a lease. `revokeClause` follows
  (`notes/mvcc-migration/server.md`, "Found", third session, (2)). Below, "Not-found arm: the update
  and `Pre` back" is superseded by this.
- **txn's `Txn.specSole`'s write wand takes `⌜txn.PathsIgnOk …⌝`** (txn's decision, `clients-txn.md`
  §8): the server's end builder needs the witness of an applied log, which `certPre` gives only once
  the paths find their previous key-values.

## Superseded (2026-11-05, decided by the coordinator)

Found unprovable over the frozen API during the M1 proofs (`notes/mvcc-migration/server.md`,
"Found"), both minor, every caller meeting them:
- `lessor.Revoke.specA` takes `⌜MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63⌝` beside its other
  pure premises: the deletes' `delKeys` need the begin state's log well formed, which the API gives
  only through `mvccState_reachable.law` (`isMvcc`, not in the precondition).
- `applierV3backend.Compaction.specA` takes `⌜1 ≤ sint.Z rev⌝`, matching `KV.Compact.contract`
  (added 2026-11-04) and `EtcdServer.Compact.spec`: `crevOk γr (-1)` admitted `rev = -1`.
- The "by reference" parts: the auth, alarm, cluster and lessor contracts take the current backend
  `B`'s `backend.wbTok`/`rdTok` in place of mvcc's `storeWT`/`storeRT`; `txnPre` and `cmpTriple`
  follow txn's restated specs (`Spec/.../etcdserver/txn/`, else `TxnSpecs.lean`).

## What changed since round 14

These follow the cross-review (`xreview-clients.md`) and API rounds 15-16.

- **The receipts.**
  - `auEnd`'s notify step and `auRestore`'s step carry the API's `⧖ (logCh …)`.
  - `kvStoreInv` keeps `⧖ (logCh σ.notifiedLog)`.
  - `histLb`, `kvReadAt`, `rangeReadOkA`, `newHeaderPostA` and the writer's facts carry the receipt
    of their log (§1, §5).
  - So `LogSmall` follows everywhere by `preceipt_lt`: the watch path's `histLb ⊢ LogSmall`,
    client/v3's `kvLogOk`, and Revoke's sort premise.
- **G3 over the API's `mvccImage_snapshot.law`** (`ac1e686407`, fixed at `6cc29c14f0` after the
  review of round 16: F1 restricts it to a store that never compacted, F2 adds `isMvcc`, F3 puts
  `mvccImage_fresh` under an update). §3b builds its update `auSnap` from `kvStoreInv`, in the
  compaction-off mode only (a new conjunct of `kvAus.law`). §3c has `senderImage.law` (the send's triple)
  and `dbImageA_of_send` (proved). The proposed `mvccPinned` and its laws are deleted.
  `reach_logWf.law` is now the API's (the draft's local copy is gone).
- **`dbImage` over `mvccImage`** (§3c), with the receiver's `dbImageA_open.law`.
- **The Restore builder with every premise of `KV.Restore.contract`** (§3d). The snapshot path is
  linked (`Link.lean:2407`).
- **`AEnvA.Pk : BkRef → IProp`** in place of the fixed `P`. `kvBk` is
  `∃ B, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B`.
  - **Deviation from the requested `∃ q B`:** the share is whole. The apply thread is its only
    holder; it lends a share to txn, `Revoke` and `Commit` only within a call. The pin of §3b and
    `Restore` need the share whole.
  - `mPreA` carries the share with `csContractA (E.Pk B) …` at the same `B`.
- **`Revoke`** takes the nested `auBegin γ σ₀ (auEnd γ σ₀ dels Y)` (xreview §3). The not-found arm
  gives it back. The separate `⌜rd ≠ nil⌝` is dropped: it is in `mvccDeleter`. The proof follows the
  revised `mvccTxn_leaseDelete.law`, which gives `End`'s triple, not `mvccTxn`.
- **`rangeReadOkA` and `newHeaderPostA`** give `⌜LogWf' log⌝` and the receipt.
  `logOk_of_receipt` (proved) restates client/v3's `idxCert_logOk` over them. `LogWf'` comes from
  `kvReadAt`'s `MvccReachable σ` via the API's `reach_logWf.law`.
- **The watch path's needs.**
  - `histLb_model.law` is stated.
  - `srvKVInvsA` takes `wsl` and ties `E.kv = wsIfaceA wsl` (`v3rpc.wsIface`, by `rfl`).
  - Timelessness is confirmed: raft's API exports `isCommittedLogLb_timeless` (`InvNode.lean:98`),
    and `srvRLogLb_timeless` (`SrvRaftLog.lean:396`) and Perennial's `preceipt_timeless` exist.
    So every conjunct of `kvStoreInv` is timeless, and raft needs no new law.
- **The writer's facts** gain `kvNx log` and `⧖ (logCh log)`. `kvAus.law` also gains the
  snapshot's update (`auSnap`). `threadTok` is out of `kvOwnA`: the
  chain specs take it beside `kvOwnA`, as the restated `Compaction.specA` does.
- **Stale references fixed:** the size facts now come from round 16's receipts, not from
  `mvccTxn_small`/`mvccState_small`. S2, S3 and S5 are closed (see Gaps).

## (a) The specs that change

### The apply chain (`apply/Chain.lean`)

- **`AEnvA`** replaces `AEnv`. It has:
  - `kv : GoInterface`, in place of `s : Loc`;
  - `γ : MvccName`;
  - `γs : KVSNames`;
  - `Nx : Log → IProp`: the raft witness (the server's `kvNx γr on`);
  - `Pk : BkRef → IProp`;
  - `Cp : Int → IProp`: the permit (the server's `crevOk γr`);
  - `BkTie : BkRef → IProp`;
  - `f : GoFunc`.

  The rest is as today. Today's other users of the fixed `E.P` (the auth, alarm and cluster stores'
  contracts) move to `E.Pk B` at the current backend, by reference.
- **`kvOwnA E log`**:
  - `(∃ c, wSt γs log c) ∗ kvBk E ∗ leasesLiveA ∗ E.RD`;
  - no `threadTok`;
  - no `storeReader`, `txn.kvWriter` or `writerOwn`.
- **`cmpOwnA E c`**: `mvccOpen γ ∗ crOwn γs c`.
- **`csContractA`**: one definition (txn's `csA` is the same). The cross-review §8 asks for it
  beside `hookRun` in the API.
- **`mPreA`**: the halves, leases and `RD`, then `chainRes`, then
  `∃ B, mvccBackend γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗ csContractA (E.Pk B) E.f Pre Q Post`.
- **`certPreA`**: `E.Nx` of each outcome's log.
  - The `pend = []` arms with no `chainStep` outcome take `E.Nx log` from the writer's facts:
    `DeleteRange`'s `ok = false` and `Put`'s `ErrKeyNotFound` (xreview §7).
  - `putPre`/`deletePre` lose `storeWT`.
- **`applierV3backend.Compaction.specA`**:
  - pre: `⌜rev < log.length⌝`, `E.Cp rev`, `threadTok`, `mPreA`, `cmpOwnA E crev`;
  - post: as today, plus `threadTok` and `compactChanOk` for `<-physc`.
- **`rqOk`**:
  - `putOk`/`delOk` relax to `+3`, from the writer's facts (`mvccState_reachable`);
  - the range sort's premise is txn's (`stateOk` at the `Range` contracts);
  - `rqSmall_of_small`'s receipt is now the writer's facts'.

### Lease

- **`lessor.Revoke.specA`**:
  - the deleter: `mvccDeleter rd γ` (its `rd ≠ nil` inside), `rdOwn`, `threadTok`;
  - the store: `mvccBackend γ q B P ∗ hookIs B f ∗ csContractA`;
  - **one update**, `auBegin γ σ₀ (auEnd γ σ₀ dels Y)`, with `dels = leaseDels (stateAfter σ₀.log) id`;
  - the lease state: `leaseOwn` at `σ₀`'s item map, `leaseRevokers`;
  - the `Lease` bucket: its `rbPart`, `leaseParams`, `lessorBeOn`;
  - a kept premise, `(stateAfter σ₀.log).length ≤ 2^62`, which the caller now derives from the
    writer's receipt (a live key-value is a change, `receiptBound ≤ 2^48`). The tester derives it
    from its keys.
  - Post: `Y ∗ Post`, `id` filtered out, the record deleted. Not-found arm: the update and `Pre`
    back.
- **`Grant.specA`**: only `csContractA` changes.

### The server (changed conjuncts; the rest by reference)

- **`srvKVInvsA on E γr wsl`**: `kvInv ∗ srvRaftLogInv ∗ kvStoreInv E.kv E.γ γr on E.γs`, with
  `E.kv = wsIfaceA wsl`, `E.Nx = kvNx γr on`, `E.Cp = crevOk γr`, and the mode and retention ties.
- **Floors and read resources:**
  - `srvAppliedBody`'s `idxCert E.γ.idx L` becomes `kvLogLb E.γs L`;
  - `srvFloorFacts` becomes `srvFloorFactsA slog`;
  - `srvRdCallA`: `threadTok` in place of `storeReader`.
- **`EtcdServer.Range`/`Txn`**: they take `kvLogLb F`. Post `rangeReadOkA`: a floor, `kvNx`, the
  receipt, `LogWf'`.
- **`EtcdServer.Compact`**: `threadTok`.
- **`newHeader`**: `threadTok`; post `newHeaderPostA`.
- **The compactor**: `srvRevLbA`, with `R := threadTok ∗ …`.
- **`NewServer.spec`**:
  - drops `idxFresh`, the `cok` authority and `ρ.rd.kv.cok = E₀.γ.cok`;
  - adds `newServerStoreFreshA γs`;
  - indexes the claims at `γs.slog`;
  - `envAgree` compares every field but `kv`, `γ`, `Nx`, `Pk`, `Cp`, `BkTie`;
  - drops the reader-slot grants;
  - builds the stand-in `E₀` from `names_nonempty.law` (S3 closed).
- **Examples**:
  - allocate `γs` instead of `idxFresh`/`cok`;
  - the initial client floor is `kvLogLb γs [[],[]]`;
  - `compactkv`'s `watchNoDup` becomes the watch path's `srvOnce`.

## (b) The server's invariant, the builders, G3 and Restore

**`kvStoreInv kv γ γr on γs`** (§2, at `kvsN`, outside `↑mvccN` and `wsN`) holds:
- `isMvcc kv γ ∗ inv kvsN (∃σ, …)`, with inside the invariant:
  - `mvccState γ σ`;
  - the halves of `st` (`(σ.log, σ.pending)`) and `cr` (`σ.crev`);
  - the `slog` and `nlog` authorities;
  - `kvNx σ.log` and `kvNx σ.notifiedLog`;
  - **`⧖ (logCh σ.notifiedLog)`**;
  - `crevOk σ.crev`.
- Every conjunct is timeless.
- The receipt is maintained:
  - notify: the API's step gives `⧖ (logCh (σ.log ++ [pend]))`, and `logCh (log ++ [[]]) = logCh log`;
  - commit and compaction leave the notified log unchanged;
  - `Restore`'s step gives `⧖ (logCh σ'.log)`;
  - boot uses `preceipt_zero`.

**Builders (`kvAus.law`, §3):**
- begin and the writer's read, in continuation form;
- end: needs `kvNx (commitLog log pend)`, the receipt being mvcc's;
- compact: needs `crevOk rev`;
- restore;
- anyone's read: `kvReadAt` gives the floor, `kvNx`, the receipt and reachability;
- **the writer's facts**: a floor, `kvNx log`, `⧖ (logCh log)`, reachability, `+3`.

The peek, `crevOk_off`, `histLb_boot` and **`histLb_model.law`** are as the watch path asks (§6).
`histLb_model.law` gives, under `receiptBound ≤ 2^62`:
- `LogWf' L`;
- `L.length < 2^63`;
- `LogSmall L`;
- `LogPutsLe etcdKeyMax L`;
- the reached revisions (the restated `srvReachedAt`).

`srvLogA` restates v3rpc's `srvLog` over `histLb`, for `srvEtcdState`/`srvStep`.

**G3, the sender's image (§3b, §3c), over the API's `mvccImage_snapshot.law`.**

(**2026-11-04: superseded.** The user strengthened `backend.Snapshot`'s axiom, so
`mvccImage_snapshot.law` no longer takes `σ.crev = -1`; `auSnap` and `senderImage.law` no longer
need `γr.kv.cmp = false`, which the M1 proofs drop. The paragraph below records the earlier scope.)
**Scope: a cluster that never compacts.** That is `γr.kv.cmp = false`, the server's
`E.cmp = false`. It is not this draft's `on`, which is the auth mode, also `false` here, with #7-on
deferred.

The law (`6cc29c14f0`) takes:
- `isMvcc kv γ` (F2), which `kvStoreInv` holds;
- the whole share `mvccBackend γ 1 B Pk`, held through `backend.Snapshot`;
- the update `auSnap γ Φ`:
  `AU <{∃∃ σ, mvccState γ σ ∗ ⌜σ.pending = none ∧ σ.crev = -1⌝}> <{mvccState γ σ, COMM Φ σ}>`;
- the client's observation `Q` of the meta keys and tracked buckets.

It gives back the share, and `∃ σ u, Φ σ ∗ mvccImage D σ.log σ.crev u`.

*The update, from `kvStoreInv`.* `kvAus.law`'s new conjunct is
`⌜γr.kv.cmp = false⌝ → wSt log c ∗ (wSt log c -∗ X) -∗ auSnap γ (σ = stAt log c ∗ X)`.
- At each access it opens the invariant and gives `mvccState γ σ`.
- `⌜σ.pending = none⌝` holds there, because the invariant's half of `st` agrees with the writer's
  `(log, none)`.
- `⌜σ.crev = -1⌝` holds because the invariant's `crevOk γr σ.crev`, with `cmp = false`, gives it
  (`crevOk_off`). The model gives the same (`crevOf_plain`).
- It takes `mvccState` back unchanged and commits `⌜σ = stAt log c⌝ ∗ X`.
- A reader's `auRead` does not give `auSnap` by monotonicity: `auSnap`'s atomic precondition says
  `pending = none` at every access, which only the writer's half shows.
- The model tie is outside the update: the apply thread's `kvApplied` at `A` gives
  `log = kvModel A` and `c = crevOf A` (pure). So `Φ` needs only the halves.

*The send* (`senderImage.law`, derived from the API's law, the Snapshot spec and `kvAus.law`, under
`γr.kv.cmp = false`):
- pre: the store invariant (its `isMvcc` the law's), `wSt` at `(kvModel A, crevOf A)`,
  `srvRLogLb A`, the whole share, the
  snapshot's open share, a write-back, and the client's `R`/`Q`, with the server's bridge
  `Q (hkData D) (rbData D) → imageRestAt … D` (today's `srvBeSnapOk_window`, `ciKeys_hk`,
  `bkRestAt_of_rb`);
- post: `snapOpen sp D`, the shares, `wSt` back, and `dbImageA` at the snapshot's index (by
  `dbImageA_of_send`, proved).

*The interleaving checked* (`s.KV().Commit()` then `s.be.Snapshot()`, readers and the compaction
job concurrent).

**Correction: my earlier "no obstacle found" was wrong for a cluster that compacts** (the review of
round 16, F1).
- `mvccImage`'s obligations concern `D`'s compaction keys (`scheduledCompactRev`,
  `finishedCompactRev`).
- `backend.Snapshot.spec` says nothing of their committed values once they have been written: the
  observation `Q` is over the Key bucket, the hook's keys and the tracked buckets, none of which
  holds them, and `fkRd` gives them only before any write.
- So for a store that has compacted, the law was unprovable. My check covered the mvcc state, not
  what the backend's axiom lets the law learn of `D`.

The API now restricts the law to `σ.crev = -1`. The compacting sender stays deferred. The review's
minimal fix is `fkdAt` in `backend.Snapshot.spec`'s observation, a trust-boundary strengthening and
the user's decision.

In the compaction-off mode, the interleaving has no obstacle:
- **`KV.Commit`** takes and returns a share. The apply thread then holds the whole share (`kvBk`'s
  `1`) for the snapshot, and nothing it lent is outstanding: no txn, `Revoke` or `Commit` is
  mid-call.
- **`pending = none`** at every access of the update. Only the apply thread calls `End`, and it is
  not inside one. The invariant's `st` half is at `(log, none)` by agreement with `wSt`, so a
  pending revision is impossible there.
- **Concurrent readers' updates** (`auRead`, the watch path's peek, `Watch`/`Rev`) open the same
  invariant and leave `σ` unchanged. The snapshot update may be accessed and aborted repeatedly;
  each access reopens the invariant. No conflict: the masks are `⊤ \ ↑mvccN` and `kvsN` is outside
  it.
- **No compaction job runs** in the compaction-off mode: no compaction entry is ever committed
  (the KV invariant admits them only when `cmp`), so `Compact` is never called. The backend's
  periodic commits commit nothing of the store's: no transaction is open.
- **A write transaction left open** (not the server's case) would hold the batch lock. `End` needs
  a share, so it could not end during the call, and `Snapshot`'s commit would block: partial
  correctness, vacuous. The server never does this.
- **The model tie** cannot be read inside the update, but is not needed there: the pure facts
  `log = kvModel A`, `c = crevOf A` come from the apply thread's `kvApplied`, outside the update.

(Superseded 2026-11-06, the server track's ninth session: `dbImageA` landed in place as
`InvImage.lean`'s `dbImage`, with one more pure conjunct, `imageStOk (kvModel γk A) (crevOf γk A)`:
the image's state reachable and its history `+ 3 ≤ 2 ^ 63`, the sender's writer's facts
(`writer_facts`), carried to the receiver; so `kvModel_reachable.law` below is not needed, and the
receiver's KV ghost-state jump has its length bound. The send is `KVStoreLaws.snapImageG` (the
API's `mvccImage_snapshot.law` at `au_snap`, either compaction mode), `senderImage.law` proved over
it (`senderImage_holds`); `srvBeSnapOk`'s observation is a resource, `Qd : Data → IProp`.)

**`dbImageA γ γk i D`** (§3c, restating `InvImage.lean:148`) is
`∃ A u, srvRLogLb γ A ∗ ⌜i = ai0 + |A| ∧ imageRestAt …⌝ ∗ mvccImage D (kvModel γk A) (crevOf γk A) u`.
- `imageRestAt` is `imageAt` without its store part: the stored index, a term, `bkRestAt`.
- The store part (`keyImageM`, records, `IdxWf`, the separate receipt) is inside `mvccImage`.
- Restore's reachability comes from the model (`kvModel_reachable.law`).
- **`dbImageA_open.law`**: the receiver's `mvccBackendFor` at the image's history, from
  `mvccBackendFor_open.law` at the snapshot opener's post (`K := snapOpenK`) and the store's part of
  the payment rights.

**Restore (§3d).** `restorePreA` is `KV.Restore.contract`'s precondition, written out. **
`restoreArgs.law`** derives all of it from:
- the store invariant;
- `wSt log c ∗ crOwn c`, with `log`/`c` the model's at the applied prefix `A`;
- the snapshot's prefix `A'` (`A <+: A'`), its raft witness, and its permit `crevOk σ'.crev`;
- the thread token, the open token and the old backend's whole share;
- `mvccBackendFor B' (Pk B') σ'.log σ'.crev u`, from `dbImageA_open.law`;
- the new backend's unset hook (`plHookAt … dq f`; `f = nil`, `hookRun`'s view-shift row, the hook
  set after `Restore`);
- the apply protocol's `Pre`/`Q'`/`Post`;
- the commit request `True ⇒ True`;
- `leaseOwn (mvccLeases γ) Ls ∅` after `lessor.Recover`;
- the model's facts: reachability, and the leased items' leases live (no lease workload: `Ls = []`,
  no item).

`σ' := stAt (kvModelM on A') (crevOf A')`. The update commits the apply thread to `σ'`: its halves
move, and the invariant takes the receipt from `Restore`'s step.

**The consistent index.**
- The hook is frozen non-nil (`hookIs = plHookRO`) and runs at `Write`/`Compact`, and at
  `Restore` when the image's compaction is unfinished.
- The stored-index window's `commit_freeze_au` goes through `KV.Commit`'s `commitReq`, unchanged.
- `Compact`'s `ForceCommit` requests `True ⇒ True`.

**The boot sequence:**
1. `mvccW_alloc`.
2. `backend.New` at `mvccW gx`, at `K := bFresh`.
3. The write-back stock invariant, before `mvcc.New` (S6).
4-5. **`bootBackend.law`** (§3c, derived): `mvccImage_fresh.law` on the fresh data (Key bucket
   empty, no compaction keys), now under an update (F3), which the boot's fupd absorbs; then
   `mvccBackendFor_open`.
6. The lessor.
7. `mvcc.New`.
8. `bootStore.law`, which takes `⧖ 0` from `preceipt_zero`.
9. The frozen hook.
10. `E`.

## (c) What txn's restated specs must give

Unchanged from round 14, with the round-16 receipts:
1. **The API's update shapes, with an arbitrary payload, given back.** The nested begin/end shape
   for `putAU`/`delAU`/`txnBeginAU`.
2. **The committed changes as named functions** (`putPend o σ₀`, `delPend o σ₀ ok`,
   `txnChs log t`), equal to `backendStep`'s logs.
3. **No floor or certificate premise.**
4. **The hook and backend:** `mvccBackend ∗ hookIs B f ∗ csContractA` (one shared definition), and
   `threadTok` in and back.
5. **The lessor:** `lessorUser (mvccLeases γ) …`, plus the shared lemma relating
   `pendItems log []` and `leaseItemsOf (stateAfter log)` (xreview §11).
6. **Pure premises on `log` only**, needing at most `+3` of room.
7. **The receipt.** txn's commit updates must pass the notify step's
   `⧖ (logCh (σ.log ++ [pend]))` through to the server's payload unchanged; the server's end builder
   consumes it. txn must not need it itself.

## Gaps

- **G3: closed for a cluster that never compacts** by the API's `mvccImage_snapshot.law`
  (`6cc29c14f0`). The server's update comes from `kvStoreInv` (§3b), and the interleaving has no
  obstacle in that mode.
- **G3 for a compacting cluster: deferred** (F1). `backend.Snapshot.spec` gives no fact of the
  compaction keys' committed values once written. The review's minimal fix is `fkdAt` in the
  snapshot's observation, or a separate `SnapshotFk` spec: a trust-boundary strengthening, the
  user's decision. Until then, the compacting examples' adequacy through the snapshot path, and
  `dbImageA_open.law`/`restoreArgs.law` on a receiver of a compacting sender, rest on it.
- **S1 (Revoke's sort).** Kept as a premise, now derivable by the caller from the writer's receipt
  (round 16). Not an API gap.
- **S2: closed.** `mvccDeleter` has `rd ≠ nil` (round 15).
- **S3: closed.** `names_nonempty.law`.
- **S4: closed.** `histLb`'s receipt gives `LogSmall` (round 16).
- **S5: closed.** Positivity is the API's at the results (`kvSortOk`, `wsRecvOk`, round 16).
- **S6.** The write-back supply must exist before `mvcc.New` (server-side reorder).
- **S7.** Thread tokens for the apply job, the compactor and the handlers. The gRPC handler's
  per-run `S` lends its token (xreview §8).
- **S8: closed** by `AEnvA.Pk`.
- **Deferred: #7-on** (the auth-on model's image).
- **Not drafted, by reference:**
  - the chain specs' mechanical edits;
  - `isServer`/`isServerReadM`'s fields;
  - the full `NewServer` post;
  - `SnapSendBranch`'s window lemmas over `senderImage.law`;
  - the examples' `Served` lemmas;
  - `EtcdServer.snapshot`'s `KV().Commit()` (apply thread, over `kvBk`).
