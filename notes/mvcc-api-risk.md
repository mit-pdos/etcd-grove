# The mvcc API migration: its proof obligations ranked by risk (2026-11-04, branch `mvcc-api`)

The user (2026-11-04): strict M1, "do the highest risk stuff first" (`notes/decisions.md`, "strict
M1, no scaffold"). Risk: the probability that the work finds a frozen statement of the API
(`Spec/.../mvcc/Api.lean`, `ApiState.lean`) wrong, weighted by the proof a change would redo. An
independent ranking (a planning agent, read-only), the probabilities its estimates.

**Start with mvcc's side (M):** its devices are new and unproved, over invariants frozen in prose
and superseded four times (`notes/mvcc-api-backtracking.md` §3); the client drafts typecheck over
the API and mostly re-route existing arguments, and two client results (C1, C3) consume exactly
M1's and M2's statements.

## (M) mvcc's proofs of the API

1. **The watch guarantee** (`wsRecv_ok.law`, `wsChan_recv.law`, per-watcher delivery under
   compaction, invariants §4.4-§4.5): today's receive facts are not pure (`WatchRecv.lean:86-94`,
   `regsAt` needs `£ 1 ={⊤}=∗`, `evLog` carries the client's `certOk`), so the plain `⊢ ⌜wsRecvOk⌝`
   needs a channel invariant rebuilt; `rangeEvents.spec:52` requires `c = -1 ∨ oneChangePerKeyAt
   log c`, while `wsRecvOk`'s positivity and `modRev ≤ rev` hold unconditionally (a new scan spec
   for a lossy compaction). Could force: `wsRecvOk`'s conjuncts 1-3, `wsRecv_ok`'s `⊢` (a fancy
   update with credits), `wsChan_recv`'s empty case, `Watch`'s stamp. 4-6k lines; ~21k lines
   outside mvcc consume today's watch internals.
2. **`mvccImage_snapshot.law` for a compacting store**: the image needs `entsCutAt`'s per-key
   prefix of deleted entries (`InvIndexRestore.lean:714-718`); no store-side proof tracks the
   compaction job's cut (`SnapSendBranch.lean:530`, `SNAPSHOT-SORRY #7-cmp`); the strengthened
   axiom gives the values only. Could force: `mvccImage`'s meaning, or the axiom again. 1-1.5k lines.
3. **`Restore`, `mvccBackendFor`, `mvccBackendFor_open`**: the receipt into `idxCert`, the slot
   switch, each watcher's delivery invariant across the restore; resuming an unfinished compaction
   with a nil hook is on the linked server path (`clients-server.md:271`). 2-3k lines.
4. **The two-step commit** with the receipts and the writer's view carried from `Write` to `End`
   (`store.Write` drops it today): low probability, the largest weight (every writer). ~1k lines.
5. Low: `mvccTxn_leaseDelete`, `Range`'s `stateOk`, the notify step's receipts.

## (C) the clients' proofs over the API

1. **v3rpc's watch** over `wsState`/`wsRecv`/`wsRecvOk`: `progressCov`, `drain_empty`,
   `snap_after_recv` (`notes/mvcc-api-clients/WatchSpecs.lean:492-571`) statements and a sketch
   only. ~6k lines.
2. **`examples/mvccrand`'s adequacy**: no proof or draft over the API; it holds `mvccState` and
   `wsState` itself and checks every event's fields. ~3k lines.
3. **The snapshot send and receive** (`senderImage.law`, `dbImageA`, `restoreArgs.law`): downstream
   of M2/M3.
4. **`kvStoreInv`, the builders, the apply chain, Revoke**: typechecked, not proved; re-plumbing.
   Low probability, 5-8k lines.
5. Low: client/v3's `kvLogOk` (`logOk_of_receipt` proved in the draft), txn's range and sort.

## The probes (pure cores first, `notes/mvcc-api-probes/`, checked with `lake env lean`)

1. **M1**: `wsRecvOk_of_sent`: what each response records at its send (a pure `SentFact`), under
   monotone agreement, gives `wsRecvOk`; the snoc step keeps it.
2. **M2**: the compaction job's step keeps the cut; the `Snapshot` axiom's observation and the
   cut give the image's obligations.
3. **C1**: v3rpc's `drain_empty`, `snap_after_recv`, `progressCov`'s core over the API's laws as
   hypotheses.

Then, if they pass: stage 2 with M1 and M2 first (not the 13 store contracts), then C1, then the
tester.
