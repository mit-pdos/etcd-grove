# Cross-review of the three client drafts (txn, server, watch) against mvcc's API at round 15

2026-11-03. Read-only. All three scratch files (copies in `~/.claude-D/jobs/e4ba2bf8/tmp/xreview/`) still
**typecheck** against round 15's `Api.lean` (`lake env lean`, exit 0, only the "manifest out of date"
warning). They compile only because every removed law (`mvccTxn_small`, `mvccState_small`) is named
in docstrings, never in terms. Ranked by severity.

## 1. High: no client can produce the receipt `⧖ (logCh L)`, and three linked consumers need it (API gap)

- **Round 15's `Restore` takes `⧖ (logCh σ'.log)`.** Its docstring says the snapshot image
  certificate carries it (`InvImage.lean:148`, `dbImage`). That certificate's receipt comes from the
  sender's mvcc internals (`merged_image`, `SnapSendBranch.lean:784`: "`txn.soleWriter`'s `idxCert`
  ... `idxCertR`"). The API removes those internals and exports no receipt, because the user rejected
  (C). So after the migration the claim is circular.
- **`LogSmall` is not only a watch need (S4).** It is also:
  - client/v3's KV path: `idxCert_logOk` (`KVService.lean:1515`, D48 `kvLogOk`, which the exported
    client results state) and `kmLog` (`EtcdModelKV.lean:148`);
  - v3rpc's `HistoryModel`/`ClientModel`.

  It is used for the client model's "0 < version" (`stateAt_client_revs`). It is not a sort premise,
  so `stateOk` does not replace it.
- **txn cannot mint the receipts itself.** A single `Txn.DeleteRange` call commits many changes in
  O(1) txn steps.
- **Resolution (needs the user):** give the receipt at the call that produces it (the principle of
  `dbc5f67e02`), not as (C)'s state law:
  - `Txn.End`'s notify step gives `⧖ (logCh (σ₀.log ++ [pend]))`, and its commit gives
    `⧖ (logCh (commitLog σ₀.log pend))`;
  - `KV.Put`/`KV.DeleteRange` do the same;
  - `New` gives `⧖ 0`.

  The server then keeps `⧖ (logCh σ.notifiedLog)` in `kvStoreInv`, and `kvNx`/`histLb` carry it.
  `LogSmall` follows by `preceipt_lt` with `receiptBound ≤ 2^62`. `Restore`'s premise and `dbImage`
  get their source. Revoke's premise (§7) becomes derivable too.
- **Alternative:** drop `LogSmall` from the client model, replacing it with once-per-revision
  (S5/`srvNoDupKeys` through raft) and changing exported results. Even then, `Restore`'s receipt
  stays unsatisfiable.

## 2. High: the server draft calls the snapshot path "unlinked", but it is linked (client design to finish now)

`Link.lean:2407` `EtcdServer.wp_applySnapshot` takes `watchableStore.Restore.spec`. So the following
are on a linked path:
- the Restore builder;
- S8: `AEnvA.P` is fixed, while `Restore` returns `mvccBackend γ 1 B' Pk'` with `Pk'` depending on
  `B'`;
- Restore's receipt (§1), its length premise and its lessor premise;
- lending the new backend's unset hook (`plHookAt B'.γB dq f`).

Left as they are, `AEnvA`/`kvBk` would have to change during the applySnapshot proof.

**Resolution:**
- `AEnvA.Pk : BkRef → IProp`, and `kvBk := ∃ q B, mvccBackend E.γ q B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B`.
- State the Restore builder with every premise of round 15's contract.
- Only G3 (`kvWriter_keyObs`, already `sorry` at `SnapSendBranch.lean:526`) and #7-on stay deferred.

## 3. High: `lessor.Revoke.specA` takes two separate updates, which no builder can make (seam; the tester reaches it)

The pre has `auBegin γ σ₀ X ∗ auEnd γ σ₀ dels Y`. But both the server's begin builder and its end
builder (`kvAus.law`) consume the writer's exclusive `wSt`, so the two cannot be built up front. The
tester has the same exclusivity: `examples/mvccrand`'s writer calls `le.Revoke`
(`mvccrand.go:527`), and the tester is the linked adequacy target. txn already uses the right shape.

**Resolution:**
- Pre: `auBegin γ σ₀ (auEnd γ σ₀ dels Y)`, i.e. `beginAU γ (fun σ => ⌜σ = σ₀⌝ ∗ commitAU γ σ₀ dels Y)`.
- Post: `Y`. The not-found arm gives the begin update back.
- Drop the separate `⌜rd ≠ func.nil⌝`: round 15 put it in `mvccDeleter`.

## 4. Medium-high: txn's size premises are obsolete at round 15, and the server cannot supply them anyway (fix before freezing)

`Txn.Range`'s post gives `stateOk (stateAt k.readLog r')` for every `r' ∈ [crev, readLog.length-1]`.
That range covers a write transaction's pending state (`readLog = σ.log ++ [pend]`, `writeRev ≤
σ.log.length`), and `stateOk` gives `sortSmall` through `srvPre_small` (`stateOk`'s `≤ 2^62` is
exactly its premise; `kvSortOk ↔ txn.kvOk` is a reordering).

**Delete:**
- `VersOk` from the read updates' `COMM` (`Range`, `Txn.specSole`, `Txn.specRead`) and from
  `executeTxn`/`txn`;
- `RunSmall`, `WriteSmall`, `StateSmall`;
- `TxnPreA`'s write conjunct;
- `executeRange`'s `sortSmall` premise (derive it from the `Txn.Range` call's post instead).

As drafted these specs are unsatisfiable by the server's builders:
- `auRead`'s `COMM` gives `⌜σ = stAt log c⌝ ∗ X` and `kvReadAt`, with no `VersOk`;
- the server lists versions as open (S5).

Dropping the premises strengthens txn's specs, so do it now, not during the proof. This closes txn
1a and server S5.

**Housekeeping:**
- Unify `txn.kvOk` with `api.kvSortOk`.
- Fix the stale references:
  - the server's `rqOk` note ("`mvccTxn_small` on read transactions");
  - `kvReadAt`'s docstring (`mvccState_small`);
  - txn's header and §2a.

## 5. Medium: client/v3's KV path is covered by no draft (seam)

Today `EtcdServer.Range`'s outcome carries `idxCert ∗ certOk`, and client/v3 extracts
`LogWf' ∧ length < 2^63 ∧ LogSmall` from it (`idxCert_logOk`). The server's `rangeReadOkA` and
`newHeaderPostA` give `kvLogLb ∗ kvNx ∗ ⌜2 ≤ len ∧ len+3 ≤ 2^63⌝`, with neither `LogWf'` nor
`LogSmall`. That would force those posts to be strengthened during the client proof.

**Resolution:**
- Add to both posts `⌜LogWf' log⌝`, from `MvccReachable`'s `LogWf` or the KV model (whichever matches
  `LogWf'`), and the receipt of §1.
- Restate `idxCert_logOk` over them, and list the obligation in the server draft.

## 6. Medium: what the watch path needs that the server does not state

Agreed and provided:
- `kvPeek.law` matches `srvPeek`: same state back, `histLb σ.notifiedLog`, `crevOk σ.crev`;
- `histLb` is persistent, prefix-closed and agrees (`nlog` lower bounds);
- `crevOk_off`, `histLb_boot`;
- the namespaces are disjoint: `kvsN = nroot.@"server_kv_store"`, `wsN = nroot.@"v3rpc".@"ws"`,
  `mvccN = nroot.@"mvcc"`.

Missing:
- **(a) `histLb L ⊢ ⌜LogSmall L⌝`:** see §1.
- **(b) The client-model laws `watchLaws_srv` takes over `histLb`** (`etcdReached`,
  `srvEtcdState`/`srvStep`, `LogPutsLe`, watch (c)2). The server only says they follow from `kvNx`.
  State them as a `histLb_model.law` in the server draft.
- **(c) The tie `E.kv = wsIface R.wsl`.** `shapes.law`'s first conjunct gives only `isKV` from
  `isMvcc`, while `NewWatchStream` needs the concrete `*watchableStore` type (its second conjunct is
  per `PW`). Record it in `srvKVInvsA`/`watchSrvOk`.
- **(d) Timelessness.** The peek strips no later, so every conjunct of `kvStoreInv` must be timeless.
  `kvNx` contains raft's sealed `isCommittedLogLb` (`InvNode.lean:89`, `@[no_expose]`, with
  `cmtFactsS`). Confirm that raft's API exports a `Timeless` instance, or add one as a law there.

## 7. Medium: the server's builders and token placement

- **The writer's facts lack `kvNx log`.** Two arms need the end builder at `pend = []`, i.e.
  `kvNx (commitLog log []) = kvNx log`:
  - `DeleteRange`'s `∀ ok` arm `ok = false`, which has no `chainStep` outcome at `nd = true`, so
    `certPreA` cannot give it;
  - `Put`'s `ErrKeyNotFound` arm, unless `chainStep` lists that outcome.

  Add `kvNx log` to the writer's-facts builder: the invariant holds it, and it is persistent.
- **`threadTok` inside `kvOwnA`.** The apply goroutine's one token is lent separately today
  (`applyConfChange.lean:97,114`, `restoreAlarms`, `applySnapshot`). Bundling it into `kvOwnA` forces
  every such spec to unpack `kvOwnA`. Keep it a separate conjunct of the chain specs, as txn's entry
  specs do.
- **Revoke's sort** (`(stateAfter σ₀.log).length ≤ 2^62`) remains: it sorts the lease's keys, not a
  range, so `stateOk` does not apply. Status:
  - for etcd it is deferrable (`rqOk`'s `leaseRevoke` is `False`);
  - the tester discharges it from its six keys;
  - with §1 the server derives it (state length ≤ `logCh` < `receiptBound`).

## 8. Agreement on ownership (consistent; no change needed)

- **`mvccState`:** only in the server's `kvStoreInv` at `kvsN`. txn passes updates through. Watch
  peeks, and returns the state unchanged in `Watch`, `Rev` and the snapshot.
- **`mvccOpen`:**
  - the boot holds it until `cmpOwnA` (it covers `NewServer`'s `kv.Close()` error path);
  - after that, the apply thread holds it, for `Compact` and `Restore`.
- **`mvccBackend`:** the apply thread's `kvBk` holds it, and lends it to txn, `Revoke` and `Commit`.
  `EtcdServer.snapshot`'s `KV().Commit()` is on the apply thread, so it is covered (to add to the
  by-reference list).
- **The hook:** `f : GoFunc`, frozen (`hookIs`), with one `csContract` definition, written twice
  today (`txn.api.csA` = `srvApi.csContractA`). Put it beside `hookRun` in the API.
- **`threadTok`:**
  - every API caller holds one: the apply job, the request goroutines, the compactor, recvLoop and
    sendLoop (sendLoop calls `Rev()`), `close`, and the handler;
  - watch's W1 is stale: the notes (`mvcc-api-candidate.md:706`) find the gRPC handler's per-run `S`
    lends the token (`InvGrpc.lean:151`), with no change to the trust base.

## 9. Seams that match (checked)

- **Update shapes.** txn's `readAU`/`beginAU`/`putAU`/`delAU`/`txnBeginAU`/`commitAU` are instances of
  the server's `auRead`/`auBegin`/`auEnd` by AU monotonicity. The continuation form of `auBegin`
  lets the end update nest inside the begin's payload.
- **The committed changes are named functions:** `putPend o σ₀`, `delPend o σ₀ ok`, `txnChs log t`.
  They depend on `σ₀` only through `σ₀.log`, which the server pins (it pins the whole `stAt log c`,
  which is stronger than txn's `σ.log = log`).
- **The notified log.** `notifiedLog` after `notify pend` equals `commitLog log pend` (`commitLog log
  [] = log`), so `kvStoreInv`'s `kvNx σ.notifiedLog` matches the end builder.
- **`Txn.End`'s `⌜σ = σ₀⌝` is mvcc's promise.** Only the read-then-write pin is the caller's (in `Qr`,
  then in the wand).
- **No floor or certificate premise in txn.** `TxnPreA` becomes `OpsOk` alone after §4. The room
  `+3` comes from `mvccState_reachable`.
- **The revision.** `W64 σ.rev` versus `(log.length:Int) - 1` is a pure rewrite at `2 ≤ len`.
- **The tester** holds `mvccState` itself and never compacts (`crev = -1`, so `onceUpTo` is vacuous).
  It needs none of `kvNx`, `histLb`, `crevOk` or `LogSmall`. Only §3 and the Revoke premise touch
  it.

## 10. Round 15 closed these; the drafts should say so

| Gap | Closed by |
|---|---|
| txn 1 (`shapes.law`) | restored |
| server S2 | `mvccDeleter`'s `⌜rd ≠ nil⌝` |
| server S3 | `names_nonempty`: build the stand-in `E₀` from `Nonempty`; repair (a) is not needed |
| txn 1a, server S5 | `stateOk` (§4) |

## 11. API hygiene (mechanical, before `etc/api-check.py`)

- **mvcc internals that clients name.** The drafts name these, reached through `Api.lean`'s public
  imports of `Proof/...` modules (txn gap 7):
  - `txnCtx`, `rangeCtx`, `neverDone`, `errorfIs`, `isLessor`, `rangeRev`;
  - `pendItems`, `delKeys`, `writeRev`, `commitLog`, `stateAt`/`stateAfter`, `leaseItemsOf`;
  - `leaseDels`, `rbDel`, `leaseName`, `leaseParams`;
  - `watchRangeOf`, `watchEvents`;
  - the internal `WsNames` (watch W2).

  Re-export them into `ApiState`'s vocabulary.
- **A shared pure lemma.** State `pendItems log [] = leaseItemsOf (stateAfter log)` once there: both
  txn and the server need it.

## Not blocking

These need no API change:
- W3: the model type changes;
- W4: compaction responses are now live in sendLoop;
- W5;
- S6: the write-back supply before `start`;
- S7;
- the examples' `Served` lemmas.

## What would force a strengthening mid-proof if left

- §1: `Restore`, `histLb` and `kvNx` all lack the receipt.
- §2: `AEnvA.P` is fixed.
- §3: `Revoke`'s update shape.
- §4: txn's obsolete premises; dropping them later strengthens frozen specs.
- §5: `rangeReadOkA`'s missing `LogWf'`/`LogSmall`.
- §6(b): the `histLb` model laws.
- §7: `kvNx log` in the writer's facts.

Fix these before the proofs start. §1 needs the user's decision.
