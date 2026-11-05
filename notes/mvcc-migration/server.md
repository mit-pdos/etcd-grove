# The server's migration onto mvcc's API (strict M1): hand-off

Scope: `server/v3/etcdserver` outside `txn/` and `api/`, and `server/v3/lease`. The frozen draft is
`notes/mvcc-api-clients/ServerSpecs.lean` (with `clients-server.md`); its names are kept, namespace
`srvApi`, a restated definition with the suffix `A`.

## Done

- **The lessor's specs restated** (`Spec/go_etcd_io/etcd/server/v3/lease/lessor__Revoke.lean`,
  `lessor__Grant.lean`): `lease.lessor.Revoke.spec` and `lease.lessor.Grant.spec` are the draft's
  `lessor.Revoke.specA`/`lessor.Grant.specA` word for word (Revoke: `mvccDeleter`, the backend share
  and frozen hook, `csContractA`, one nested update `auBegin γ σ₀ (auEnd γ σ₀ dels Y)`, the sort
  premise kept; Grant: only the contract). Both build.
- **The update shapes** (`Proof/go_etcd_io/etcd/server/v3/lease/MvccShapes.lean`): `stAt`,
  `auBegin`, `auRead`, `auEnd`, `auSnap`, `auCompact`, `auRestore`, `csContractA` (below the lessor,
  whose `Revoke` takes them). `auSnap` without the draft's `σ.crev = -1` (the API's
  `mvccImage_snapshot.law` dropped it; the draft's own header says the M1 proofs drop it). Builds.
- **The store invariant and its builders, proved** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/
  KVStoreCore.lean`, builds, no `sorry`): the invariant generic in the raft witness `Nx` and the
  permit `Cp` (`kvStoreInvG`; the draft's `kvStoreInv` is it at `kvNx γr on`, `crevOk γr`, by
  `rfl`), `KVSNames`, `kvsN`, `kvLogLb`, `wSt`, `crOwn`, and every builder over mvcc's
  `persistent.law` and `mvccState_reachable.law` as hypotheses: `au_begin`, `au_wread`, `au_snap`,
  `au_end` (the two nested updates: the notify step moves the pending halves and the notified log,
  its receipt mvcc's; the commit step the committed log), `au_compact` (the compaction revision's
  three parts), `au_restore`, `au_read` (`kvReadAt`: floor, witness, receipt by `preceipt_mono`,
  reachability), `writer_facts`, `kvAusG` (all together, `kvAus.law`'s shape), `kvPeekG`,
  `histLb_bootG` (a reachable state's logs begin with `[[], []]`, `reach_prefix`), `bootStoreG`
  (`⧖ 0` by `preceipt_zero`). The riskiest part of the server's side: no frozen statement found
  false.
- **The draft's statements** (`KVStoreApi.lean`: §2-§3d, §4 as `AEnvA` etc., §6) and their laws by
  instantiation (`KVStoreLaws.lean`: `kvAus_holds`, `kvPeek_holds`, `crevOk_off_holds`,
  `histLb_boot_holds`, `bootStore_holds`). **Not built yet**: their imports (`ServerOn`,
  `InvImage`, `apply.Chain`) are red under strict M1 (`apply.Chain` and `apply.Contracts` use txn's
  deleted sole-writer API: `txn.kvWriter`, `txn.Writer`), so the statements are the draft's text,
  typechecked at `6cc29c14f0` by the draft's author, and the laws' proofs are one-line
  instantiations of the core's, which builds.

- **The lessor's writes over the API's `hookRun`** (by reference, builds): `leaseBatchTx`'s
  `LockInsideApply` takes `csContractA P g …` at the hook `g` whose value its `f` is
  (`⌜f = #g⌝ →`), so that a `nil` hook is the caller's view shift; `Lease.persistTo.spec` and
  `lessor.Checkpoint.spec` restated like `Grant` (`f : GoFunc`, `lessorBackend … #f`,
  `csContractA`); `lessor.Grant.wp_proof`, `lessor.Checkpoint.wp_proof`, `Lease.persistTo.wp_proof`
  proved over them (no `sorry`).

## For the parallel tracks

- v3rpc: `srvApi.histLb` (= `histLbG (kvNx γr on)`), `srvApi.kvPeek.law` (proved: `kvPeek_holds`),
  `srvApi.histLb_model.law` (stated, not proved: it needs the KV invariant's claims),
  `srvApi.srvKVInvsA` with the tie `E.kv = wsIfaceA wsl`; all in `KVStoreApi.lean`. Until the
  server's foundations build, the generic forms in `KVStoreCore.lean` (which builds) are the ones a
  proof can import: `kvPeekG`, `histLbG`, `histLb_bootG`.
- `AEnvA` (§4) is the draft's separate structure for now; the plan is to restate `apply.AEnv` in
  place with its fields (next step) and make `AEnvA` an alias.

## Left (in order)

1. **The apply chain's foundations** (`apply/Chain.lean`, `apply/Contracts.lean`): `apply.AEnv`,
   `kvOwn`, `cmpOwn`, `mPre`, `certPre`, `leasesLive` restated in place as the draft's `AEnvA`,
   `kvOwnA`, ... (`threadTok` beside `kvOwn` in the chain's triples; `putPre`/`deletePre` without
   `storeWT`; the floors `kvLogLb`; `revokeRes` over `rdOwn`/`mvccDeleter`); the components'
   contracts (`isApplyKV` → `isMvcc ∗ ⌜kv = E.kv⌝ ∗ envAus E`; `isAuthStore`, `isAlarmStore`,
   `isCluster`, `isApplyLessor` at `E.Pk B` of the current backend, without mvcc's `storeWT`/
   `storeRT`: not drafted, "by reference"). This unblocks `InvRequest`, `InvImage`, `ServerOn`
   and so `KVStoreApi`.
2. The apply chain's proofs, `applyAll`; `lease.Revoke`'s proof over `mvccDeleter`,
   `Txn.DeleteRange`, `mvccTxn_leaseDelete.law` and `Txn.End` (blocked: see "Found").
3. The boot (`mvccW_alloc.law` now gives `mvccWReg gx ∗ mvccW gx`), the receipts for client/v3's
   `kvLogOk` (`logOk_of_receipt`, proved in `KVStoreApi.lean`).
4. The snapshot send and receive (`senderImage.law`, `dbImageA_open.law`, `restoreArgs.law`, stated).

## Placeholders

None (no `sorry`, no axiom).

## Found

- **`lessor.Revoke.specA` (landed as drafted) is unprovable over the frozen API: it lacks the
  begin state's reachability.** The proof must show that the loop's `Txn.DeleteRange(key, nil)`
  calls, one per key of the lease's item set (`l.Keys()`, sorted), leave exactly `dels =
  leaseDels (stateAfter σ₀.log) id` pending, since `End`'s update (`mvccTxn_leaseDelete.law`'s
  triple, `Txn.End.contract`) commits `σ.notify pend` for the transaction's actual `pend` and the
  caller's `auEnd γ σ₀ dels Y` takes `σ.notify dels`. Each call deletes
  `delKeys σ₀.log pend true k []` (mvcc's index answer), which is `[k]` for a key of the state
  only under `LogOk (σ₀.log ++ [pend])` and `σ₀.log ≠ []` (`txn.delKeys_eq`), i.e. `σ₀`'s log well
  formed (`LogWf`, from `MvccReachable σ₀` by `reach_logWf`). The precondition gives only
  `σ₀.pending = none ∧ (stateAfter σ₀.log).length ≤ 2 ^ 62`; the only API fact of reachability is
  `mvccState_reachable.law`, which needs `isMvcc kv γ`, not in the precondition (`mvccDeleter rd γ`
  has none), and the deleter's begin update gives the proof no access to the state. (True of every
  run, since the begin update commits only at mvcc's real, reachable state; not provable from what
  the API exports.) **Minimal fix**: add `MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63` (txn's
  `Reach σ₀`) to the pure premise. Both callers have it: the server's apply thread from the
  writer's facts (`kvAus.law`'s last conjunct gives exactly `MvccReachable (stAt log c) ∧ log.length
  + 3 ≤ 2 ^ 63`), the tester from `mvccState_reachable.law` on the state it holds. (Alternatively
  `mvccDeleter`'s triple could return the begin state's reachability with `R σ`.) The Revoke proof
  is stopped until the user decides.

- **`applierV3backend.Compaction.specA` is unprovable over the frozen `KV.Compact.contract`**
  (not landed). The draft's precondition is `⌜sint.Z rev < log.length⌝ ∗ E.Cp (sint.Z rev)` with
  `E.Cp = crevOk γr`, and `crevOk γr (-1)` holds (`⌜c = -1⌝` is its first disjunct), so the spec
  admits `rev = -1`; but `KV.Compact.contract` takes `⌜1 ≤ sint.Z rev⌝` (added 2026-11-04,
  `04dd363d79`, after the draft froze), so `Compaction`'s call of `KV.Compact` cannot be proved at
  `rev = -1` (nor at `0`, which `crevOk` excludes). Minimal fix: the premise
  `⌜1 ≤ sint.Z rev ∧ sint.Z rev < log.length⌝` (its caller has it: a compaction request's revision
  is positive, `EtcdServer.Compact.spec` requires it); alternatively `E.Cp` the cluster permit
  `kvCmpPermit γr.kv` (positive) rather than `crevOk`.
