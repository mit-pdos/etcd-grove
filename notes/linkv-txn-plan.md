# Plan: linkv over Delete and Txn (the robustness tester's workload)

Status: done (2026-10-20; STATUS "linkv-txn stage A", "stage B1", "stage B2, B3", "stage C", "stage D", "stage E", "stage F", "stage G"): `linkvtxn_safe`, on exactly `linkv_safe`'s axioms.

## Goal

`linkv_safe` (and `linkv3_safe`, which runs `linkv.Check`) say porcupine never answers `Illegal`
for `linkv.Model()` on histories of `Put`/`Get`, with a values-only model. Extend the workload and
the model to the KV API etcd's robustness tester exercises
(`.lake/go-src/etcd/tests/robustness/{traffic/etcd.go,model/deterministic.go}`), minus leases,
compaction, defragmentation and stale/serializable reads (below, "Out of scope"):

| robustness request | here                                                                    |
|--------------------|-------------------------------------------------------------------------|
| `Get`              | as now, plus the reply's `ModRevision`/`Version` and header revision    |
| `List`, `ListKeyOnly` | `cli.Get(prefix, WithPrefix())` (`client_range_end_to_end`)           |
| `Put`              | as now, plus the reply's header revision                                |
| `Delete`           | `cli.Delete(k)`: deleted count, header revision                         |
| `MultiOpTxn`       | `Txn().Then(ops...)`, ops Get/Put/Delete on distinct keys              |
| `CompareAndSet`    | `Txn().If(cmp).Then(Put).Else(Get)`, `cmp` on `Value`/`Version`/`ModRevision` `=` |

The closed theorem's statement keeps its shape: `Main` does not panic and returns `Ok` or
`Unknown`, on exactly `linkv_safe`'s axioms. What changes is what that means: the Go `Model()` is
part of the statement (porcupine's verdict is relative to it), so the model has to be etcd's
API semantics, recognisably. Stage D has the checks for that.

## What is already there

- **Server and client, every KV op** (unit T2): `client_{put,delete,txn,range}_end_to_end` over
  `kvOpAu`/`kvReadAu` on the whole `KVState` with `kvOpStep`; replies tied to the log the op ran
  at: `putReplied`, `deleteReplied` (`deleted`, `prevs`, header revision `writeRev`),
  `txnReplied` (`succeeded`, `opRespsRel` of `srvRunTxn`'s results, header revision), all in
  `Proof/go_etcd_io/etcd/client/v3/Results.lean`. The server's request path is generic in the op
  (`reqPropOk`'s `kvOpAu1` case, `InvRequest.lean`).
- **At-most-once firing** (D21 M6) for **Put only**: `EtcdServer.Put.spec`, `kvDepPre`'s `.put`
  case (`.op1`), `putAuOk`/`kvOnce` at the client. Delete and writing Txn still take the
  persistent `kvOpAu` (`kvDepPre`: `.op`), which a failed-then-late write cannot use: lintest's
  update must commit once.
- **lintest and porcupine** are generic (`applySpec`, `ModelSpec`, the bounded `rep`): no change.
- **linkv's proof pattern** (`linkv/Inv.lean`): prophecy of ok/err for writes, prophecy of the
  read revision for persistent read updates, pending failed puts as ghost tokens in the
  invariant, the revisions' map for reads.

## Gaps this plan closes

1. Delete and writing Txn fire at most once (D21 M6 extended).
2. A writing Txn's range results are not known to the client: `txnReplied` quantifies the apply's
   `skip` (`SkipRangeExecution`, set when `needResult` is false, i.e. no waiter registered).
   Needed: a delivered reply had `skip = false`.
3. A read-only Txn takes no read update at the client (`client_txn_end_to_end` forces
   `Q = True`; STATUS "Open work", item 3), though `txnReplied`'s read-only case and the server's
   `kvDep` already carry `□ Q`.
4. linkv's model knows values only, puts only; its abstraction (`absKV`, `ModelKV.lean`) and
   invariant (`LinkvOk`, pending *puts*, revisions' map of key-values) follow.

## Stages

A and B (server/client) are independent of C–E (model); F needs all of them; G closes.

### A. At-most-once Delete and Txn (server, gRPC layer, client)

Follow D21 M6's Put changes (STATUS "D21 M6", decisions.md "D21 M6 carried out"):

- `EtcdServer.DeleteRange.spec`, `EtcdServer.Txn.spec` (writing case): take `kvOpAu1`, success
  gives `Q` (not `□ Q`) through `kvRes`, as `EtcdServer.Put.spec`. Their proofs: the request
  path already handles `reqPropOk`'s third case.
- `kvDepPre`: `.deleteRange` and the writing `.txn` accept `.op1` (keep `.op` for the
  persistent callers or move them over with `_of_box`); `kvDeleteOk_of_server`,
  `kvTxnOk_of_server`, `deletePermit_of_dep`, `txnPermit_of_dep`.
- Client: `client_delete_end_to_end` takes `putAuOk … (.deleteRange …) Q` (not renamed);
  `client_txn_end_to_end`'s writing case `txnAuOk` (on the `*txn`). `txnObjAt` has no `kvOnce` today
  (`InvTxnBuilder.lean`): thread it from `NewKV` through `Txn()` to `Commit`.
- `deleteReplied`/`txnReplied` lose `□` on `Q`; `_mono` lemmas.
- Callers (putget, putget3, recipes, concurrency, leasing, cache, watchkv) pass `□ Q` via
  `putAuOk_of_box`. Gate: every `gen-link.py` mode unchanged, TCB unchanged.

### B. Replies the client can use

- **B1 `skip = false` on a delivered reply.** The apply thread reads `needResult :=
  s.w.IsRegistered(id)`; the proposer registered `id` before proposing and only the apply's
  `Trigger` delivers a result (a timeout's `Trigger(id, nil)` gives the client an error). With the
  wait registry's ghost state (`Proof/go_etcd_io/etcd/pkg/v3/wait/Defs.lean`): registered at
  trigger ⇒ registered at `IsRegistered` (ids are not reused) ⇒ `skip = false`. Put it in
  `txnReplied`'s writing case. **Fallback** if this turns out expensive: gens with no Get in a
  writing Txn (the CAS's `Else(Get)` then becomes `Else()`), and B1 later.
  **Done** (2026-10-20, STATUS "linkv-txn stage B1"), as the findings below proposed but for (b):
  the registration rides on a cluster-level registries' map (`IdNames.wn`, per prefix), not on
  `ρ.wait`, which raft's environment (`srvC`) fixes before `start` makes the wait.
  **Findings (2026-10-20, before any change)**: the apply thread already proves the
  dichotomy at a *known* registration (`request_delivered`, `entryDelivered`: `out.waived = false`
  or the registration with token `t` is gone), but (i) both apply loops (`EtcdServer.apply`)
  call `applyEntryNormal` at `ot = none` (`entryRegd_none`): no entry carries its id's
  registration, because the claim (`srv_claim_mint`, `entryClaim`) is minted *before*
  `Register` (whose condition `reqWaitR` needs the claim); and (ii) `Trigger(id, x)` demands
  `waitTrig` (every registered expectation's `Ψ x`) even when the registration is gone, so the
  result handed over cannot say "not waived" unless the apply thread proves it in every case.
  What B1 needs: (a) `isWait`'s `Trigger` also accepting `waitGone γw id t` (provable in
  `wait/List.lean`: a gone id is out of the live map and cannot come back, the record map
  being written once per id); (b) every own-prefix entry carrying its registration: the
  proposer, after `Register`, records `waitRegd ρ.wait id t` where `kv_prop_au` builds the
  entry's `entryClaim` (the claim is cluster-level since D21e (A): another member's entries
  need no record, `reqWaitR`'s prefix clause makes `waitTrig` vacuous for them); (c) the loops
  passing `some t` for own-prefix entries; (d) `resultΨ` (`resultIsW`) carrying
  `⌜out.waived = false⌝`, through `appliedOk` to `txnAppliedOk` and `txnReplied` (`skip =
  false`). Every other consumer of `entryClaim`/`entryWaitOk` (`BuildGap`, `InvRun`, boot logs)
  follows (b).
- **B2 read-only Txn with a read update** (item 3): the read-only case of
  `client_txn_end_to_end` takes `kvReadAu γr.kv Q` and returns `□ Q (kvStateOf log)` (already in
  `txnReplied`); for a linearizable (non-serializable) txn only.
- **B3 value lemmas** (as `client_get_value`): `client_put_value` (header revision
  `σ.rev + 1`), `client_delete_value` (deleted count = keys in range at `σ`, revision),
  `client_txn_value` (succeeded, each op's response, revision, all as functions of `σ`),
  `client_list_value` (from `rangeReply_state`). Each states the reply as a pure function of the
  `σ` that `Q` is at, which is what stage F's commit needs.

### C. The Lean model (`linkv/KVModel.lean`, `ModelKV.lean`; pure)

**Done** (2026-10-20) in new files `PendModel.lean`, `TxnModel.lean`, `TxnModelKV.lean` (STATUS
"linkv-txn stage C"), with versions and mod revisions as words and `list` over the workload's
keys; the old model stays until F.

- **State**, as robustness's `EtcdState`: `rev : Nat` and per key `ValRev := (val, modRev,
  version)` (no create revision, no lease, as robustness). Init: revision 1, empty store (what
  `kvStateOf` of the boot log gives: check against `linkvInv_alloc_boot`).
- **Ops**: `get k`, `list` (every generated key: the prefix), `put k v`, `delete k`,
  `txn cmps thenOps elseOps` (cmps: `value k = v`, `version k = n`, `modRev k = n`; ops: get, put,
  delete). One function `mStep : Op → MState → MState × Resp`, the revision bumped once per
  writing step that changed something (robustness's `increaseRevision`, `KVState.commit`'s
  `cs = []`).
- **Outputs**: `Resp` with header revision, per robustness's `EtcdResponse`: get/list kvs with
  `ModRevision`/`Version`, delete's count, txn's `Failure` and op results.
- **Nondeterminism**: the pending *writes* (put, delete, writing txn) generalize the pending
  puts; a failed read constrains nothing. `KVSet.Closed`: closed under any pending write taking
  effect (`mStep` at the configuration's state). The powerset construction, `kvSeq_*` lemmas and
  `lintest`'s theorem carry over.
- **Shapes** (`InShape`): keys from `genKeys`; write keys of a txn distinct (else `checkIntervals`
  rejects: an error, still sound, but no check); no nested txn, no range end `[0]`, no limit, no
  lease. Lemma: `InShape` ⇒ `txnPlain ∧ txnNoZeroEnd ∧ siblingSafeL ∧ OpsNoCut` and the check
  passes (`kvDepPre`'s writing-txn case).
- **Against etcd's state** (`ModelKV.lean`): `absS : KVState → MState`; for `InShape` ops,
  `absS (kvOpStep (opOf i) σ) = (mStep i (absS σ)).1` and the reply facts of B3 give
  `(mStep i (absS σ)).2`. The txn case is the work: `srvRunTxn` on a plain flat txn over distinct
  keys, reads inside the txn seeing its earlier writes (etcd's `storeTxnWrite.Range`; robustness's
  `getRange` on `newState`); `txn.txnOk` of the three compare kinds.

### D. The Go program (`examples/linkv/linkv.go`)

**Done** (2026-10-20) as a new module `examples/linkvtxn` (STATUS "linkv-txn stage D"), linkv
unchanged.

- `Input`/`Output` widened (an op kind, a key, a value, cmps and ops for a txn; the response
  fields above). Keep plain structs with slices of small structs: Goose-friendly, and
  `Input_intoVal_inj`/`Output_intoVal_inj` still come from the field projections.
- `Gen`: robustness's `EtcdPutDeleteLease` weights without leases and stale reads (Get 15,
  List 8, Put 20, Delete 5, MultiOpTxn 10, CAS 5); 3 keys, a few values; CAS compares on `Value`
  (small domain: often succeeds) and on `Version`/`ModRevision` (rarely).
- `Apply`: one case per kind through `cli.Get`/`Get(WithPrefix)`/`Put`/`Delete`/`Txn`; the ok
  prophecy as now; the revision prophecy for every persistent-read kind (get, list, read-only
  txn).
- `Model()`: the configurations as now, `step` per kind (txn: compare evaluation, ops in order,
  one revision bump), `closure` over pending writes.
- **That the model is etcd's**:
  - unit tests as now, plus rejected histories: a lost delete, a txn run in the wrong branch, a
    read inside a txn not seeing the txn's own put, a revision going backwards or skipping;
  - a **differential test** (`_test.go` only, not translated): random histories (and recorded
    ones from `TestLinkv`) checked with our `Model()` and with robustness's
    `model.NonDeterministicModel` (`go.etcd.io/etcd/tests/v3/robustness/model`, histories
    translated to its `EtcdRequest`/`MaybeEtcdResponse`); the verdicts must agree;
  - `go test -race` against the in-process member, as now.
- Regenerate (`etc/goose.py --project linkv`); `--check` in CI.

### E. The Go model's proofs

**Done** (2026-10-20, STATUS "linkv-txn stage E"): every function of the model specified and
proved, `Model` linked against `pM (txnSpec wks)`; `Input`/`Output` made plain values first.

Per helper, one spec/proof file (as `lookup`, `set`, …): compare evaluation, the txn's op loop,
`delete`, the list, `step`, `closure` (pending writes), `Model` (`isModel linkvS` with
`rep k = stRepB (k + 1)`; lengths and revisions bounded by the step index `< 2^60`).
`ModelLemmas.lean`'s `stepL`/`absCfg`/`decIO` generalized; `step_closure_ok` re-proved.

### F. `Apply` (`Spec/.../linkv/Apply.lean`, `linkv/Inv.lean`, `linkv/Apply.lean`)

**Done** (2026-10-20, STATUS "linkv-txn stage F") for `examples/linkvtxn`: `call` split per kind,
each kind's call proved at the state its update fired at, `Apply` linked (`wp_Apply`). A finding on
the way: a compare-only `Txn` skips the read index (`issues/etcd-txn-empty-serializable.md`);
`Apply`'s input excludes empty transactions, which `Gen` never makes.

- Premises: `DeleteRange` and `Txn` registered (`etcd_kv_served` gives all four).
- `linkvInv`: pending writes `GMap Nat WOp`; the revisions' map holds the abstract state per
  revision (`absS`, not key-values: List and read-only txns read all keys); `LinkvOk` with
  `c.st = absS σ`.
- Commits, generic over the kind: `write_ok_au` (a `kvOpAu1` committing lintest's update at the
  firing, output `(mStep i (absS σ)).2`), `write_err_commit` + `write_pend_au` (pending write
  token, late firing from the invariant), `read_ok_au` (persistent read update + revision
  prophecy: get, list, read-only txn), `read_err_commit`.
- `Apply`'s proof: one branch per kind; most of the work is the reply-to-output step (B3, C).

### G. Close

**Done** (2026-10-20, STATUS "linkv-txn stage G"): `linkvtxn_safe`, its axioms `linkv_safe`'s
(`proto.Clone` was already in its trust base, through the server). linkv stays (linkv3, linkv3p).

For `examples/linkvtxn` (stage D made it a module of its own): `Gen` (`genFrom`, `pick`, `mkTxn`,
`workloadKeys`: `GenIn`, which `Apply`'s input premise is), `Check`, `Main` (linkv's, at
`linkvtxnS` and `linkvInv`'s allocation from the boot state: `linkvInv_alloc` needs a good state
that is the model's initial one), the closed theorem `linkvtxn_safe` (as `linkv_safe`), its
`Results.lean` and a TCB collection; `etc/gen-init.py` if the package's init changes. Then decide
whether linkv retires (linkv3/linkv3p still use it). Gates: `lake build`, `goose.py --check`, every
link mode, `tcb-report.py --check` and every collection (`linkvtxn_safe`'s axioms linkv_safe's plus
the client's comparison clone, `proto.Clone`), `verified-code.py` shows the new functions verified.
STATUS and decisions updated.

## Order and sizing (rough)

A (≈ the size of D21 M6's client/server half) and C+D can start in parallel; B1 is the one
unknown (fallback above); E is mechanical but long (the txn loop); F is the size of linkv's
current Apply plus the txn case. A sensible cut: **first Delete + MultiOpTxn without reads**
(A, B3 for delete/put, C/D/E/F without B1/B2), closed; **then** reads inside txns (B1),
read-only txns and List (B2), CAS with `Else(Get)`.

## Out of scope (each a later plan)

- **Stale reads** (`WithRev(r)`, robustness's `StaleGet`/`StaleList`): the verified server answers
  them (`mvcc.stateAt`, under `backendNoCompaction`); the model would keep past states, or check
  only as robustness does (`Persisted` with the revision).
- **Serializable reads**: not linearizable; robustness validates them separately by replay. A
  separate theorem.
- **Leases** (`PutWithLease`, `LeaseRevoke`): unit T3 (STATUS "Open work", item 1).
- **Compaction, defragmentation**: removes the premise `mvcc.backendNoCompaction`; model
  `CompactRevision`, `ErrCompacted`.
- **Watch** validation (robustness's watch checks): `watchkv` is the start.
- **Nested txns, limits, sort, range ends `[0]`**: where `issues/etcd-txn-*` live; the shape
  restriction keeps them out.
