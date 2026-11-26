# F7 S11 review: `Txn_CommitOn_dist` widened to nested transactions (2026-11-26)

This review used the `axiom` skill and was read-only on the Lean tree. I read `/shared/etcd-grove-f7ra` (branch
`etcd-safe-f7-runauth`, head `3830cea6ed`); the change reviewed is `git diff f4406f31f7 e0e078b74e` of
`Spec/.../etcd/dist/TxnCommitOnDist.lean` and its `Proof/` file. The Go source is the etcd checkout of
`f7-s5-gotest/etcd` (the harness of the earlier F7 reviews), run with go1.27.3; tests in
`f7-txn-nested-gotest/`.

**Target.** `Perennial.EtcdGrove.etcd_dist.authd.Txn_CommitOn_dist.wp_proof` (`Txn_CommitOn_dist.spec`):

- the shared pure premise `⌜TxnModel.plain b.model ∧ txnModelIn (txnWireOf b.model)⌝` became
  `⌜txnModelIn (txnWireOf b.model)⌝`;
- the write arm's pure premise gained `∧ txnNestOk (txnWireOf b.model)`.

So a writing transaction may now contain `OpTxn`s at any depth, in either branch. Nothing else changed.

## Verdict

**SOUND.** I found no counterexample. The widened premise is exactly the write arm of the proved single-process
contract `client.txnUpdAtOn` (`KVServiceOn.lean:985`: `txnReadonly = false ∧ (txnPlain ∨ (lm = revocable ∧ txnPlainL))
∧ txnNoZeroEnd ∧ txnNestOk`). `client.client_txn_on` (`ResultsOn.lean:371`) is proved over it with no plainness premise.
The proof covers the nested semantics through the real server code: the v3rpc checks, `checkIntervals`, the apply-time
auth check, `compareToPath`, and `executeTxn`. In Go, the cross-machine behaviour (grant at apply time, one commit,
the response) matches the model in 22 cases × 3 members.

## What the widening admits, and the model it is checked against

- **Grant** (`writeCheckedD … (irrTxn tw)`, `opGrantD`, through `grantedAt` and `kvGranted`): `reqPerms` of a txn
  is the comparisons' reads plus `opsPerms` of both branches. For a nested txn, `opPerms (.txn cs ts es)` is its
  comparisons' reads plus both of its branches, recursively. This is etcd's `checkTxnPermission`, which calls
  `checkTxnReqsPermission` on the `RequestOp_RequestTxn` case (`server/etcdserver/apply/auth.go:128-180`). A
  nested put's checks are `checkPutAuth` (the key, the lease's keys, `PrevKv`'s read), the same as a top-level
  put's. In the model they are `apply.putPerms` and `leaseGrantedM`'s `txnPutsW`, which recurse into both
  branches.
- **Step** (`kvOpStep (.txn t)` = commit of `srvRunTxn`): nested verdicts are evaluated at the read state `s0`
  (`srvOp`'s `cmpHolds s0`, as `compareToPath`). Operations run in order, each at the state the previous ones
  left (`srvOps`, as `executeTxn` on one `txnWrite`).
- **Premise `txnNestOk`**: it rules out two shapes. The first is a get cut early by a limit, at any depth
  (`OpsNoCut`). The second is a nested put that a later sibling deletes (`txnSibSafeL`). That is the shape etcd
  accepts but `check_gives_nodup` needs excluded (`issues/etcd-txn-check-intervals-sibling.md`).
  `txnModelIn` now constrains only top-level gets. Nested gets are covered by `txnPlain` (revision 0, at any
  depth) and by `OpsNoCut`.
- **Read-only arm**: unchanged in effect. A read-only transaction is flat (`txnReadonly_plain`). A txn whose
  only operations are nested gets is not read-only (`opIsGet (.txn ..) = false`, as etcd's `IsTxnReadonly`), so it
  goes through the write arm and raft.

## Attacks tried (Go: `f7-txn-nested-gotest/`, all PASS at m0, m1, m2)

1. **Refusal not modelled** (the post claims `grantedAt` for a success the user had no right to): T4's nested put
   outside the user's range was refused. So were the same beside a permitted put (all or nothing), a nested put
   on the untaken outer `Else`, a nested put on the untaken branch of a nested txn, a nested comparison on an
   unreadable key, a write-only user's nested comparison and nested `Delete WithPrevKV`, a 40-deep nested put
   outside the range, and a raw gRPC request with a nested put (not flattened by the client). Every one got
   `permission denied`, with no revision step. So Go refuses whenever the model refuses. Where the model grants
   (a write-only user's nested put), Go succeeds.
2. **Step mismatch**: a permitted nested txn, and a 40-deep one, each made exactly one revision step, with
   `Header.Revision` the new revision and every nested `Succeeded` true. A nested comparison after an outer put
   was evaluated at `s0`: else branch, as `srvRunTxn`. A nested get after an outer put read the put, as
   `srvOps`. A writing txn holding only a nested get went through raft with no revision step (`σ.commit []`).
   One key put in both branches of a nested txn ran only the taken one.
3. **Sibling conflicts**: delete-then-put in nested siblings was refused with `duplicate key`, as were a nested
   put with a top-level delete (both orders) and two nested siblings putting one key. All of these land in the
   error arm. A put in a nested sibling followed by a delete in a later one is accepted by Go. That shape is
   excluded by `txnNestOk`, so it is not a counterexample. Even there, the store agrees with the in-order run
   (the key ends deleted, one step); only watch events differ, as the issue records.
4. **Retries / double application**: `Op.isWrite` recurses into both branches (`client/v3/op.go:235`), and
   `Commit`'s call options do not depend on it. `writeAuD` is `□` anyway.
5. **Depth**: a transaction about 5000 deep panics every member at apply
   (`issues/etcd-txn-nested-depth-apply-panic.md`). That is the server's obligation. It is discharged by
   `maxTxnOpsOk` in `NewServerDist.lean`, and the examples set `MaxTxnOps: 128`. The client axiom claims
   nothing about it: the error arm covers a refused request, and partial correctness covers a dead cluster.
   Not a gap of this axiom.

## Noted, not a defect of the widening

- `client_txn_on` takes `hsh` (`kvShapeAll (irrTxn tw)`: every permission of the request in the cache's decided
  shape), but the dist axiom has no such premise (nor do the other dist axioms). That is safe for the success
  post. For a request outside `reqShape` (an inverted or empty `[key, end)`), the model's `covers` is vacuous, so
  the model grants at least whatever Go grants. `kvShapeAll` matters only for a refusal's content, and the dist
  error arm claims nothing. Nesting adds more permissions but changes nothing here, because `checkRequestOp`
  still rejects empty keys at every depth.

No spec defect found. Not tried: compaction or a snapshot between the nested txn's proposal and its apply (as
for flat txns, the read state is the apply-time state, the same in both).
