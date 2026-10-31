---
upstream: unchecked
checked: 2026-10-30
links: []
---

# etcdserver: a transaction nested 4999 deep passes gRPC and panics every member at apply (with --max-txn-ops ≥ about 5000)

- **Status**: bug (a reachable panic of the apply loop, persistent across restarts), reachable only
  with a non-default `--max-txn-ops`. Found by the axiom review of the nested-transaction wire
  model (`notes/axiom-review/txn-nested-wire.md`).
- **Where** (the fork's `goose-lean`, `249d76bea7`; upstream `main` the same code):
  - `server/etcdserver/api/v3rpc/key.go:202-231, 333-334`: `checkTxnRequest` recurses into nested
    transactions (`checkRequestOp`'s `RequestOp_RequestTxn` case) with the budget `maxTxnOps - opc`,
    so a chain of nested transactions of one operation each may be about `--max-txn-ops` deep; no
    other bound on the depth.
  - gRPC's codec decodes the request with protobuf-go's default recursion limit
    (`protowire.DefaultRecursionLimit`, 10000 message levels): a request at most 10000 levels deep
    is accepted.
  - `server/etcdserver/v3_server.go:1094`: the request is wrapped in an `InternalRaftRequest`
    (one level more) and marshalled into a raft entry (marshalling has no depth limit).
  - `server/etcdserver/apply/apply.go:29`: `apply.Apply` decodes every committed normal entry with
    `pbutil.MustUnmarshalMessage` (`proto.Unmarshal`, the same 10000 limit), which panics on error.
- **What happens**: a `TxnRequest` whose innermost transaction has one comparison, nested 4999 times
  (each level a `RequestOp` holding the next `TxnRequest`), is 10000 messages deep: gRPC decodes
  it; with `--max-txn-ops` at least about 5000, `checkTxnRequest` accepts it; the server proposes
  its 10001-deep `InternalRaftRequest` (34 KB, far below `--max-request-bytes`); raft commits it;
  every member's apply loop panics, `unmarshal should never fail (proto: exceeded maximum recursion
  depth)`. The entry is in the WAL: a restarted member replays it and panics again. One client
  request takes the cluster down for good. Through the client's public API:

  ```go
  op := clientv3.OpTxn([]clientv3.Cmp{clientv3.Compare(clientv3.Version("k"), "=", 0)}, nil, nil)
  for i := 0; i < 4998; i++ {
      op = clientv3.OpTxn(nil, []clientv3.Op{op}, nil)
  }
  cli.Txn(ctx).Then(op).Commit()
  ```

  Reproduction: `examples/axiomcx/txnwire/poison_test.go` on branch `axiom/txn-nested-wire`
  (`TestNestedDepthPoison`: one member with `MaxTxnOps: 10000`, the member panics in
  `apply.Apply`; with `TXNPOISON_DIR` set, `TestNestedDepthPoisonRestart` restarts it from the same
  data directory and it panics again). `TestDepthBoundary` (`depth_test.go`) shows the boundary
  without a server: the 4999-deep request decodes, its `InternalRaftRequest` does not; a request
  one level deeper is refused by gRPC with `codes.Internal` (`TestNestedDepthRefused`, harmless).
  With the default `--max-txn-ops` (128) the nesting stays below about 128 levels and the bug is
  not reachable.
- **Expected**: a request the gRPC layer accepts and the server proposes can be applied; a request
  too deep for the apply path is refused before it is proposed.
- **How the proof handles it** (2026-10-31, branch `irr-depth`, `notes/irr-depth.md`; the user's
  approval, `notes/decisions.md`, "A depth premise for `proto.MarshalIRR`"): as a premise and a scope
  restriction. Until then `proto.MarshalIRR.wp_proof` (an axiom) said the marshalled bytes of any
  `InternalRaftRequest` decode, which is false of one 10001 messages deep. Now:
  - `proto.MarshalIRR.spec` (`Spec/google_golang_org/protobuf/proto/MarshalIRR.lean`) takes the
    premise `apply.irrDepthOk rq` (`apply/IrrDepth.lean`: the request's transaction at most 9999
    messages deep, `TxnModel.msgDepth`), its post unchanged;
  - the server's proposer (`processInternalRaftRequestOnce.spec`, `raftRequest.spec`) takes the same
    premise, and `EtcdServer.Txn.spec` takes `apply.txnDepthOk t` of a writing transaction;
  - the gRPC handler discharges it: `v3rpc.txnCheck_msgDepth` (`v3rpc/CheckLemmas.lean`) proves that
    a transaction `checkTxnRequest` accepts at the budget `n` is at most `2n + 1` messages deep, and
    the `*kvServer` keeps `v3rpc.maxTxnOpsOk (sint.Z n)` (`n ≤ 4999`, `v3rpc/RecvLimit.lean`);
  - `NewServer.spec` takes `v3rpc.maxTxnOpsOk (sint.Z cfg.MaxTxnOps')`: the **scope restriction**,
    exact (at 5000 the 4999-deep chain above passes the check and panics the apply). etcd's default
    (128) meets it; the examples discharge it (`MaxTxnOps: 128`).
- **Possible fixes**: bound the nesting depth in `checkTxnRequest` (a depth parameter; a limit
  well below 5000, e.g. 64 or `maxTxnOps`-independent); or check, before proposing, that the
  marshalled `InternalRaftRequest` decodes (cost: one decode per write); or decode raft entries
  with a larger `RecursionLimit` (`proto.UnmarshalOptions`), which only moves the boundary unless
  gRPC's limit is kept strictly below it.
- **Found**: 2026-10-30, the `axiom` skill's review of the nested-transaction wire model (the
  attack "the server's decoded copy reproduces the client's tree": the gRPC decode does; the raft
  round trip does not).
