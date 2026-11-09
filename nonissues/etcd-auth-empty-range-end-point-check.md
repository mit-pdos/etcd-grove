---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: yes
---

# auth: a range with a non-nil empty end is permission-checked for its key alone but reads every key from it on

A linearizable or serializable `Range` (or a read-only `Txn`) whose `RangeEnd` is a non-`nil`
empty byte slice passes the permission check if the user may read the request's key alone. The
read then returns every key from that key on, including keys the user has no permission to read.

**Why not an issue:** no test; found by code reading while integrating the auth store's specs
(2026-11-09). gRPC cannot carry such a request. proto3 does not encode an empty `bytes` field, so
the server decodes the end as `nil`, which both the check and mvcc read as the key alone. The bug
needs an in-process client: the gRPC-proxy's adapters (`server/proxy/grpcproxy/adapter`,
`v3client`), which hand the `*pb.RangeRequest` to the server's handlers without marshalling it.
The request must also carry a token in its context. `clientv3.WithRange("")` through
such a client gives such a request.

**How:** the request path checks a read before running it: `EtcdServer.Range` calls
`IsRangePermitted(ai, r.Key, r.RangeEnd)` (`server/etcdserver/v3_server.go:146`), and a read-only
`Txn` calls `apply.CheckTxnAuth` (`v3_server.go:355`). `isRangeOpPermitted` tests
`len(rangeEnd) == 0` and calls `checkKeyPoint`, which checks the key alone
(`server/auth/range_perm_cache.go:124`). mvcc reads the same request differently.
`treeIndex.Revisions` tests `end == nil` for a single key. Otherwise it calls `unsafeVisit`, which
drops the upper bound when `len(end) == 0`, so the read covers every key from the key on
(`server/storage/mvcc/index.go:99,116`). The model reads a range end the same way as mvcc
(`EtcdWire.endOf`). The apply thread's checks of writes (`DeleteRange`, a `Txn`'s operations) are
not affected: they run on the request decoded from the raft entry, where the end is `nil` again.

## Proof

yes, for the request path's read checks (2c's `Range`, `RangeStream` and read-only `Txn`, and 3a's
`CheckTxnAuth`): at this input their posts, which say the model's range is permitted, are false.
The specs sidestep it with a scope premise. 3a's `CheckTxnAuth.spec`, `checkTxnPermission.spec`
and `checkTxnReqsPermission.spec` take `endsDecoded rt` / `opsDecoded sl`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/Api.lean`, provisional for W0/3h): every range
end in the message is `nil` or non-empty, as gRPC's decoding gives. The apply thread gets it from
the decoded entry (`reqMsgAt_endsDecoded`). 2c's `Range` needs the same premise on its
`rangeReqOwn`, or its gRPC caller's decoding fact. The auth store's specs (3d) state the code's
behavior (`IsRangePermitted`'s check is over `{key, e}` with the raw slice; their Margin). The
premise excludes only in-process requests built with a non-`nil` empty end.

## Notes

A fix: `isRangeOpPermitted` (or `checkRangeRequest` in `api/v3rpc`) could normalize the end as
mvcc reads it: treat a non-`nil` empty `RangeEnd` as `"\x00"`, or refuse it.
