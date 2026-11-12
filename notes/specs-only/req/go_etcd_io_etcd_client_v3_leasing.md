# Requirements on `go.etcd.io/etcd/client/v3/leasing` (batch 1e)

## from W0

1. **Leasing's KV does not meet the client's KV contract (`kvAt`)**, so 1e needs its own contract
   (as the old proofs' `getOutcome`), not `ClientV3.kvAt`. A cached `Get` answers with the cached
   response's header (`leasing/cache.go`, `copyGetResponseMetadataOnly` over `li.response`; served
   at `leasing/kv.go`), whose revision is the one leasing last saw for that key, not the cluster's
   current revision, while `KV.GetTriple`'s linearizable answer is `.range σ.kv.rev a`; and
   `issues/leasing-update-stale.md` (blocks-proof: yes) already makes its values diverge. The stale
   header is observable: `examples/specreq/clientv3kv/history.go`'s `ReqRevisionsMonotone` would
   panic through a leasing KV after a put through another client. W0's `Api.lean` no longer lists
   leasing among the wrappers that realize `kvAt`.
   ```go
   resp, _ := lkv.Get(ctx, "k")   // cached: resp.Header.Revision may be below a revision seen elsewhere
   ```
   Used by: none of W0's specs; 1e's own contract and snippets.

2. Leasing builds on the client's vocabulary as is: `OpM`, `opAt`, the `Op` getters and `Do`
   (`KV.DoTriple` over the client it wraps), nested transactions (`OpTxn`), `Cmp.KeyBytes`,
   `Cmp.GetCompare`, and the replies' unfold laws to write into replies (`Wire.lean`, at `own 1`).
