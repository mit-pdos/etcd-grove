---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#22615 pr open: would fix this bug without saying so: it fixes #22612 (etcd-range-sort-none-limit) by making IsDefaultOrdering false for a non-key target with NONE, so checkRangeStreamRequest rejects these requests, as this candidate's fix does (run 2026-10-23: this candidate's test then gets Unimplemented; main's TestV3RangeRequest/sort fails under #22615 until its RangeStream expectation is updated)
  - etcd-io/etcd#21631 pr merged: related, not this bug (the RangeStream server, whose IsDefaultOrdering check is the defect)
  - etcd-io/etcd@9acc0ebe3: related, not this bug (clones the chunk's last key before appending \x00 in rangeStream; does not touch the sort check)
candidate: issues/upstream/etcd-rangestream-sort-none/
---

# server: RangeStream accepts a sort by a non-key target with no order and returns duplicated and missing keys

- **Status**: open (a wrong result, reachable from clients: `clientv3.KV.GetStream` with
  `WithSort(SortByVersion, SortNone)`; not filed, no fix branch). Found 2026-10-12 while fixing
  [etcd-range-sort-none-limit](etcd-range-sort-none-limit.md); not part of the verified code
  (`RangeStream` is not translated).
- **Where** (`main` at f061acd0902d489041448cdd19d71a345d27b9f5): `checkRangeStreamRequest`
  (`server/etcdserver/api/v3rpc/key.go:169-180`) rejects "custom sort orders" with
  `!txn.IsDefaultOrdering(r.SortTarget, r.SortOrder)`, which is true for any target with
  `SortOrder == NONE`. But `txn.Range` sorts `NONE` with a non-key target as `ASCEND`
  (`server/etcdserver/txn/range.go:126-129`). `EtcdServer.rangeStream`
  (`server/etcdserver/v3_server.go:197-270`) serves the stream as chunks, each a `txn.Range` with a
  chunk limit, and starts the next chunk after the last key of the previous one
  (`nextKey = resp.Kvs[len(resp.Kvs)-1].Key + "\x00"`); with the chunk sorted by version, that
  key is not the chunk's largest, so chunks overlap and skip keys, and `Count` sums the chunks.
- **What happens**: 12 keys `ka`..`kl` with versions 12..1; `GetStream("k", WithPrefix(),
  WithSort(SortByVersion, SortNone))` then `GetStreamToGetResponse`:
  on `main`, `[kk kj ki kh kg kf ke kd kc kb kl kk kj ki kh kg kf ke kd kc]`, `Count` 20;
  with the `range-sort-none-limit` fix (7362d4129), `[kl kk kj ki kh kg kf ke kd kc kl kk kj ki kh
  kg kf ke kd]`, `Count` 19 (and each chunk now reads the whole rest of the range). `Get` with the
  same options returns the 12 keys sorted, `kl` first; `GetStream` with `SortAscend` is rejected
  with `Unimplemented: RangeStream does not support custom sort orders`. Reproduction (in
  `tests/integration/clientv3`): put key `k` + `'a'+i` `12-i` times for `i` in `0..11`, then the
  call above.
- **How it happens**: `RangeStream` serves a range as a sequence of chunks. Each chunk is an
  ordinary `txn.Range` with a small limit, and the next chunk starts just after the last key of
  the previous one. That is correct only if every chunk is in key order, so the stream rejects
  custom sort orders with `IsDefaultOrdering`. But `IsDefaultOrdering` is true whenever the
  order is `NONE`, whatever the target, while `txn.Range` sorts a non-key target with order
  `NONE` as `ASCEND`. So a request sorted by version with no order passes the check, and each
  chunk comes back sorted by version. Its last key is then not its largest key, and the next
  chunk starts in the middle of the keys already sent. On `main`, with the example above:

  1. Keys `ka`..`kl` have versions 12..1. The client calls `GetStream("k", WithPrefix(),
     WithSort(SortByVersion, SortNone))`; `checkRangeStreamRequest` accepts it (the order is
     `NONE`).
  2. Chunk 1 has limit 10. `txn.Range` reads 11 keys in key order (`ka`..`kk`, one more to
     detect `More`), sorts them by ascending version (`kk` (2), `kj` (3), ..., `ka` (12)) and
     keeps 10: `kk kj ... kb`, with `More` set. `ka` is dropped.
  3. The next chunk starts after the chunk's last key, `kb`: at `kb\x00`.
  4. Chunk 2 (limit 20) reads `kc`..`kl` and sorts them: `kl kk ... kc`. Nine of these keys
     were already sent in chunk 1. `More` is false, so the stream ends.
  5. The client gets 20 key-values: `ka` is missing, `kc`..`kk` appear twice, and `Count` (the
     sum of the chunks) is 20.

  ```go
  // server/etcdserver/api/v3rpc/key.go:169-180 (etcd main f061acd09)
  func checkRangeStreamRequest(r *pb.RangeRequest) error {
  	if err := checkRangeRequest(r); err != nil {
  		return err
  	}
  	if !txn.IsDefaultOrdering(r.SortTarget, r.SortOrder) { // <-
  		return status.Errorf(codes.Unimplemented, "RangeStream does not support custom sort orders")
  	}
  	// ...
  }
  ```

  ```go
  // server/etcdserver/txn/range.go:97-103 and 125-129 (etcd main f061acd09)
  func IsDefaultOrdering(sortTarget pb.RangeRequest_SortTarget, sortOrder pb.RangeRequest_SortOrder) bool {
  	// ...
  	return sortOrder == pb.RangeRequest_NONE || // <-
  		(sortTarget == pb.RangeRequest_KEY && sortOrder == pb.RangeRequest_ASCEND)
  }
  // ...
  func sortRangeResults(rr *mvcc.RangeResult, r *pb.RangeRequest, lg *zap.Logger) {
  	sortOrder := r.SortOrder
  	if r.SortTarget != pb.RangeRequest_KEY && sortOrder == pb.RangeRequest_NONE { // <-
  		sortOrder = pb.RangeRequest_ASCEND
  	}
  ```

  ```go
  // server/etcdserver/v3_server.go:244-247 and 269-271 (etcd main f061acd09)
  		var nextKey []byte
  		if resp.More {
  			nextKey = append(resp.Kvs[len(resp.Kvs)-1].Key, '\x00') // <-
  		}
  	// ...
  		r.Key = nextKey
  		r.Limit = adjustChunkLimit(r.Limit, proto.Size(resp), int(s.Cfg.MaxRequestBytes))
  		r.Limit = min(r.Limit, totalLimit-count)
  ```
- **Expected**: rejected like `SortAscend` (`Unimplemented`), or streamed in the sorted order.
- **Possible fix**: in `checkRangeStreamRequest`, test the order `txn.Range` sorts by (`NONE` with
  a non-key target is `ASCEND`), e.g. by exporting `txn`'s `rangeSortOrder` from the
  `range-sort-none-limit` fix, or make `IsDefaultOrdering` false for a non-key target with `NONE`
  (then `tests/common/kv_test.go`'s `rangeStreamSupports`, which mirrors the check, follows).
