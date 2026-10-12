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
- **Expected**: rejected like `SortAscend` (`Unimplemented`), or streamed in the sorted order.
- **Possible fix**: in `checkRangeStreamRequest`, test the order `txn.Range` sorts by (`NONE` with
  a non-key target is `ASCEND`), e.g. by exporting `txn`'s `rangeSortOrder` from the
  `range-sort-none-limit` fix, or make `IsDefaultOrdering` false for a non-key target with `NONE`
  (then `tests/common/kv_test.go`'s `rangeStreamSupports`, which mirrors the check, follows).
