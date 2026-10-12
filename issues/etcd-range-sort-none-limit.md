# server/etcdserver/txn: a range sorted by a non-key target with no order and a limit returns the wrong keys

- **Status**: open (a wrong result, reachable from clients: `etcdctl get --sort-by=VERSION
  --limit=1` without `--order`; not filed).
- **Where**: `server/etcdserver/txn/range.go` at bc8b52a50 (`etc/goose.py`'s etcd pin):
  `rangeLimit` (`range.go:86-95`) keeps the request's limit (plus one) when
  `IsDefaultOrdering(r.SortTarget, r.SortOrder)` (`range.go:97-103`) holds, and it does for any
  target with `SortOrder == NONE`; `sortRangeResults` (`range.go:125-154`) then turns `NONE` into
  `ASCEND` for a target other than the key (`range.go:126-129`, since 1cd6fefd4, 2016: "set sort
  ASCEND for empty sort order") and sorts. So mvcc reads only the first `limit + 1` keys of the
  range (in key order), those are sorted by the target, and `asembleRangeResponse` keeps the first
  `limit`: the response is the first `limit` of a sort of a key-order prefix, not of the range.
  With an explicit `ASCEND` the limit is dropped (`IsDefaultOrdering` is false), the whole range
  is read and sorted, and the answer is right. The client's `WithSort(target, SortNone)`
  (`client/v3/op.go:386`) sends exactly `NONE` with a non-key target; `etcdctl get` does when
  `--sort-by` is given without `--order` (`etcdctl/ctlv3/command/get_command.go:153-185`).
- **What happens**: keys `a` (version 3), `b` (version 2), `c` (version 1); a range over
  `[a, d)` sorted by `VERSION` with limit 1 returns `b` with `SortOrder: NONE`, `c` with
  `SortOrder: ASCEND`. Reproduction (in `server/etcdserver/txn/`, next to `txn_test.go`'s
  `setup`; `go test -run TestRangeSortNoneLimitProbe -v`):

  ```go
  func TestRangeSortNoneLimitProbe(t *testing.T) {
  	s, _ := setup(t, testSetup{})
  	for i := 0; i < 3; i++ { // versions: a=3, b=2, c=1
  		s.Put([]byte("a"), []byte("v"), 0)
  	}
  	for i := 0; i < 2; i++ {
  		s.Put([]byte("b"), []byte("v"), 0)
  	}
  	s.Put([]byte("c"), []byte("v"), 0)
  	lg := zaptest.NewLogger(t)
  	for _, order := range []pb.RangeRequest_SortOrder{pb.RangeRequest_NONE, pb.RangeRequest_ASCEND} {
  		resp, _, err := Range(context.Background(), lg, s, &pb.RangeRequest{
  			Key: []byte("a"), RangeEnd: []byte("d"), Limit: 1,
  			SortTarget: pb.RangeRequest_VERSION, SortOrder: order,
  		}, true)
  		if err != nil {
  			t.Fatal(err)
  		}
  		t.Logf("order %v: key %q version %d more %v count %d", order, resp.Kvs[0].Key,
  			resp.Kvs[0].Version, resp.More, resp.Count)
  	}
  }
  ```

  Output: `order NONE: key "b" version 2 more true count 3` and `order ASCEND: key "c" version 1
  more true count 3`.
- **Expected**: the same answer as `ASCEND` (the server's own reading of `NONE` with a non-key
  target): the `limit` key-values of the lowest versions in the range.
- **How the proof handles it**: the server's result is stated as the code computes it
  (`srvPre`/`srvSorted`/`srvTrunc`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/RangeModel.lean`);
  the bridge to the client model's `rangeKvsOk` of `rangeSel` (`srvRangeOk_rangeKvsOk`, and
  `range_rangeSel` in `Results.lean`) takes the premise `¬ cutEarly o` (the server sorts and mvcc
  read with a positive limit), which excludes exactly these requests.
- **Possible fixes**: in `rangeLimit`, test the order `sortRangeResults` uses (`NONE` with a
  non-key target is `ASCEND`): e.g. `if r.SortTarget != pb.RangeRequest_KEY && sortOrder == NONE
  { sortOrder = ASCEND }` before `IsDefaultOrdering`, or drop the limit whenever the target is
  not the key.
- **Found**: 2026-10-11, specifying `executeRange` against the client model (txn unit 2),
  confirmed by the test above.
