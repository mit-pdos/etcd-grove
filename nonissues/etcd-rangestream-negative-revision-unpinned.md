---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# etcdserver: a streamed range at a negative revision is read at a new revision on every page

`RangeStream` pins the revision of its pages only when the request asks for revision `0`
([`server/etcdserver/v3_server.go`](https://github.com/etcd-io/etcd/blob/main/server/etcdserver/v3_server.go),
`rangeStream`: `if r.Revision == 0 { r.Revision = headerRev }`). A negative revision passes the gRPC
layer's checks (`api/v3rpc/key.go`, `checkRangeStreamRequest`) and the client's `toRangeRequest`
unchanged, and mvcc reads a non-positive revision as the current one, so each page (and the final
count) is read at the then-current revision: `GetStream(ctx, k, WithRange(end), WithRev(-1))` returns
pages of different revisions, a list that may skip a key moved between pages or show one twice,
under a header revision that only the first page was read at. A unary `Range` treats a negative
revision as the current one, consistently.

**Why not an issue:** no test; found by code reading (the client model's round-2 review,
2026-11-09); no user found passes a negative revision (Kubernetes passes a positive one or none),
and a negative revision is not a documented value of `WithRev`. A test could promote it: a stream of
two pages with a put between them (the failpoint `beforeRangeStreamChunk`).

## Proof

no: the client's `GetStream` spec takes `0 ≤ revision`
(`SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean`, `KV.GetStreamTriple`), which every user meets.

## Notes

Fix, if wanted: pin when `r.Revision <= 0`, or refuse a negative revision in
`checkRangeStreamRequest`.
