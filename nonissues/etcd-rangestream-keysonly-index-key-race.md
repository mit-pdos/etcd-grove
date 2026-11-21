---
upstream: fixed
checked: 2026-11-21
links:
  - etcd-io/etcd@9acc0ebe37: the fix, "etcdserver: fix data race in keys-only RangeStream" (2026-10-15): `append(bytes.Clone(lastKey), '\x00')`
  - etcd-io/etcd@fd2cc937c9: introduced it, "*: implement server-side RangeStream"
blocks-proof: yes
---

# etcdserver: keys-only RangeStream appends into mvcc's in-memory index keys

A keys-only `RangeStream` computes the next page's start key by appending a zero byte to the last
key of the page it just read. For a keys-only read that key is mvcc's own index key, so the append
writes into the spare capacity of the index's key array. Two concurrent keys-only streams over the
same keys both write that byte: `go test -race` reports a data race. Both write `0` past the key's
length, so no value read by anyone changes and nothing panics.

**Why not an issue:** fixed upstream (etcd-io/etcd@9acc0ebe37, 2026-10-15, after the commit the fork
`upamanyus/etcd` was based on); found by the independent review of the trust-boundary spec of
`rangeStream` (`notes/axiom-review/rangestream.md`, 2026-11-21). The fork carries upstream's fix since
2026-11-21 (`4416a5786`, branch `goose-lean-rangestream-clone`, the cherry-pick of 9acc0ebe37 on
`34f5142d0`; the user's choice, auth-mediation Q4 option (i)).

**How:** `server/etcdserver/v3_server.go:246` at the fork's `d3feef9bcd`,
`nextKey = append(resp.Kvs[len(resp.Kvs)-1].Key, '\x00')`; with `KeysOnly` (and the default sort),
mvcc's `treeIndex.Range` returns the index's key slices (`server/storage/mvcc/index.go:177`), which
the keys-only read puts in the response (`kvstore_txn.go`). The race test:
`examples/authmedrangestream/review_test.go`, `TestConcurrentKeysOnly`, run with `-race`: it reports the race at `34f5142d0` and passes at `4416a5786`.

## Proof

yes: the race makes the trust-boundary spec of `rangeStream`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__rangeStream.lean`) false of the old body in
GooseLang (racing stores are stuck) for two concurrent keys-only calls; the fork carries upstream's
fix (`4416a5786`: `append(bytes.Clone(lastKey), 0)`), so the next key is a fresh slice and the spec
no longer needs the margin it had.
