---
upstream: fixed
checked: 2026-11-21
links:
  - etcd-io/etcd@9acc0ebe37: the fix, "etcdserver: fix data race in keys-only RangeStream" (2026-10-15): `append(bytes.Clone(lastKey), '\x00')`
  - etcd-io/etcd@fd2cc937c9: introduced it, "*: implement server-side RangeStream"
blocks-proof: no
---

# etcdserver: keys-only RangeStream appends into mvcc's in-memory index keys

A keys-only `RangeStream` computes the next page's start key by appending a zero byte to the last
key of the page it just read. For a keys-only read that key is mvcc's own index key, so the append
writes into the spare capacity of the index's key array. Two concurrent keys-only streams over the
same keys both write that byte: `go test -race` reports a data race. Both write `0` past the key's
length, so no value read by anyone changes and nothing panics.

**Why not an issue:** fixed upstream (etcd-io/etcd@9acc0ebe37, 2026-10-15, after the commit the fork
`upamanyus/etcd` pins, `d3feef9bcd`, is based on); found by the independent review of the
trust-boundary spec of `rangeStream` (`notes/axiom-review/rangestream.md`, 2026-11-21).

**How:** `server/etcdserver/v3_server.go:246` at the fork's `d3feef9bcd`,
`nextKey = append(resp.Kvs[len(resp.Kvs)-1].Key, '\x00')`; with `KeysOnly` (and the default sort),
mvcc's `treeIndex.Range` returns the index's key slices (`server/storage/mvcc/index.go:177`), which
the keys-only read puts in the response (`kvstore_txn.go`). The race test:
`examples/authmedrangestream/review_test.go`, `TestConcurrentKeysOnly`, run with `-race`.

## Proof

no for the proof as it stands (auth-mediation M3, option (B)): `rangeStream` is names only, and its
trust-boundary spec gives the request's key back without its contents. The race makes the spec's
triple unprovable of the fork's body in GooseLang (racing stores are stuck) for two concurrent
keys-only calls; the fix (upstream's `bytes.Clone`) on the fork removes it, and option (A), proving
`rangeStream`, needs it.
