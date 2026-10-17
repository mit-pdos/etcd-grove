---
upstream: unchecked
checked: 2026-10-17
links: []
---

# server/storage/mvcc: `HashByRev` (`HashKV`) accepts a negative revision and hashes nothing

- **Status**: an unstated precondition (or a missing input check): a negative revision is not
  refused; the result is a hash of no revision, which no member state corresponds to. Minor: the
  corruption checks never pass one; only a client's `HashKV` request can.
- **Where**: `server/storage/mvcc/kvstore.go:167-195` (`store.hashByRev`) at 09669450f
  (`etc/goose.py`'s etcd pin): the checks are `rev > 0 && rev < compactRev` (`ErrCompacted`) and
  `rev > 0 && rev > currentRev` (`ErrFutureRev`), and `rev == 0` means the current revision; a
  negative `rev` passes all three and goes to `kvindex.Keep(rev)` and the hasher, whose upper
  bound `Revision{Main: rev + 1}` (`hash.go:62`) excludes every stored revision. The gRPC
  `Maintenance.HashKV` (`server/etcdserver/api/v3rpc/maintenance.go:242`) passes
  `r.Revision` through unchecked. The API documents `revision` as "the key-value store revision
  for the hash operation".
- **What happens**: `HashByRev(-5)` on a store at revision 10 returns
  `{Hash: 1084519789, CompactRevision: -1, Revision: -5}`, no error (1084519789 is the hash of
  nothing; the same as `HashByRev(1)`). Reproduction: `notes/pr-verify/etcd-21202/hash_negative_rev_test.go`
  (`TestHashByRevNegativeRevision`, fails at the pin; log `hash_negative_rev.log` there).
- **Expected**: an error for a revision that is not a store revision (as `ErrFutureRev` for one
  above the current revision), or the documented meaning of a negative value.
- **How the proof handles it**: the specs of the hash's functions on branch
  `pr-verify/etcd-21202` (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/store__prepareHashParams.lean`,
  `store__hashByRev.lean`, `store__hashByRevWithCompactRev.lean`) take `0 ≤ rev` as a premise
  (`treeIndex.Keep`'s spec needs it). The same holds after etcd-io/etcd#21202, whose
  `prepareHashParams` keeps these checks.
- **Possible fixes**: reject `rev < 0` in `hashByRev` (or in `HashKV`) with an invalid-argument
  error.
- **Found**: 2026-10-17, verifying etcd-io/etcd#21202 (`notes/pr-verify/etcd-21202.md`).
