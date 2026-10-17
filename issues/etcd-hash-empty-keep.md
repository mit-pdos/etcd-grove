---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22517 issue open: same root cause (symptom 2: HashKV depends on how far a compaction has gone when nothing is kept)
  - etcd-io/etcd#22515 pr open: fix for #22517 only (filters by Keep(compactRev) when Keep(rev) is empty); keeps the finished-compaction hash of older versions; does not fix symptom 1 (reproduced)
  - etcd-io/etcd#21202 pr open: not a fix; its `etcdutl hashkv --compact-rev` makes symptom 1 reachable between snapshots (an uncompacted snapshot hashed with `--compact-rev C` and one compacted at `C` disagree when nothing is live at the hashed revision; reproduced); notes/pr-verify/etcd-21202.md
  - etcd-io/etcd#22562 pr open: fixes both symptoms (drops `len(h.keep) > 0`); changes the hash older versions return after a finished compaction when Keep(rev) is empty (reproduced with #22515's test); notes/pr-verify/etcd-22562.md
---

# server/storage/mvcc: with an empty kept set, the hasher filters nothing, so the two hashes of a revision disagree

- **Status**: a bug (a wrong result: two computations of the same `(Revision, CompactRevision)`
  hash differ; etcd's corruption checks compare them across members).
- **Where**: `server/storage/mvcc` at 09669450f (`etc/goose.py`'s etcd pin).
  `kvHasher.WriteKeyValue` (`hash.go:60-90`) skips a revision at or below the compaction revision
  that the kept set does not keep, but only `&& len(h.keep) > 0` (line 72: "don't skip if there
  isn't one", a leftover from when `keep` was the store's saved compaction set, nil when no
  compaction was in progress). The kept set is never "no compaction" any more:
  `store.hashByRev` (`kvstore.go:167-195`, `HashKV`) passes `kvindex.Keep(rev)` (line 186), and the
  compaction job (`kvstore_compaction.go:28`) passes `kvindex.Compact(rev)` (line 35) with the
  previous compaction revision (line 48); `hashStorage.Store` keeps the job's hash and
  `HashByRev(rev)` returns it. `Keep(rev)` is empty when no key is live at `rev`; `Compact(rev)`
  also keeps a tombstone at `rev` ending a generation (the asymmetry `keyIndex.keep` documents),
  so it can be non-empty when `Keep(rev)` is empty.
- **What happens**:
  1. *`HashKV` and the compaction's stored hash differ.* A key put at 2, the store compacted at 2,
     the key deleted at 3: `HashKV(3)` (compaction revision 2) hashes the put at 2 (`Keep(3)` is
     empty: nothing filtered); the compaction at 3 (`Compact(3)` keeps the tombstone) skips it and
     stores a hash with the same `Revision` 3 and `CompactRevision` 2. `CompactHashCheck`
     (`etcdserver/corrupt.go:277`) compares the leader's stored hash with a peer's `HashKV` at the
     same revision when the compact revisions match (line 315): a follower that has not applied
     the compaction at 3 yet answers with the computed hash, a mismatch. Reproduction:
     `notes/pr-verify/etcd-22562/hash_empty_keep_test.go` (`TestHashByRevEmptyKeepMatchesCompactionHash`,
     fails at the pin, passes with #22562, fails with #22515); also the seed
     `[0 0 128 0 64 128 64]` of #22562's `FuzzCompactionHash`
     (`notes/pr-verify/etcd-22562/hash_fuzz_22562_test.go`).
  2. *`HashKV` depends on how far a compaction has gone* (#22517): with `Keep(rev)` empty, the
     revisions at or below the compaction revision that the running compaction has not deleted
     yet are hashed, so a member still compacting and one done answer differently
     (#22515's `TestHashByRevAcrossPhysicalCompaction`, copied as
     `notes/pr-verify/etcd-22562/hash_physical_compaction_22515_test.go`: its two cases with
     nothing kept fail at the pin, "hash during the compaction").
- **Expected**: the hash of a revision with a given compaction revision is a function of the
  key-value history, whichever way it is computed and however far compaction has gone (the
  `HashStorage` comment: "the hash of all MVCC revisions up to a given revision").
- **How the proof handles it**: the hasher (`kvHasher`, crc32) is at the trust boundary with an
  opaque spec (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/kvHasher__WriteKeyValue.lean`), so no
  result on `lean` says what is hashed. On branch `pr-verify/etcd-22562` the filter is proved
  (`kvHashIncludes`) and `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/HashFilter.lean` states both
  properties: `hashIncl_keep_compact` (the two kept sets give the same filter, #22562's filter),
  `hashIncl_not_del` (nothing compaction may delete is hashed, under `NoDelPutAt`, the premise of
  `issues/etcd-compaction-delete-then-put.md`), and `hashInclOld_keep_compact_differ` (the filter
  at the pin violates the first, the case above). On branch `pr-verify/etcd-22515` the same file
  states #22515's filter (`kvHashIncludes` with `exactKeep`, `hashByRevKeep`, both proved):
  `hashIncl22515_not_del` (symptom 2 fixed, same premise), `hashIncl22515_compat` (the hash after
  a finished compaction is the pin's) and `hashIncl22515_keep_compact_differ` (symptom 1 remains).
- **Possible fixes**: #22562 (drop the `len(h.keep) > 0` guard) fixes both, but changes the hash
  that versions before it return after a finished compaction whenever `Keep(rev)` is empty and a
  revision at or below the compaction revision is stored (a key live at the compaction revision,
  deleted after it, i.e. a nearly empty keyspace): in a mixed-version cluster `HashKV` then
  differs on identical data (#22515's case "every key deleted after the compact revision" fails
  on #22562), which the opt-in corruption checks report: `PeriodicCheck` (`--corrupt-check-time`,
  default off) raises `CORRUPT`, `InitialCheck` (gate `InitialCorruptCheck`, default off) keeps a
  restarted member from starting, `CompactHashCheck` (gate `CompactHashCheck`, alpha) only when
  `Compact(rev)` is empty too. #22515 keeps that hash but
  leaves symptom 1. Symptom 1 cannot be fixed without changing some value older versions compute
  (at the pin, `HashKV` and the stored hash already disagree there); which one to change is the
  maintainers' call. One option (untested): change only the compaction job's stored hash to
  `HashKV`'s, with #22515's progress fix, which confines the change to `CompactHashCheck`.
- **Found**: 2026-10-16, verifying etcd-io/etcd#22562 (`notes/pr-verify/etcd-22562.md`).
- **Also** (2026-10-17, verifying etcd-io/etcd#21202, `notes/pr-verify/etcd-21202.md`): #21202
  adds `etcdutl hashkv --compact-rev C` (`HashByRevWithCompactRev(rev, C)`) to compare snapshots
  in different compaction states. With an empty `Keep(rev)` the filter skips nothing, so on a
  snapshot not compacted at `C` it hashes every stored revision at or below `C`, while a snapshot
  compacted at `C` has only the kept ones left: identical histories, different hashes
  (`notes/pr-verify/etcd-21202/hash_compactrev_21202_test.go`,
  `TestHashByRevWithCompactRevEmptyKeepDisagrees`: every key deleted at the hashed revision;
  `0xfeac4025` vs `0x734032ba`). With a key live at the hashed revision the two agree
  (`TestHashByRevWithCompactRevAtStoreCompactionAgrees`). #22562's filter would make them agree.
