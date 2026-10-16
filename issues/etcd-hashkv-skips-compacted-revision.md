---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#18337 issue closed: same finding (closed by its author for lack of bandwidth, not fixed; maintainers tie any change to compaction and hash compatibility across versions)
  - etcd-io/etcd#21284 issue closed: related (range-free compaction proposal, cites #18337)
---

# `HashKV(rev)` skips stored revisions at or below the compaction revision

- **Status**: documentation the code contradicts (or a wrong result, depending on which is
  meant); not a consistency bug between members: every member applies the same filter, so equal
  stores give equal hashes, and the filter is the one the compaction at `rev` applies to the
  hash it stores (which the corruption checks compare with `HashKV`).
- **Where**: at the etcd pin of `etc/goose.py` (`107edf7e4`): `store.hashByRev`
  (`server/storage/mvcc/kvstore.go:167`, `keep := s.kvindex.Keep(rev)` at `:186`),
  `kvHasher.WriteKeyValue` (`server/storage/mvcc/hash.go:60`, the filter at `:72`: a revision
  below `compactRevision + 1` is hashed only if it is in `keep`). Documentation:
  `api/etcdserverpb/rpc.proto:243`, "HashKV computes the hash of all MVCC keys up to a given
  revision", and the API reference generated from it.
- **What happens**: `keep` is the set of revisions a compaction *at `rev`* would keep, not the
  set the compaction *at `compactRevision`* kept. A revision `r ≤ compactRevision` that is still
  stored and readable (the key's latest revision at `compactRevision`) is skipped when the key has
  a later revision `≤ rev`. Reproduction (a test in `server/storage/mvcc`,
  `issues/etcd-hashkv-skips-compacted-revision/hashkv_compacted_revision_test.go`; fails at the pin:
  `HashByRev(7)` is the hash of revisions 6..7, not 5..7, while a read at revision 5 returns
  `"5"`):

  ```go
  func TestHashKVSkipsCompactedRevision(t *testing.T) {
  	b, _ := betesting.NewDefaultTmpBackend(t)
  	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
  	defer cleanup(s, b)
  	put := func(v string) { s.Put([]byte("foo"), []byte(v), lease.NoLease) }
  	del := func() { s.DeleteRange([]byte("foo"), nil) }
  	put("2"); put("3"); del()           // revisions 2, 3, 4 (tombstone)
  	put("5"); put("6"); put("7"); del() // revisions 5, 6, 7, 8 (tombstone)
  	put("9")
  	done, _ := s.Compact(traceutil.TODO(), 5)
  	<-done
  	r, _ := s.Range(t.Context(), []byte("foo"), nil, RangeOptions{Rev: 5})
  	require.Equal(t, "5", string(r.KVs[0].Value)) // revision 5 is stored and readable
  	got, _, _ := s.HashStorage().HashByRev(7)
  	hashOf := func(mains map[int64]bool) uint32 { // kvHasher's encoding, no filter
  		h := crc32.New(crc32.MakeTable(crc32.Castagnoli))
  		h.Write(schema.Key.Name())
  		tx := b.ReadTx(); tx.RLock(); defer tx.RUnlock()
  		tx.UnsafeForEach(schema.Key, func(k, v []byte) error {
  			if mains[BytesToRev(k).Main] { h.Write(k); h.Write(v) }
  			return nil
  		})
  		return h.Sum32()
  	}
  	require.Equal(t, hashOf(map[int64]bool{5: true, 6: true, 7: true}), got.Hash) // fails:
  	// got.Hash == hashOf(map[int64]bool{6: true, 7: true})
  }
  ```
- **Expected**: per the documentation, every stored MVCC revision `≤ rev`, revision 5 included.
- **How the proof handles it**: outside the verified code. `hash.go` is translated names-only
  (`Code/go_etcd_io/etcd/server/v3/storage/mvcc.toml`: "restore, compaction, hashing is names
  only", bar `NewHashStorage`); the hasher is an axiom whose result is any value
  (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/kvHasher__Hash.lean`, `newKVHasher.lean`,
  `kvHasher__WriteKeyValue.lean`; `hashStorage__Store.lean`: "the stored hashes are not
  modelled"); `store.hashByRev` and `hashStorage.HashByRev` are not translated.
- **Possible fixes**: document what is hashed ("the revisions in `(compactRevision, rev]` and,
  at or below the compaction revision, those a compaction at `rev` would keep"), which is what
  the corruption check needs; or hash with the keep set of the compaction revision, which changes
  hash values and needs the cluster-version gating the maintainers asked for in #18337.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#18337 (`notes/bug-triage/etcd-18337.md`);
  reproduced at the pin.
