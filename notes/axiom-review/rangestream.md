# Axiom review: `EtcdServer.rangeStream.wp_proof` (auth-mediation M3, option B)

- Axiom: `axiom EtcdServer.rangeStream.wp_proof : EtcdServer.rangeStream.spec`, spec in
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__rangeStream.lean` (uncommitted, worktree
  `/shared/etcd-grove-authm3`, branch `auth-mediation-m3`, as of 2026-11-21, **including the revised
  store-error case** `⌜err ≠ nil⌝ ∗ applyErrIs err ∗ rangeReadErr err`); vocabulary
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/RangeStreamDefs.lean` (`rangeRequestOwn`,
  `rangeChunkIs`, `rangeSendOk`, `rangeReadErr`; `rangeStreamCtx` is not used by the axiom).
- Go code: fork `upamanyus/etcd` at `d3feef9bcd` (the pin of `examples/go.mod`),
  `server/etcdserver/v3_server.go:198-274` (`rangeStream`, `adjustChunkLimit`),
  `server/etcdserver/txn/range.go`, `server/storage/mvcc/{kvstore_txn.go,index.go}`. The code came in
  with `fd2cc937c9` ("*: implement server-side RangeStream").
- Toolchain: go1.27.3. The tests are in a scratch module that copies `examples/go.mod` (same pins):
  `/shared/tmp/authm3/attack/mod/rs/` (`attack_test.go`, mine, kept as
  `examples/authmedrangestream/review_test.go`; `base_test.go`, a copy of
  `examples/authmedrangestream/rangestream_test.go`).

## Verdict: survives, with one finding to fix in the statement (a Go data race)

I found no Go program that panics, and no false conclusion, that follows from the axiom. But one
part of the post is false in the model, and the Go code behind it races:

**Finding F1. The returned request key shares memory that concurrent calls write.** With `KeysOnly`
(and a sort target other than VALUE, `FastKeysOnly`), mvcc's `treeIndex.Range` returns the index's
own key slices (`index.go:177`, `keys = append(keys, ki.key)`; `kvstore_txn.go` FastKeysOnly branch:
`Key: keys[i]`). So the chunk's `kv.Key` **is** mvcc's `keyIndex.key`. Then `v3_server.go:246`,
`nextKey = append(resp.Kvs[len(resp.Kvs)-1].Key, '\x00')`, writes into the spare capacity of that
index key's array. The protobuf-go v2 unmarshal of the put rounds the capacity up to a size class,
so the capacity is usually there. Then `r.Key = nextKey`.
- In Go: two concurrent keys-only `RangeStream`s over the same range both write that byte.
  `go test -race` reports it (`TestConcurrentKeysOnly`: `WARNING: DATA RACE` write at
  `v3_server.go:246` / previous write at `v3_server.go:246`, two `RangeStream` goroutines). Both
  write `0`, so the race causes no panic and no wrong value: it is not a counterexample under the
  skill's rules ("not a data race the detector reports without a crash").
- In the spec: the post gives `∃ o', rangeRequestOwn r o'`, which includes `ksl' ↦*□ k'` of the final
  `r.Key`. Its last cell is that byte of mvcc's index-key array, which another call (holding its own
  `mvccReaders γ 1`; the tokens are counted, so concurrent calls are allowed) writes non-atomically.
  In GooseLang a non-atomic store that races another access is stuck (`Perennial/GooseLang/Lang.lean`,
  the `NonAtomic` heap). So the claim cannot be proved of the real body. The planned replacement,
  option (A) (a proof over a restated `txn.Range.spec`), would get stuck exactly here. No caller can
  exploit it today: only `0` is ever written there, and no spec grants the slice's capacity.
  `TestKeysOnlyAliasing` confirms the sharing: the final `req.Key` (`"k0049\x00"`) shares its array
  with a chunk's key, and two streams' chunks share all 60 key slices (the index's).
- Proposed restatement (not applied): do not give the request's key contents back persistently. Use
  a post with just the field points-tos (`∃ ksl, Key ↦ ksl`, plus `Limit`/`Revision` owned and the
  read-only rest), not `rangeRequestOwn r o'`. After `rangeStream` returns, `RangeStream` does not
  read `r.Key` again (the span attributes and trace fields read it before `doSerialize`). If a caller
  needs the contents, the fix is in Go: `nextKey = append(lastKey[:len(lastKey):len(lastKey)], 0)`
  (or `bytes.Clone`). With that fix the race is gone and the claim would hold.
- **Candidate issue in the verified code** (CLAUDE.md, "Issues in the verified code"; I did not
  write the file, because the brief allows no writes outside `examples/axiomcx/rangestream/`):
  "RangeStream with keys_only appends into mvcc's in-memory index keys (data race between concurrent
  streams; an in-process client that appends to a keys-only result's `kv.Key` can change an in-flight
  stream's next start key)". It probably belongs in `issues/`: the `-race` test fails at the pin
  through the public `EtcdServer.RangeStream`, and etcd's CI runs with `-race`. Check whether
  upstream `main` still has `fd2cc937c9`'s code. `blocks-proof:` yes for option (A), no for (B).

## Attacks tried, and why each failed

| # | Claim attacked | Attack | Result / why it fails |
|---|---|---|---|
| 1 | Keys in `auth.inRange o.key o.base.rangeEnd` | Range-end forms nil / non-nil empty / `"\x00"` / other; keys with `0x00`, `0x01`, `0x7f`, `0xfe`, `0xff`; limits `-1,0,1,2,3,7,10,11,25,1000`; serializable or not; keys-only; count-only; pinned past revisions; Send failures (author's test, 3000 random streams, 6937 chunks, 650 multi-chunk: passes, rerun by me) | Holds. `rangeEndOf` matches mvcc: nil → `Revisions`/`Range` `end == nil` single key (`index.go:116,145,166`); non-nil empty → `unsafeVisit`'s `len(endi.key) > 0` test is false, so open-ended (`index.go:99`); `"\x00"` → `mkGteRange` → `[]byte{}` (`txn/delete.go:63`), open-ended. Later pages start at `append(last,0)` ≥ previous key ≥ `o.key`, and `RangeEnd` is never written. |
| 2 | Same, with sort / revision filters (the axiom does not exclude them; v3rpc's `checkRangeStreamRequest` does, `key.go:169-176`) | Reasoned: `rangeLimit` sets 0 (`range.go:85`), mvcc returns everything, `asembleRangeResponse` truncates and sets `More` | Keys stay in `[nextKey, end) ⊆ o`'s range. With DESCEND the stream can repeat pages until `count == totalLimit` (non-termination for `Limit = 0`), which is not a panic and not a false conclusion of a partial-correctness triple. |
| 3 | `resp.Kvs[len-1]` in bounds | Limits ≤ 0, 1, huge; `adjustChunkLimit` overflow | `More` only if `r.Limit > 0 && len > r.Limit` (`range.go:150`), so `len ≥ 1` after truncation. A negative `Limit` gives `totalLimit < 0`, `r.Limit = totalLimit`, `More = false`, done. Not done implies `count < totalLimit`, so the next `r.Limit ≥ 1`. `lastLimit *= 2` overflows only past 2^62 keys; even then a negative `Limit` means unlimited and `More = false`. Overflow of `targetSize*2` or `/2` only picks a branch. No division. |
| 4 | Store errors are `applyErrIs ∗ rangeReadErr` (the revised case) | Compaction between pages (`TestCompactMidStream`), context cancelled between pages (`TestCancelMidStream`), future revision with and without count-only (`TestFutureRev`) | Errors observed: `err == mvcc.ErrCompacted` (the global's value), `"rangeKeys: context cancelled: context canceled"` with `errors.Is(err, context.Canceled)`, `err == mvcc.ErrFutureRev`, with no chunk sent. These are `txn.rangeResult`'s error cases (`InvRange.lean:66`), which `rangeReadErr` restates. `txn.Count` is a count-only `Range` (`range.go:34`), so it can only give FutureRev or Compacted. Keys-only and count-only reads never check the context (the stream finished with `nil` after the cancel). `applyErrIs` of each case comes from existing lemmas (`applyErrIs_ctxErrorf`, `applyErrIs_of_isCtxErr`, the read path's mvcc error vars). |
| 5 | Send error returned unchanged, `Ξ resp err` | Fail the n-th Send (author's test); typed-nil errors (reasoned) | It returns exactly Send's error, with no further Send (`v3_server.go:262-264`, and the count-only `return rs.Send(...)`). A nil Send result leads to the nil case or to the next page. A typed nil is `!= nil` and is returned with `Ξ`. `Ξ resp err` is given only for a resp that was really passed to Send. |
| 6 | Chunk fields `↦□`, header nil or fresh with owned ids | Deep copies at Send compared after the stream (author's test); writes and deletes during a stream (`TestWritesMidStream`); later puts of the same keys and a second stream (`TestKeysOnlyAliasing`) | `out` and the `RangeStreamResponse` are fresh, `out.Header` is set once before Send (`:252-256`), and nothing writes them after Send. `proto.Size(resp)` (`:271`) writes only the `sizeCache` of `resp` and its KeyValues, which `kvIs` does not claim. Chunk key bytes `[0,len)` were never changed (for keys-only they are mvcc's immutable index keys). Values come from `proto.Unmarshal` (a copy), or `Value = nil` set inside `txn.Range` before the chunk exists. |
| 7 | Request ownership in and out | Aliasing between the request and the chunks | Only `Key`/`Limit`/`Revision` are written (author's test checks the rest). With a nil end and keys-only, the chunk's `kv.Key` is `r.Key`'s own slice (`index.go:171`, `[][]byte{key}`). Both are `↦*□`, which is consistent. The post's key contents: F1. |
| 8 | Precondition sufficient | Lock slots, logger, trace | Its locks are `s.Logger()`'s `lgMu` read slot (`srvLgReader`) and the store's read txn (`mvccReaders γ 1`), once per call, given back. The trace comes from `ctxTraceIs ctx (some t)` (`EnsureTrace` returns `t`). `s.Cfg.MaxRequestBytes` and `s.KV()` are server facts. |
| 9 | Cross-world pattern | Looked for entailments or laws with a pure conclusion about an opaque function of a pointer | The axiom is one triple, and its new definitions state no such law. `rangeReadErr` and `rangeKeysErr` are post facts (per run). `rangeKeysErr`'s `errDesc` conjunct is existing vocabulary shared with the proved `txn.Range.spec`: not new here, not attacked. |

## Not tried

- A Lean proof of anything: there is no counterexample, and the brief excludes builds.
- Proposal-side interleavings beyond writes and compaction during a stream (defrag, snapshot restore
  of the backend between pages). The pages read through `mvccReaders`/`kv.Read`, and restore swaps the
  store under `s.KV()`, which I did not exercise.
- Whether a caller can actually build `Ψ` from `rangeChunkIs` for `headerFillingRangeStream.Send`
  (a usability question, not soundness). Its spec takes `Header ↦□ h` plus `hdrW h`, which `respHdrOwn`
  should give, but I did not check that.
- Whether upstream `main` still has the race (for the candidate issue).

## Resolution (the author, 2026-11-21)

F1 applied as proposed: the post gives the request back as `rangeRequestBack r` (the three fields owned, no
key contents); the race recorded in `nonissues/etcd-rangestream-keysonly-index-key-race.md` (fixed upstream by
etcd-io/etcd@9acc0ebe37); the remaining concern (the triple is not provable of the fork's body for two concurrent
keys-only calls) reported to etcd-grove-03 with the option of carrying upstream's fix on the fork.
