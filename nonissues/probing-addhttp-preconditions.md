---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# probing: `Prober.AddHTTP` panics on a non-positive interval, an empty URL list or an unparsable URL

`github.com/xiang90/probing`'s `(*prober).AddHTTP(id, probingInterval, endpoints)` (`prober.go:41-90`
at `a49e3df8f510`) has preconditions its documentation does not state:

- `time.NewTicker(probingInterval)` panics, synchronously, if the interval is not positive;
- the probing goroutine indexes `endpoints[pinned]` and computes `(pinned + 1) % len(endpoints)`: an
  empty list is an index-out-of-range (or a division by zero) panic in that goroutine, which kills
  the process;
- it builds each probe with `http.NewRequest("GET", endpoints[pinned], nil)` and `panic(err)`s on an
  error: a URL `url.Parse` rejects kills the process;
- the goroutine keeps reading the `endpoints` slice while the target lives, so the caller must not
  write it afterwards.

**Why not an issue:** a library precondition etcd meets. rafthttp's `addPeerToProber`
(`server/etcdserver/api/rafthttp/probing_status.go:41-57`) passes `proberInterval` (4 s), and the
peer's URLs from `Transport.AddPeer`, which first parses them (`types.NewURLs`, panicking on a bad
one, `transport.go:305-310`; a peer always has at least one URL), each followed by `/raft/probing`
(a parsed URL with a path appended parses); the slice is a fresh local never written again.

## Proof

no: the assumed `Probing.proberOk` bundle (`Spec/github_com/xiang90/probing/Api.lean`) takes the
preconditions as `AddHTTP`'s premises (`0 < interval`, a non-empty read-only-for-good list, every URL
`urlParses`), which rafthttp's `addPeerToProber` discharges.

## Notes

Found by code reading in batch 4b's review, round 1 (F7, `notes/specs-only/reviews/4b-review-1.md`),
2026-11-09. No test written.
