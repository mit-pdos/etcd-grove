# Requirements on `go.etcd.io/etcd/client/pkg/v3/types` (batch 1c)

## from 2f

Provisional in `Rafthttp`'s `Api.lean`:
- **`urlsHosts us`** (pure): `types.NewURLs(us)` succeeds exactly when it is `some hs`, `hs` the parsed
  URLs' hosts, non-empty (`NewURLs` refuses an empty list); the URLs are sorted (order irrelevant to
  rafthttp).
- **`urlsAt sl hs`** (persistent): a `types.URLs` slice (from `NewURLs`) of URLs with hosts `hs`,
  read-only, each with `Http.urlOk` (its `String()` parses back: `NewRequest` accepts it).
- `ID.String()` (lowercase hex, never fails) and `IDFromString(s)` (an error, or the id whose
  `String` is `s`).
```go
urls, err := types.NewURLs(us)   // transport.go:282, 305, 378 (Logger.Panic on err)
```
Used by: `Transport.AddPeer.spec`, `AddRemote`, `UpdatePeer`, `startPeer`, `newURLPicker`,
`streamHandler.ServeHTTP` (`IDFromString` of the path), `addRemoteFromRequest`.

### from 2f, round 1

- **No comma in a peer URL string**: `types.NewURLs` accepts `http://a,b:2380` (url.Parse and
  SplitHostPort succeed), but rafthttp's receiver splits `X-PeerURLs` on `","` (`util.go:202`,
  `http.go:423`), so `AddRemote` of the pieces panics (recovered by `Serve`). 2f's `trCfg` takes
  `urlsNoComma sl` (provisional) of the local URLs. Please give it from the membership's URLs, or
  as a fact of `urlsAt` (`nonissues/etcd-rafthttp-peerurl-comma-split.md`).
