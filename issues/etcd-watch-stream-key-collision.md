---
upstream: unchecked
checked: 2026-10-29
links:
---

# A watch can go out with another context's metadata: the stream key collides

**Status**: a bug (wrong result), low impact: two watch contexts with different outgoing gRPC
metadata can share one gRPC watch stream, so the second watch is sent, authenticated and resumed
with the first context's metadata (its token, its `require-leader`, ...).

**Where**: `client/v3/watch.go` at the pin (`etc/goose.py`, project `etcd`): `streamKeyFromCtx`
(l. 1102-1107) keys the client's watch streams by `fmt.Sprintf("%+v", map[string][]string(md))` of
the context's outgoing metadata; `(*watcher).Watch` reuses the stream of an equal key
(l. 281-289), opened with the first such context (`newWatcherGRPCStream`, kept for reconnects,
l. 330-347, 1069).

**What happens**: `%+v` of a `map[string][]string` prints each value list joined by spaces, so
distinct metadata print alike. Checked with go1.27 (`fmt` only):

```go
a := map[string][]string{"token": {"a b"}}
b := map[string][]string{"token": {"a", "b"}}
fmt.Sprintf("%+v", a) == fmt.Sprintf("%+v", b) // true: both "map[token:[a b]]"
```

A watch whose context carries `b`'s metadata, made after one carrying `a`'s on the same client,
joins `a`'s stream and is created with `a`'s metadata: the server checks its permission for `a`'s
principal. A value with a space (or keys and values containing `:`, `[`, `]`) is needed; etcd's own
tokens contain none, so with etcd's credentials alone it is not reached. Or an empty value: `%v`
prints `[]string{}` (and `nil`) and `[]string{""}` alike, so `{"k": {}}` (a literal `MD` given to
`NewOutgoingContext`) and `AppendToOutgoingContext(ctx, "k", "")` both key as `map[k:[]]`, no space
needed (found by the `axiom` review of the key's laws, `notes/axiom-review/g2-streamkey.md`,
2026-10-30; `examples/axiomcx/g2streamkey`, `TestEmptyValue`).

**Expected**: a watch is sent with its own context's metadata (`WithRequireLeader` and per-call
tokens are documented per context).

**How the proof handles it**: found designing authkv's watch with auth on (G2,
`notes/authkv-main-plan.md`): the client spec states a watch's check over the metadata of the
stream it joined (a context whose key equals the watch's), not the watch context's own; the key's
model (`streamKeyFromCtx`'s spec) says which metadata share one.

**Possible fixes**: key the streams by an injective encoding of the metadata (sorted keys, each
value list quoted, e.g. `fmt.Sprintf("%q", …)` over sorted pairs), or compare the metadata itself.

**Found**: 2026-10-29, by the spec review of authkv's G2 watch design (reading `watch.go`).
