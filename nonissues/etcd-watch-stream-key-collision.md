---
upstream: none
checked: 2026-11-02
links:
blocks-proof: no
---

# clientv3: watches whose contexts carry different gRPC metadata can share one watch stream, and go out with the first one's metadata

The client shares a gRPC watch stream between watches whose contexts' outgoing metadata print
alike under `fmt.Sprintf("%+v", md)` (`streamKeyFromCtx`, `client/v3/watch.go`), and the stream is
opened (and reopened on reconnect) with the first such context. `%+v` is not injective: a value
list `{"a b"}` and `{"a", "b"}` print alike, and so do `{""}` and `{}` (an
`AppendToOutgoingContext(ctx, "k", "")` and a literal `metadata.MD{"k": {}}`). A watch made under
the second context is then created with the first one's metadata (its token, `require-leader`,
...).

**Why not an issue:** not reached with etcd's own metadata: tokens and `hasleader` hold no spaces
or brackets, and the client never builds empty value lists. It needs application metadata on the
watch context with such values, and the test checks only the key (a copy of `streamKeyFromCtx`'s
body), not a watch.

## Proof

no: the client spec states a watch's check over the metadata of the stream it joins, not its own
context's, with the key's laws saying which metadata share a stream
(`Proof/go_etcd_io/etcd/client/v3/StreamKey.lean`).

## Notes

The key test (go1.27, `fmt` and grpc `metadata` only):

```go
func key(ctx context.Context) string {
	if md, ok := metadata.FromOutgoingContext(ctx); ok {
		return fmt.Sprintf("%+v", md)
	}
	return ""
}

func TestEmptyValue(t *testing.T) {
	bg := context.Background()
	c1 := metadata.AppendToOutgoingContext(bg, "k", "")       // {k:[""]}
	c2 := metadata.NewOutgoingContext(bg, metadata.MD{"k": {}}) // {k:[]}
	if key(c1) != key(c2) {
		t.Fatalf("keys differ") // never: both are "map[k:[]]"
	}
}
```

Found by the `axiom` review of the key's laws (`notes/axiom-review/g2-streamkey.md`). A fix: key
the streams by an injective encoding of the metadata (sorted keys, each value quoted), or compare
the metadata itself.
