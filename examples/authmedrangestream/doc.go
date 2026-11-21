// Package authmedrangestream tests, against the real Go code at the etcd pin, the claims of the
// trust-boundary spec of `(*EtcdServer).rangeStream` (Spec/go_etcd_io/etcd/server/v3/etcdserver/
// EtcdServer__rangeStream.lean; auth-mediation M3, option (B), 2026-11-21): it sends only through
// the stream it is given; every chunk is a fresh `RangeStreamResponse` whose `RangeResponse` is not
// nil and holds key-values of the request's range only (as the auth store reads a range: the key
// alone for a nil range end, every key from the key for an empty or "\x00" one, [key, end)
// otherwise); only the last chunk has a header; the chunks' key-values are not written after they
// were sent (the next page's key is a copy of the last key with a 0 appended); the request's fields but
// Key, Limit and Revision are unchanged; and an error a Send returns is the error returned
// (rangestream_test.go, the author's). review_test.go is the independent review's
// (notes/axiom-review/rangestream.md): errors after a compaction or a cancel between pages, writes
// during a stream, the keys-only aliasing and its data race (run with -race; fixed on the fork since
// 4416a5786). No proof; not translated.
package authmedrangestream
