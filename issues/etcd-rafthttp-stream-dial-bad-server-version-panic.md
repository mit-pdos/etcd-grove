---
upstream: unchecked
checked: 2026-10-23
links: []
---

# rafthttp: a peer's malformed `X-Server-Version` panics the dialing member

**Status**: a reachable panic (a robustness bug): a response to a stream dial whose
`X-Server-Version` header does not parse as a semantic version crashes the member that dialed.
Between etcd members the header is always `version.Version`, so only a non-etcd (or misbehaving)
server at a peer URL, or a proxy rewriting the header, reaches it.

**Where** (`upamanyus/etcd` `188113160d`, upstream's code unchanged):
`server/etcdserver/api/rafthttp/stream.go:612`, `streamReader.dial`:
`rv := serverVersion(resp.Header)`; `util.go:148-155`, `serverVersion` returns
`semver.MustParse(verStr)`, which panics on a string that does not parse. `dial` runs on the
stream reader's goroutine (`streamReader.run`, started by `start`), outside any HTTP handler, so
nothing recovers the panic and the process exits. (The server side's
`checkClusterCompatibilityFromHeader` calls `serverVersion` on a *request's* headers too, but in
a handler, whose panic `net/http`'s server recovers: the connection is dropped, the member stays up.)

**What happens**: a test in package `rafthttp` (as `TestStreamReaderDialHttpError`, whose
`respRoundTripper` it uses), passing at the pinned revision:

```go
func TestStreamReaderDialBadServerVersion(t *testing.T) {
	h := http.Header{}
	h.Add("X-Server-Version", "not-a-version")
	sr := &streamReader{
		peerID: types.ID(2),
		tr:     &Transport{streamRt: &respRoundTripper{code: http.StatusOK, header: h}, ClusterID: types.ID(1)},
		picker: mustNewURLPicker(t, []string{"http://localhost:2380"}),
		errorc: make(chan error, 1),
		ctx:    t.Context(),
	}
	defer func() {
		if r := recover(); r != nil {
			t.Logf("dial panicked: %v", r) // "invalid semantic version"
		} else {
			t.Errorf("dial did not panic")
		}
	}()
	sr.dial(streamTypeMessage)
}
```

**Expected**: a peer's bad response is a failed dial (`dial` already returns errors for bad
statuses, unsupported stream types and unparsable precondition bodies), not a crash.

**How the proof handles it**: the HTTP boundary's protocol constrains the headers a handler
commits (`rhdr`, `Proof/net/http/Boundary.lean`, rafthttp stage 5e); a raft member's
(`raftProto`'s `verHdrOk`) has `X-Server-Version` unset or a version that parses, which the stream
handler's proof establishes (it sets `version.Version`, `"3.8.0-alpha.0"`). `dial`'s proof (stage
5e-3) reads the header through `RoundTrip`'s view of the committed headers, so `serverVersion`'s
`MustParse` does not panic: the proof excludes the panic for peers that are members of the
program, and the bug stays reachable from anything else at a peer URL.

**Possible fixes**: parse with `semver.NewVersion` in `serverVersion` (and `minClusterVersion`),
returning an error that `dial` turns into a failed dial (`cr.picker.unreachable(u)`), or treat an
unparsable header as `2.0.0`, as an absent one.

**Found**: 2026-10-23, scoping rafthttp stage 5 (the stream reader's `dial`), while stating what
the client side of the HTTP boundary knows of a response's headers.
