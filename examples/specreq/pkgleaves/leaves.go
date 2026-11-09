// Requirement snippets for pkg/v3/{pbutil,ioutil,httputil} and the third-party boundaries semver,
// x/time/rate, probing (batch 4b).
package pkgleaves

import (
	"bytes"
	"context"
	"io"
	"net/http"
	"time"

	"github.com/Masterminds/semver/v3"
	"github.com/xiang90/probing"
	"golang.org/x/time/rate"

	"go.etcd.io/etcd/pkg/v3/httputil"
	"go.etcd.io/etcd/pkg/v3/ioutil"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/raft/v3/raftpb"
)

// REQ pbutil/marshal-round-trip: a message marshalled by MustMarshalMessage decodes, by
// MustUnmarshalMessage, to an equal message (rafthttp's encoder and decoder; the apply thread's
// decoding of what the proposer marshalled).
// Users: rafthttp/msg_codec.go:40, pipeline.go:99 (MustMarshalMessage), msgappv2_codec.go
// (MustUnmarshalMessage of an Entry), etcdserver/apply.go:29 (MustUnmarshalMessage).
// Assumes: nothing (a raft message always marshals).
// Specs: PbUtil.MustMarshalMessage.spec, PbUtil.MustUnmarshalMessage.spec; Proto.encodes_fun.
func ReqMarshalRoundTrip(m *raftpb.Message) {
	b := pbutil.MustMarshalMessage(m)
	var m2 raftpb.Message
	pbutil.MustUnmarshalMessage(&m2, b)
	if m2.GetIndex() != m.GetIndex() || m2.GetType() != m.GetType() {
		panic("marshal-round-trip: decoded a different message")
	}
}

// REQ pbutil/apply-decode: a committed entry's data decodes without a panic.
// Users: etcdserver/apply.go:29, server.go (applyConfChange).
// Assumes: data is a ConfChange's encoding (the proposer marshalled it: R1's committedLb).
// Specs: PbUtil.MustUnmarshalMessage.spec.
func ReqApplyDecode(data []byte) uint64 {
	var cc raftpb.ConfChange
	pbutil.MustUnmarshalMessage(&cc, data)
	return cc.GetNodeId()
}

// REQ ioutil/limited-read: a request body read through a limited buffer reader yields the body.
// Users: rafthttp/http.go:121 (pipelineHandler.ServeHTTP, io.ReadAll of the limited reader).
// Assumes: body is a reader of the request's body (Http.readerAt), n >= 0.
// Specs: IoUtil.NewLimitedBufferReader.spec, Http.readerAt_read.
func ReqLimitedRead(body io.Reader, n int) []byte {
	b, err := io.ReadAll(ioutil.NewLimitedBufferReader(body, n))
	if err != nil {
		return nil
	}
	return b
}

// REQ ioutil/reader-and-closer: a reader and a closer joined read as the reader, close as the
// closer.
// Users: rafthttp/snapshot_sender.go:195 (createSnapBody).
// Assumes: rc is a body reader with a closer (Http.readerAt, readerCloser).
// Specs: IoUtil.ReaderAndCloser_reader, ReaderAndCloser_closer.
func ReqReaderAndCloser(head []byte, rc io.ReadCloser) io.ReadCloser {
	return &ioutil.ReaderAndCloser{Reader: io.MultiReader(bytes.NewBuffer(head), rc), Closer: rc}
}

// REQ httputil/graceful-close: a response the caller will not use is drained and closed.
// Users: rafthttp/stream.go:615-675 (streamReader.dial's error paths).
// Assumes: resp is a client response whose body this goroutine owns.
// Specs: HttpUtil.GracefulClose.spec.
func ReqGracefulClose(resp *http.Response) {
	if resp.StatusCode != http.StatusOK {
		httputil.GracefulClose(resp)
	}
}

// REQ semver/parse-compare: etcd's version and a peer's header parse; versions compare by
// precedence.
// Users: rafthttp/util.go:134-175 (compareMajorMinorVersion, serverVersion, checkVersionCompatibility),
// apply/backend.go:272-275 (ClusterVersionSet).
// Assumes: hdr parses (the peer protocol's header knowledge).
// Specs: Semver.MustParse.spec (parse_version), Version.LessThan.spec.
func ReqParseCompare(hdr string) bool {
	lv := semver.MustParse("3.8.0-alpha.0")
	rv := semver.MustParse(hdr)
	if lv.LessThan(lv) {
		panic("parse-compare: a version below itself")
	}
	return rv.LessThan(lv)
}

// REQ semver/major-minor: the major.minor.0 of a version.
// Users: rafthttp/util.go:135-136, stream.go:712, etcdserver/version/downgrade.go:44,59.
// Assumes: v is a version (verAt).
// Specs: Version.Major.spec, Version.Minor.spec, New.spec, Version.LessThan.spec.
func ReqMajorMinor(v *semver.Version) {
	nv := semver.New(v.Major(), v.Minor(), 0, "", "")
	if nv.Major() != v.Major() || nv.Minor() != v.Minor() {
		panic("major-minor: fields lost")
	}
}

// REQ semver/round-trip: a version's String() parses back to it (the stored cluster version).
// Users: membership/cluster.go:586 (MustParse(c.version.String())), schema/membership.go:156,205.
// Assumes: s parses.
// Specs: MustParse.spec, Version.String.spec, NewVersion.spec; law parse_render.
func ReqRoundTrip(s string) {
	v := semver.MustParse(s)
	w, err := semver.NewVersion(v.String())
	if err != nil || v.LessThan(w) || w.LessThan(v) {
		panic("round-trip: String did not parse back")
	}
}

// REQ rate/dial-retry: a stream reader waits on its dial limiter before each dial; an error ends
// the loop.
// Users: rafthttp/peer.go:216,227 (NewLimiter), stream.go:449 (Wait), transport.go:153 (Every).
// Assumes: ctx is a context (ctxOk).
// Specs: Rate.Every.spec, NewLimiter.spec, Limiter.Wait.spec.
func ReqDialRetry(ctx context.Context) {
	rl := rate.NewLimiter(rate.Every(100*time.Millisecond), 1)
	for i := 0; i < 3; i++ {
		if err := rl.Wait(ctx); err != nil {
			return
		}
	}
}

// REQ probing/prober-lifecycle: probers are made, given peers, and emptied; the probing handler is
// registered on the peer mux.
// Users: rafthttp/transport.go:146-147,166,221-222,349-350,385-387; probing_status.go:41-57.
// Assumes: rt is a round tripper.
// Specs: Probing.NewProber.spec (proberOk), NewHandler.spec; Http.ServeMux.Handle.spec.
func ReqProberLifecycle(rt http.RoundTripper, mux *http.ServeMux, id string, us []string) {
	p := probing.NewProber(rt)
	_ = p.AddHTTP(id, time.Second, us)
	_ = p.Remove(id)
	p.RemoveAll()
	mux.Handle("/raft/probing", probing.NewHandler())
}
