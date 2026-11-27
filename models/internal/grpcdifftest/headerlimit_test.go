package grpcdifftest_test

// Header lists over the receiver's limit (models/grpc/model_wire.go, the MODEL: note on
// headerListTooLarge; finding F1 of notes/phase7-plan.md, section 0a). grpc-go v1.84.0's receivers
// refuse a header list over 16 MiB (x/net/http2's count: name, value and 32 per field) in one of
// several ways, by where the limit falls in the HTTP/2 frames (measured here, against grpc-go):
//
//	client metadata just over the limit:  Internal "stream terminated by RST_STREAM with error code: FRAME_SIZE_ERROR"
//	a metadata value over the limit:      Unavailable "error reading from server: EOF" (or, by timing,
//	                                      the server's RST as a read's "connection reset by peer" or a
//	                                      write's "broken pipe": headRefused)
//	a server header or trailer over it:   Unavailable "error reading from server: connection error: COMPRESSION_ERROR"
//
// and never runs the handler of a call whose head is refused. The model, which writes no block
// over the limit, has these outcomes as choices; in Go it takes the second and the third.

import (
	"io"
	"strconv"
	"strings"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"

	"models.lab/internal/grpcdifftest/svc"
)

const headerLimit = 16 << 20

func TestHeaderListLimit(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)

	// under the limit: the call goes through
	id := fresh()
	ctx := metadata.AppendToOutgoingContext(ctx5(t), "big", strings.Repeat("v", headerLimit-4096))
	if r, err := c.Unary(ctx, svc.M(id+" echo x")); err != nil || r.GetValue() != "x" {
		t.Fatal(r, err)
	}
	if got := len(srv.Seen(id).MD.Get("big")[0]); got != headerLimit-4096 {
		t.Fatalf("handler saw %d bytes", got)
	}

	// the outgoing metadata just over the limit: refused, the handler never runs
	id = fresh()
	ctx = metadata.AppendToOutgoingContext(ctx5(t), "big", strings.Repeat("v", headerLimit-200))
	_, err := c.Unary(ctx, svc.M(id+" echo x"))
	if m := status.Convert(err).Message(); !(status.Code(err) == codes.Internal &&
		m == "stream terminated by RST_STREAM with error code: FRAME_SIZE_ERROR" || headRefused(err)) {
		t.Fatalf("just over the limit: %v", err)
	}
	if srv.Runs(id) != 0 {
		t.Fatalf("runs %d", srv.Runs(id))
	}

	// a metadata value over the limit
	for _, n := range []int{headerLimit + 10, 64 << 20} {
		id = fresh()
		ctx = metadata.AppendToOutgoingContext(ctx5(t), "big", strings.Repeat("v", n))
		_, err = c.Unary(ctx, svc.M(id+" echo x"))
		if !headRefused(err) {
			t.Fatalf("over the limit: %v", err)
		}
		if srv.Runs(id) != 0 {
			t.Fatalf("runs %d", srv.Runs(id))
		}
	}

	// a stream with such metadata is created, and fails at its first receive
	id = fresh()
	ctx = metadata.AppendToOutgoingContext(ctx5(t), "big", strings.Repeat("v", headerLimit+10))
	st, err := c.Bidi(ctx)
	if err != nil {
		t.Fatalf("NewStream: %v", err)
	}
	if err := st.Send(svc.M(id + " echo x")); err != nil && err != io.EOF {
		t.Fatalf("Send: %v", err)
	}
	_, err = st.Recv()
	if !headRefused(err) {
		t.Fatalf("stream over the limit: %v", err)
	}
	if srv.Runs(id) != 0 {
		t.Fatalf("runs %d", srv.Runs(id))
	}

	// a server's header or trailer: under the limit it arrives; over it, the call fails after the
	// handler ran
	for _, cmd := range []string{"bighdr", "bigtrl"} {
		id = fresh()
		var hdr, trl metadata.MD
		r, err := c.Unary(ctx5(t), svc.M(id+" "+cmd+" "+strconv.Itoa(headerLimit-4096)), grpc.Header(&hdr), grpc.Trailer(&trl))
		if err != nil {
			t.Fatal(cmd, err)
		}
		if cmd == "bighdr" && (r.GetValue() != "<nil>" || len(hdr.Get("h")) != 1 || len(hdr.Get("h")[0]) != headerLimit-4096) {
			t.Fatalf("bighdr: reply %q", r.GetValue())
		}
		if cmd == "bigtrl" && (len(trl.Get("t")) != 1 || len(trl.Get("t")[0]) != headerLimit-4096) {
			t.Fatalf("bigtrl: trailer %d", len(trl.Get("t")))
		}
		for _, n := range []int{headerLimit + 10, 64 << 20} {
			id = fresh()
			_, err = c.Unary(ctx5(t), svc.M(id+" "+cmd+" "+strconv.Itoa(n)))
			wantStatus(t, err, codes.Unavailable, "error reading from server: connection error: COMPRESSION_ERROR")
			if srv.Runs(id) != 1 {
				t.Fatalf("%s: runs %d", cmd, srv.Runs(id))
			}
		}
	}
}

// headRefused: the error of a call whose head the server refused by closing the connection
// (Unavailable; grpc-go's reader sees the EOF, or the server's RST as a reset, or a write fails
// with a broken pipe, by timing: the model's modelChooseMessage).
func headRefused(err error) bool {
	m := status.Convert(err).Message()
	return status.Code(err) == codes.Unavailable && (m == "error reading from server: EOF" ||
		strings.HasPrefix(m, "error reading from server: ") && strings.HasSuffix(m, ": connection reset by peer") ||
		strings.HasSuffix(m, ": write: broken pipe\""))
}
