package grpcdifftest_test

import (
	"context"
	"fmt"
	"io"
	"os"
	"sort"
	"strings"
	"sync"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/stats"
	"google.golang.org/grpc/status"

	"models.lab/internal/grpcdifftest/svc"
)

// A server stats handler (etcd installs otelgrpc's): every event grpc-go's server gives a handler,
// per call in order, and per connection, with the fields that do not depend on HTTP/2's encoding
// (InHeader's WireLength, an HPACK size, is not compared: the model's is its own choice,
// modelChooseLength).
type recStats struct {
	mu    sync.Mutex
	calls map[string][]string // by the call's tag (TagRPC's FullMethodName and the request id)
	conns []string
}

type recKey struct{}

type recTag struct{ method string }

func newRecStats() *recStats { return &recStats{calls: map[string][]string{}} }

func (r *recStats) TagRPC(ctx context.Context, info *stats.RPCTagInfo) context.Context {
	return context.WithValue(ctx, recKey{}, &recTag{method: info.FullMethodName})
}

func (r *recStats) add(ctx context.Context, ev string) {
	r.mu.Lock()
	defer r.mu.Unlock()
	key := "untagged"
	if tag, _ := ctx.Value(recKey{}).(*recTag); tag != nil {
		key = tag.method
	}
	r.calls[key] = append(r.calls[key], ev)
}

func (r *recStats) HandleRPC(ctx context.Context, s stats.RPCStats) {
	if s.IsClient() {
		r.add(ctx, "client event")
		return
	}
	switch e := s.(type) {
	case *stats.InHeader:
		r.add(ctx, fmt.Sprintf("InHeader %s compression=%q k=%v", e.FullMethod, e.Compression,
			e.Header.Get("k")))
	case *stats.Begin:
		r.add(ctx, fmt.Sprintf("Begin cs=%v ss=%v", e.IsClientStream, e.IsServerStream))
	case *stats.InPayload:
		r.add(ctx, fmt.Sprintf("InPayload len=%d wire=%d", e.Length, e.WireLength))
	case *stats.OutHeader:
		r.add(ctx, fmt.Sprintf("OutHeader k=%v", e.Header.Get("k")))
	case *stats.OutPayload:
		r.add(ctx, fmt.Sprintf("OutPayload len=%d wire=%d", e.Length, e.WireLength))
	case *stats.OutTrailer:
		r.add(ctx, fmt.Sprintf("OutTrailer k=%v", e.Trailer.Get("k")))
	case *stats.End:
		r.add(ctx, fmt.Sprintf("End code=%v", status.Code(e.Error)))
	default:
		r.add(ctx, fmt.Sprintf("%T", s))
	}
}

func (r *recStats) TagConn(ctx context.Context, info *stats.ConnTagInfo) context.Context {
	return ctx
}

func (r *recStats) HandleConn(ctx context.Context, s stats.ConnStats) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.conns = append(r.conns, fmt.Sprintf("%T", s))
}

func (r *recStats) get(method string) []string {
	r.mu.Lock()
	defer r.mu.Unlock()
	return append([]string(nil), r.calls[method]...)
}

// TestStatsHandler: the events a server's stats handler gets for a unary call, a failed unary
// call, and the three kinds of stream (each on a method of its own, one call each, so a method
// names its call), in grpc-go's order; and the connection's begin and end. STATS_PRINT=1 prints
// what it got instead of comparing (to take grpc-go's sequences).
func TestStatsHandler(t *testing.T) {
	rec := newRecStats()
	srv := svc.New()
	gs, addr := serveOpts(t, srv, grpc.StatsHandler(rec))
	cc, c := dial(t, addr)
	ctx := metadata.AppendToOutgoingContext(context.Background(), "k", "v")

	// one call per method, so that the method is the call's key
	if _, err := c.Unary(ctx, svc.M("st1 md")); err != nil {
		t.Fatal(err)
	}
	ss, err := c.ServerStream(ctx, svc.M("st2 stream 2"))
	if err != nil {
		t.Fatal(err)
	}
	for {
		if _, err := ss.Recv(); err == io.EOF {
			break
		} else if err != nil {
			t.Fatal(err)
		}
	}
	cs, err := c.ClientStream(ctx)
	if err != nil {
		t.Fatal(err)
	}
	cs.Send(svc.M("st3 a"))
	cs.Send(svc.M("st3 b"))
	if _, err := cs.CloseAndRecv(); err != nil {
		t.Fatal(err)
	}
	methods := []string{"/difftest.Echo/Unary", "/difftest.Echo/ServerStream", "/difftest.Echo/ClientStream"}
	for _, m := range methods {
		eventually(t, m+"'s End", func() bool {
			ev := rec.get(m)
			return len(ev) > 0 && strings.HasPrefix(ev[len(ev)-1], "End")
		})
	}
	// a failed call, on a second server (its own method keys)
	rec2 := newRecStats()
	gs2, addr2 := serveOpts(t, svc.New(), grpc.StatsHandler(rec2))
	_, c2 := dial(t, addr2)
	if _, err := c2.Unary(ctx, svc.M("st4 err 5 gone")); status.Code(err) != 5 {
		t.Fatalf("err call: %v", err)
	}
	eventually(t, "the failed call's End", func() bool {
		ev := rec2.get("/difftest.Echo/Unary")
		return len(ev) > 0 && strings.HasPrefix(ev[len(ev)-1], "End")
	})

	got := map[string][]string{}
	for _, m := range methods {
		got[m] = rec.get(m)
	}
	got["failed /difftest.Echo/Unary"] = rec2.get("/difftest.Echo/Unary")
	got["untagged"] = rec.get("untagged")
	// grpc-go v1.84.0's sequences (STATS_PRINT=1 against the real grpc-go)
	want := map[string][]string{
		"/difftest.Echo/Unary": {
			`InHeader /difftest.Echo/Unary compression="" k=[v]`, `Begin cs=false ss=false`,
			`InPayload len=8 wire=13`, `OutHeader k=[h]`, `OutPayload len=4 wire=9`,
			`OutTrailer k=[t]`, `End code=OK`},
		"/difftest.Echo/ServerStream": {
			`InHeader /difftest.Echo/ServerStream compression="" k=[v]`, `Begin cs=false ss=true`,
			`InPayload len=14 wire=19`, `OutHeader k=[]`, `OutPayload len=3 wire=8`,
			`OutPayload len=3 wire=8`, `OutTrailer k=[]`, `End code=OK`},
		"/difftest.Echo/ClientStream": {
			`InHeader /difftest.Echo/ClientStream compression="" k=[v]`, `Begin cs=true ss=false`,
			`InPayload len=7 wire=12`, `InPayload len=7 wire=12`, `OutHeader k=[]`,
			`OutPayload len=13 wire=18`, `OutTrailer k=[]`, `End code=OK`},
		// a trailers-only response: no OutHeader
		"failed /difftest.Echo/Unary": {
			`InHeader /difftest.Echo/Unary compression="" k=[v]`, `Begin cs=false ss=false`,
			`InPayload len=16 wire=21`, `OutTrailer k=[]`, `End code=NotFound`},
		"untagged": nil,
	}
	if os.Getenv("STATS_PRINT") != "" {
		keys := make([]string, 0, len(got))
		for k := range got {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			fmt.Printf("%q: %q,\n", k, got[k])
		}
		return
	}
	for k := range got {
		if fmt.Sprintf("%q", got[k]) != fmt.Sprintf("%q", want[k]) {
			t.Errorf("%s's events:\n got %q\nwant %q", k, got[k], want[k])
		}
	}
	cc.Close()
	gs.Stop()
	gs2.Stop()
	// the connections' events: a ConnBegin and a ConnEnd per connection (grpc-go: one connection
	// carries the three calls; the model: a connection per stream, models/README.md, "The grpc
	// model": which a handler's connection events show)
	eventually(t, "the connections' ends", func() bool {
		rec.mu.Lock()
		defer rec.mu.Unlock()
		b, e := 0, 0
		for _, c := range rec.conns {
			switch c {
			case "*stats.ConnBegin":
				b++
			case "*stats.ConnEnd":
				e++
			default:
				t.Errorf("connection event %s", c)
			}
		}
		return b >= 1 && b == e
	})
}
