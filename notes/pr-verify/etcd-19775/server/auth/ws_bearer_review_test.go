package auth

import (
	"context"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/gorilla/websocket"
	"github.com/grpc-ecosystem/grpc-gateway/v2/runtime"
	"github.com/tmc/grpc-websocket-proxy/wsproxy"
	"google.golang.org/grpc/metadata"
)

// The #19752 path: websocket client -> wsproxy (as server/embed/serve.go wires it) ->
// grpc-gateway's metadata annotation -> (outgoing md becomes the server's incoming md) ->
// authStore.AuthInfoFromCtx.
func TestReviewWebsocketBearer(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	ctx := context.WithValue(context.WithValue(t.Context(), AuthenticateParamIndex{}, uint64(1)), AuthenticateParamSimpleTokenPrefix{}, "dummy")
	resp, err := as.Authenticate(ctx, "foo", "bar")
	if err != nil {
		t.Fatal(err)
	}
	gw := runtime.NewServeMux()
	type res struct {
		md   metadata.MD
		user string
		err  error
	}
	got := make(chan res, 1)
	inner := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		actx, err := runtime.AnnotateContext(r.Context(), gw, r, "/etcdserverpb.Watch/Watch")
		if err != nil {
			got <- res{err: err}
			return
		}
		md, _ := metadata.FromOutgoingContext(actx)
		ai, err := as.AuthInfoFromCtx(metadata.NewIncomingContext(t.Context(), md))
		u := "<nil>"
		if ai != nil {
			u = ai.Username
		}
		got <- res{md, u, err}
	})
	srv := httptest.NewServer(wsproxy.WebsocketProxy(inner, wsproxy.WithRequestMutator(
		func(_ *http.Request, o *http.Request) *http.Request { o.Method = "POST"; return o })))
	defer srv.Close()
	url := "ws" + strings.TrimPrefix(srv.URL, "http") + "/v3/watch"
	for _, proto := range []string{"Bearer, " + resp.Token, "Bearer," + resp.Token} {
		h := http.Header{}
		h.Set("Sec-WebSocket-Protocol", proto)
		c, _, err := websocket.DefaultDialer.Dial(url, h)
		if err != nil {
			t.Fatalf("dial %q: %v", proto, err)
		}
		r := <-got
		c.Close()
		t.Logf("Sec-WebSocket-Protocol %q: authorization md %q, user %s, err %v", proto, r.md.Get("authorization"), r.user, r.err)
		if r.err != nil || r.user != "foo" {
			t.Errorf("not authenticated")
		}
	}
}
