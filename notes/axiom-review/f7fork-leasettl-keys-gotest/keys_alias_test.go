// Delta review of EtcdServer.leaseTimeToLive's keys conjunct (2026-11-26,
// notes/axiom-review/f7fork-leasettl-keys-contract.md). Run from the fork's
// server/ module (etcd fork d26dd5da6f): copy this file to
// server/lease/leasehttp/ and `go test -run TestF7forkKeys -v ./lease/leasehttp/`.
package leasehttp

import (
	"bytes"
	"io"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"
	"unsafe"

	"go.uber.org/zap/zaptest"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/runtime/protoiface"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasepb"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// within reports whether k's backing array [ptr, ptr+cap) overlaps b's.
func within(k, b []byte) bool {
	if cap(k) == 0 || cap(b) == 0 {
		return false
	}
	kp := uintptr(unsafe.Pointer(unsafe.SliceData(k)))
	bp := uintptr(unsafe.Pointer(unsafe.SliceData(b)))
	return kp < bp+uintptr(cap(b)) && bp < kp+uintptr(cap(k))
}

func marshalReply(t *testing.T, keys [][]byte) []byte {
	b, err := proto.Marshal(&leasepb.LeaseInternalResponse{
		LeaseTimeToLiveResponse: &pb.LeaseTimeToLiveResponse{
			Header: &pb.ResponseHeader{}, ID: 7, TTL: 5, GrantedTTL: 10, Keys: keys,
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	return b
}

// 1. proto.Unmarshal (TimeToLiveHTTP's decode) and, a fortiori, the
// AliasBuffer-permitting internal path: no decoded key overlaps the buffer;
// empty keys have capacity 0.
func TestF7forkKeysUnmarshalNoAlias(t *testing.T) {
	keys := [][]byte{[]byte("z/lease"), {}, []byte("a/other-key"), {}}
	for _, alias := range []bool{false, true} {
		b := marshalReply(t, keys)
		lresp := &leasepb.LeaseInternalResponse{}
		if alias {
			var fl protoiface.UnmarshalInputFlags = protoiface.UnmarshalAliasBuffer
			m := lresp.ProtoReflect()
			if _, err := m.ProtoMethods().Unmarshal(protoiface.UnmarshalInput{Message: m, Buf: b, Flags: fl, Depth: 10000}); err != nil {
				t.Fatal(err)
			}
		} else if err := proto.Unmarshal(b, lresp); err != nil {
			t.Fatal(err)
		}
		got := lresp.LeaseTimeToLiveResponse.Keys
		if len(got) != len(keys) {
			t.Fatalf("got %d keys", len(got))
		}
		for i, k := range got {
			if within(k, b) {
				t.Fatalf("alias=%v: key %d overlaps the body buffer", alias, i)
			}
			if len(k) == 0 && cap(k) != 0 {
				t.Fatalf("alias=%v: empty key %d has cap %d", alias, i, cap(k))
			}
			t.Logf("alias=%v key %d: len %d cap %d nil=%v", alias, i, len(k), cap(k), k == nil)
		}
		for i := range b {
			b[i] = 0xff
		}
		for i, k := range got {
			if !bytes.Equal(k, keys[i]) {
				t.Fatalf("alias=%v: key %d changed with the buffer: %q", alias, i, k)
			}
		}
	}
}

// bodyRT returns a fixed body over a buffer the test keeps, as a transport
// that retains (and later reuses) its read buffer would.
type bodyRT struct{ buf []byte }

func (rt *bodyRT) RoundTrip(*http.Request) (*http.Response, error) {
	return &http.Response{StatusCode: 200, Header: http.Header{},
		Body: io.NopCloser(bytes.NewReader(rt.buf))}, nil
}

// 2. End to end through TimeToLiveHTTP, with a transport that keeps the body:
// overwriting it after the call changes no key; writing the keys writes nothing
// of it.
func TestF7forkKeysTimeToLiveHTTPRetainedBody(t *testing.T) {
	keys := [][]byte{[]byte("k1"), []byte("key-two"), {}}
	rt := &bodyRT{buf: marshalReply(t, keys)}
	orig := append([]byte(nil), rt.buf...)
	resp, err := TimeToLiveHTTP(t.Context(), 7, true, "http://leader"+LeaseInternalPrefix, rt)
	if err != nil {
		t.Fatal(err)
	}
	got := resp.LeaseTimeToLiveResponse.Keys
	for i, k := range got {
		if within(k, rt.buf) {
			t.Fatalf("key %d overlaps the transport's buffer", i)
		}
	}
	for i := range rt.buf {
		rt.buf[i] = 0
	}
	for i, k := range got {
		if !bytes.Equal(k, keys[i]) {
			t.Fatalf("key %d changed: %q", i, k)
		}
	}
	copy(rt.buf, orig)
	for _, k := range got {
		for j := range k {
			k[j] = 0xee
		}
	}
	if !bytes.Equal(rt.buf, orig) {
		t.Fatal("writing a key wrote the transport's buffer")
	}
}

// 3. Against the real leader handler (NewHandler over a real lessor): two
// forwarded replies for the same lease share no key memory with each other
// (each decode is fresh), and keys=false yields nil Keys.
func TestF7forkKeysRealHandler(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	le := lease.NewLessor(lg, be, nil, lease.LessorConfig{MinLeaseTTL: 5})
	le.Promote(time.Second)
	l, err := le.Grant(1, 5)
	if err != nil {
		t.Fatal(err)
	}
	if err := le.Attach(l.ID, []lease.LeaseItem{{Key: "foo"}, {Key: ""}, {Key: "bar"}}); err != nil {
		t.Fatal(err)
	}
	ts := httptest.NewServer(NewHandler(le, waitReady))
	defer ts.Close()
	r1, err := TimeToLiveHTTP(t.Context(), l.ID, true, ts.URL+LeaseInternalPrefix, http.DefaultTransport)
	if err != nil {
		t.Fatal(err)
	}
	r2, err := TimeToLiveHTTP(t.Context(), l.ID, true, ts.URL+LeaseInternalPrefix, http.DefaultTransport)
	if err != nil {
		t.Fatal(err)
	}
	k1, k2 := r1.LeaseTimeToLiveResponse.Keys, r2.LeaseTimeToLiveResponse.Keys
	if len(k1) != 3 || len(k2) != 3 {
		t.Fatalf("keys %q %q", k1, k2)
	}
	for _, a := range k1 {
		for _, b := range k2 {
			if within(a, b) {
				t.Fatal("two replies share key memory")
			}
		}
		for j := range a {
			a[j] = 'X'
		}
	}
	r3, _ := TimeToLiveHTTP(t.Context(), l.ID, true, ts.URL+LeaseInternalPrefix, http.DefaultTransport)
	for _, k := range r3.LeaseTimeToLiveResponse.Keys {
		if bytes.Contains(k, []byte("X")) {
			t.Fatal("writing a returned key reached the lessor")
		}
	}
	t.Logf("keys=true: %q", r3.LeaseTimeToLiveResponse.Keys)
	r4, err := TimeToLiveHTTP(t.Context(), l.ID, false, ts.URL+LeaseInternalPrefix, http.DefaultTransport)
	if err != nil {
		t.Fatal(err)
	}
	if r4.LeaseTimeToLiveResponse.Keys != nil {
		t.Fatalf("keys=false: Keys = %q, want nil", r4.LeaseTimeToLiveResponse.Keys)
	}
	t.Log("keys=false: Keys == nil")
}
