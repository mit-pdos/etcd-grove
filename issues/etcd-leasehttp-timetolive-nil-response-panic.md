---
upstream: unchecked
---

# server/lease/leasehttp: `TimeToLiveHTTP` panics on a 200 reply without a `LeaseTimeToLiveResponse`

- **Status**: a bug (robustness): a reachable nil-pointer panic on a follower, on input from the
  network. A peer URL that answers the lease TimeToLive POST with status 200 and a body that
  unmarshals to a `LeaseInternalResponse` without its `LeaseTimeToLiveResponse` (an empty body, or
  any other message) makes the follower dereference a nil pointer. The call runs on the gRPC
  handler's goroutine (`EtcdServer.LeaseTimeToLive` -> `leaseTimeToLive`); etcd installs no
  recovery interceptor, so the process exits. etcd's own leader handler always sets the field, so
  it takes a peer URL served by something else (a proxy or misconfigured endpoint, a different
  version's handler) or a corrupted reply.
- **Where**: `server/lease/leasehttp/http.go` at 249d76bea (`etc/goose.py`'s etcd pin):
  `TimeToLiveHTTP` unmarshals the reply (`http.go:270-273`), then reads
  `lresp.LeaseTimeToLiveResponse.ID` (`http.go:274`) without checking the field. Its caller,
  `EtcdServer.leaseTimeToLive` (`server/etcdserver/v3_server.go:676-689`), calls it for each of the
  leader's peer URLs.
- **What happens**: reproduced (go1.27.3), a test in package `leasehttp`:

  ```go
  func TestTimeToLiveHTTPNilResponsePanics(t *testing.T) {
  	ts := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
  		w.WriteHeader(http.StatusOK)
  	}))
  	defer ts.Close()
  	defer func() {
  		if r := recover(); r != nil {
  			t.Logf("panic: %v", r)
  			return
  		}
  		t.Fatal("no panic")
  	}()
  	TimeToLiveHTTP(context.Background(), 1, false, ts.URL+LeaseInternalPrefix, http.DefaultTransport)
  }
  ```

  logs `panic: runtime error: invalid memory address or nil pointer dereference`.
- **Expected**: an error for a malformed reply (as for a non-200 status or an unmarshal failure),
  which `leaseTimeToLive`'s loop then treats like any other failed URL.
- **How the proof handles it**: `EtcdServer.leaseTimeToLive` is names-only, a trust-boundary
  contract (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`, the
  lease-read plan): the contract's docstring states the assumption that the leader's peer URLs are
  served by etcd's lease handler (`leasehttp.NewHandler`), which always sets the field.
- **Possible fixes**: `if lresp.LeaseTimeToLiveResponse == nil { return nil, fmt.Errorf("lease:
  empty TimeToLive response") }` before `http.go:274`.
- **Found**: 2026-10-31, the lease-read plan's Draft review (the independent spec review of the
  `leaseTimeToLive` contract), reproduced the same day.
