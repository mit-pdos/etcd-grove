---
upstream: unchecked
---

# etcdserver/api/v3rpc: `LeaseTimeToLive` panics on a forwarded reply without a response header

- **Status**: a bug (robustness): a reachable panic on a follower, on input from the network; the
  sibling of `etcd-leasehttp-timetolive-nil-response-panic.md` (there the reply lacks the
  `LeaseTimeToLiveResponse`, here the response lacks its `Header`). A peer URL that answers the
  lease TimeToLive POST with status 200 and a `LeaseInternalResponse` whose
  `LeaseTimeToLiveResponse` has the requested `ID` but no `Header` passes `TimeToLiveHTTP`'s checks
  (it compares only the `ID`); `EtcdServer.leaseTimeToLive` returns that response, and the gRPC
  handler `LeaseServer.LeaseTimeToLive` calls `ls.hdr.fill(resp.Header)`, which panics on a nil
  header (`panic("unexpected nil resp.Header")`). The handler runs on the gRPC goroutine; etcd
  installs no recovery interceptor, so the process exits. etcd's own leader handler always sets the
  header (`&pb.ResponseHeader{}`), so it takes a peer URL served by something else or a corrupted
  reply.
- **Where** (etcd at `633036387c66`, `etc/goose.py`'s pin): `server/lease/leasehttp/http.go:270-278`
  (`TimeToLiveHTTP`: unmarshal, the `ID` check, the response returned);
  `server/etcdserver/v3_server.go:681-683` (`leaseTimeToLive` returns
  `resp.LeaseTimeToLiveResponse`); `server/etcdserver/api/v3rpc/lease.go:76` (`ls.hdr.fill`);
  `server/etcdserver/api/v3rpc/header.go:54-56` (the panic).
- **What happens**: reproduced (go1.27.3), two unit tests. In package `leasehttp`, a 200 reply
  with `proto.Marshal(&leasepb.LeaseInternalResponse{LeaseTimeToLiveResponse:
  &pb.LeaseTimeToLiveResponse{ID: 1}})` is accepted, its `Header` nil:

  ```go
  resp, err := TimeToLiveHTTP(context.Background(), 1, false, ts.URL+LeaseInternalPrefix, http.DefaultTransport)
  // err == nil, resp.LeaseTimeToLiveResponse.Header == nil
  ```

  In package `v3rpc`, a `LeaseServer` whose `Lessor` returns that response
  (`&pb.LeaseTimeToLiveResponse{ID: r.ID}, nil`, what `leaseTimeToLive` returns on a follower):

  ```go
  ls := &LeaseServer{lg: zap.NewNop(), le: nilHeaderLessor{}, hdr: header{rev: func() int64 { return 1 }}}
  ls.LeaseTimeToLive(context.Background(), &pb.LeaseTimeToLiveRequest{ID: 1})
  ```

  panics with `unexpected nil resp.Header`.
- **Expected**: an error for a malformed reply, as for a non-200 status, which `leaseTimeToLive`'s
  loop treats like any other failed URL.
- **How the proof handles it**: the names-only contract `EtcdServer.leaseTimeToLive`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`) states, in its
  peers assumption, that the leader's peer URLs are served by etcd's lease handler, which always
  sets the header: its post gives `⌜w.Header' ≠ null⌝`, which the gRPC handler's proof needs for
  `fill` (the lease rows at the gRPC level, `notes/lease-grpc-plan.md`).
- **Possible fixes**: in `TimeToLiveHTTP`, after the unmarshal, `if lresp.LeaseTimeToLiveResponse
  == nil || lresp.LeaseTimeToLiveResponse.Header == nil { return nil, fmt.Errorf("lease: malformed
  TimeToLive response") }` (fixes both issues).
- **Found**: 2026-11-01, the lease rows at the gRPC level, the Draft's independent spec review;
  reproduced the same day.
